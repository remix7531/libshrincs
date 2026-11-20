# Turn test/spec/vectors/wots_c.kat into one Rocq file per case.
#
#   awk -v out=DIRECTORY -f kat_to_v.awk wots_c.kat
#
# Each file states that the function of Shrincs.spec named by the case returns
# the recorded result on the recorded arguments. A case this script does not
# know how to state is an error, never a skipped check.

function fail(message) {
  print "kat_to_v.awk: " FILENAME ":" FNR ": " message > "/dev/stderr"
  failed = 1
  exit 1
}

function need(name) {
  if (!(name in field)) fail("case " cases " (" field["function"] ") has no field " name)
  return field[name]
}

# "0a1b" becomes "[:: 10; 27]", and "empty" becomes "[::]".
function bytes(hex,    list, position) {
  if (hex == "empty") return "[::]"
  if (hex !~ /^([0-9a-f][0-9a-f])+$/) fail("not a hex byte string: " hex)
  list = ""
  for (position = 1; position < length(hex); position += 2)
    list = list (position > 1 ? "; " : "") strtonum("0x" substr(hex, position, 2))
  return "[:: " list "]"
}

function fixed(name, size) { return "(fixed " size " " bytes(need(name)) ")" }

function fixed_checked(name, size,    value) {
  value = need(name)
  if ((value == "empty" ? 0 : length(value) / 2) != size)
    fail("field " name " must contain " size " bytes")
  return fixed(name, size)
}

function state() {
  return need("state") == "none" ? "None" : "(Some " word("U64", "state") ")"
}

function znumber(value) {
  if (value !~ /^[0-9]+$/) fail("not an integer: " value)
  return value == "0" ? "Z0" : "(Zpos " value "%positive)"
}

function optional_sequence(call,    output) {
  output = need("output")
  return "omap bytes_of (" call ") == " (output == "none" ? "None" : "Some " bytes(output))
}

# "1 2 3" becomes "[:: 1; 2; 3]".
function numbers(text,    list) {
  if (text !~ /^[0-9]+( [0-9]+)*$/) fail("not a list of integers: " text)
  list = text
  gsub(/ /, "; ", list)
  return "[:: " list "]"
}

# A decimal integer as a word. No scope is involved: the literal is a positive.
function word(size, name,    value) {
  value = need(name)
  if (value !~ /^[0-9]+$/) fail("not an integer: " value)
  return "(wrepr " size " " (value == "0" ? "Z0" : "(Zpos " value "%positive)") ")"
}

function natural(name,    value) {
  value = need(name)
  if (value !~ /^[0-9]+$/) fail("not an integer: " value)
  return value
}

function boolean(name,    value) {
  value = need(name)
  if (value == "1") return "true"
  if (value == "0") return "false"
  fail("not a boolean: " value)
}

function anchor() { return word("U8", "node_height") " " word("U64", "node_index") }
function shape() { return boolean("tree_balanced") " " word("U8", "tree_depth") }

# The result as an option of bytes: the comparison's two sides.
function optional_bytes(call,    output) {
  output = need("output")
  if (output == "none") return "optional_bytes_of (" call ") == None"
  return "optional_bytes_of (" call ") == Some " bytes(output)
}

function statement(    f, output, parts) {
  f = need("function")
  output = need("output")
  if (f == "base_2b")
    return "base_2b (free " bytes(need("x")) ") " natural("b") " " natural("outlen") " == " numbers(output)
  if (f == "F")
    return "bytes_of (F " fixed("pk_seed", 16) " (WotsCHash " word("U8", "height") " " word("U64", "index") " " word("U32", "chain_index") " " word("U32", "hash_index") ") " fixed("M_1", 16) ") == " bytes(output)
  if (f == "PRF")
    return "bytes_of (PRF " fixed("pk_seed", 16) " " fixed("sk_seed", 16) " (WotsCPrf " word("U8", "height") " " word("U64", "index") " " boolean("tree_balanced") " " word("U8", "tree_depth") " " word("U32", "chain_index") ")) == " bytes(output)
  if (f == "T_sf")
    return "bytes_of (T_sf " fixed("pk_seed", 16) " (WotsCPk " word("U8", "height") " " word("U64", "index") ") " fixed("M_l", "WOTS_C_CHAINS_SIZE") ") == " bytes(output)
  if (f == "H_grind")
    return "bytes_of (H_grind " fixed("pk_seed", 16) " (WotsCGrind " word("U8", "height") " " word("U64", "index") ") " fixed("digest", 32) " " word("U16", "counter") ") == " bytes(output)
  if (f == "wots_c_chain_iter")
    return "bytes_of (wots_c_chain_iter " fixed("node", 16) " " natural("start") " " natural("stop") " " fixed("pk_seed", 16) " " anchor() " " word("U32", "chain_index") ") == " bytes(output)
  if (f == "wots_c_grind_to_constant_sum") {
    if (split(output, parts, " : ") != 2) fail("not a grinding result: " output)
    return "omap grinded_of (wots_c_grind_to_constant_sum " fixed("pk_seed", 16) " " fixed("message_digest", 32) " " anchor() ") == Some (" parts[1] ", " numbers(parts[2]) ")"
  }
  if (f == "wots_c_map_digest")
    return "wots_c_map_digest " fixed("pk_seed", 16) " " fixed("message_digest", 32) " " anchor() " " word("U16", "counter") " == " (output == "none" ? "None" : "Some " numbers(output))
  if (f == "wots_c_pubkey_gen")
    return "bytes_of (wots_c_pubkey_gen " fixed("sk_seed", 16) " " fixed("pk_seed", 16) " " anchor() " " shape() ") == " bytes(output)
  if (f == "wots_c_sign")
    return optional_bytes("wots_c_sign " fixed("message_digest", 32) " " fixed("sk_seed", 16) " " fixed("pk_seed", 16) " " anchor() " " shape())
  if (f == "wots_c_pubkey_from_sig")
    return optional_bytes("wots_c_pubkey_from_sig " fixed("signature", "(2 + WOTS_C_CHAINS_SIZE)") " " fixed("message_digest", 32) " " fixed("pk_seed", 16) " " anchor())
  if (f == "shrincs_sf_verify")
    return "shrincs_sf_verify (free " bytes(need("message")) ") (free " bytes(need("signature")) ") (free " bytes(need("ctx")) ") " fixed_checked("pubkey", 48) " == " boolean("output")
  if (f == "shrincs_sf_sign")
    return optional_sequence("shrincs_sf_sign (free " bytes(need("message")) ") (free " bytes(need("ctx")) ") " fixed_checked("seckey", 82) " " state())
  if (f == "shrincs_extract_pubkey")
    return "bytes_of (shrincs_extract_pubkey " fixed_checked("seckey", 82) ") == " bytes(output)
  if (f == "shrincs_sf_leaf_select") {
    if (output != "none" && split(output, parts, " : ") != 2) fail("not a selected leaf: " output)
    return "omap (fun p => (wunsigned p.1, Z.to_nat (wunsigned p.2))) (shrincs_sf_leaf_select " fixed_checked("structure", 2) " " state() ") == " (output == "none" ? "None" : "Some (" znumber(parts[1]) ", " parts[2] ")")
  }
  if (f == "shrincs_sf_consume") {
    if (split(output, parts, " : ") != 3 || parts[1] != "none") fail("not a final consumption result: " output)
    return "shrincs_sf_consume " fixed_checked("structure", 2) " " state() " == (None, Some (wrepr U64 " znumber(parts[2]) ", wrepr U8 " znumber(parts[3]) "))"
  }
  fail("unknown function " f)
}

function emit(    file, name) {
  if (!("function" in field)) return
  cases++
  name = sprintf("case_%03d", cases)
  file = out "/" name ".v"
  print "(* Generated from " FILENAME " by test/spec/kat_to_v.awk: " field["function"] ". *)" > file
  print "From Stdlib Require Import BinInt." > file
  if (field["function"] ~ /^shrincs_/)
    print "From mathcomp Require Import boot algebra word_ssrZ." > file
  else
    print "From mathcomp Require Import boot." > file
  print "From SSProve.Crypt Require Import jasmin_word jasmin_wsize." > file
  print "From Shrincs Require Import spec." > file
  if (field["function"] == "shrincs_sf_consume")
    print "From Shrincs Require Import schemes." > file
  print "From SpecTest Require Import harness." > file
  print "" > file
  print "Example " name " :" > file
  print "  (" statement() ") = true." > file
  print "Proof. run. Qed." > file
  close(file)
  delete field
}

BEGIN { if (out == "") { print "kat_to_v.awk: pass -v out=DIRECTORY" > "/dev/stderr"; failed = 1; exit 1 } }

/^#/ { next }
/^[[:space:]]*$/ { emit(); next }
{
  separator = index($0, " = ")
  if (!separator) fail("not a 'name = value' line: " $0)
  key = substr($0, 1, separator - 1)
  if (key in field) fail("field " key " given twice")
  field[key] = substr($0, separator + 3)
}

END {
  if (failed) exit 1
  emit()
  if (!cases) { print "kat_to_v.awk: no case found" > "/dev/stderr"; exit 1 }
  print cases
}
