# Rocq commands end at a dot followed by whitespace, a comment, or EOF.
# Comments nest. Quotes inside strings are escaped by doubling them.
function reject(message) {
  print FILENAME ":" command_line ": " message
  failed = 1
}

function imports_internal_module(text,    prefix, modules, module_count, module_index) {
  prefix = ""
  if (text ~ /^From [^ ]+ Require /) {
    split(text, modules, " ")
    prefix = modules[2] "."
    sub(/^From [^ ]+ Require /, "", text)
  } else if (text ~ /^(Require|Import|Export) /) {
    sub(/^[A-Za-z]+ /, "", text)
  } else return 0
  sub(/^(Import|Export) /, "", text)
  module_count = split(text, modules, " ")
  for (module_index = 1; module_index <= module_count; module_index++) {
    if (prefix modules[module_index] ~ /^Shrincs[.]internal([.]|$)/) return 1
  }
  return 0
}

function declaration(    text, depth, attribute_index, character) {
  text = command
  gsub(/[[:space:]]+/, " ", text)
  sub(/^ /, "", text)
  sub(/ $/, "", text)
  while (text ~ /^(#\[|Local |Global |Polymorphic |Monomorphic |Time |Timeout [0-9]+ |Redirect STRING )/) {
    if (text ~ /^#\[/) {
      depth = 1
      for (attribute_index = 3; attribute_index <= length(text) && depth; attribute_index++) {
        character = substr(text, attribute_index, 1)
        if (character == "[") depth++
        if (character == "]") depth--
      }
      if (depth) { reject("unclosed declaration attribute"); return }
      text = substr(text, attribute_index)
      sub(/^ */, "", text)
    } else if (text ~ /^Timeout /) sub(/^Timeout [0-9]+ +/, "", text)
    else if (text ~ /^Redirect /) sub(/^Redirect STRING +/, "", text)
    else sub(/^[A-Za-z]+ +/, "", text)
  }

  if (forbid_internal && imports_internal_module(text))
    reject("internal import in public definition: " text)
  if (text !~ /^(Axioms?|Conjectures?|Parameters?|Hypothesis|Hypotheses) /) return
  reject("assumption declared: " text)
}

FNR == 1 {
  command = ""
  command_line = 1
  comment_depth = 0
  comment_string = 0
  in_string = 0
}

{
  source = $0 "\n"
  for (position = 1; position <= length(source); position++) {
    character = substr(source, position, 1)
    pair = substr(source, position, 2)
    if (comment_depth) {
      if (comment_string) {
        if (pair == "\"\"") position++
        else if (character == "\"") comment_string = 0
      }
      else if (character == "\"") comment_string = 1
      else if (pair == "(*") { comment_depth++; position++ }
      else if (pair == "*)") { comment_depth--; position++ }
      continue
    }
    if (in_string) {
      if (pair == "\"\"") position++
      else if (character == "\"") in_string = 0
      continue
    }
    if (pair == "(*") { comment_depth++; command = command " "; position++; continue }
    if (character == "\"") { in_string = 1; command = command " STRING "; continue }
    if (command !~ /[^[:space:]]/ && character !~ /[[:space:]]/) command_line = FNR
    if (character == "." &&
        (substr(source, position + 1, 1) ~ /[[:space:]]/ ||
         substr(source, position + 1, 2) == "(*")) {
      declaration()
      command = ""
    } else command = command character
  }
}

ENDFILE {
  if (comment_string) reject("unclosed string in comment")
  if (comment_depth) reject("unclosed comment")
  if (in_string) reject("unclosed string")
  if (command ~ /[^[:space:]]/) reject("unfinished Rocq command")
}

END { exit failed ? 1 : 0 }
