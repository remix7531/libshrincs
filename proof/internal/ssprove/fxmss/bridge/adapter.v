(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.fxmss.bridge.adapter

    Route the public FXMSS operations to G_forge_keyed. Invalid natural coordinates
    must still spend a HASH slot and obey the internal terminal flag. They
    are routed to an overlong payload, which the internal oracle refuses
    before touching its ROM table. The adapter remembers the committed
    partner and prefixes it to SIGN and FORGE messages. *)

From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs Require Import spec games schemes.
From Shrincs.internal.ssprove.fxmss Require Import params games instance bridge.model.
From mathcomp Require Import word_ssrZ word.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.

Import Shrincs.internal.ssprove.fxmss.games.

Import PackageNotation.
#[local] Close Scope Z_scope.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Definition shrincs_fxmss_rom_refused_payload : shrincs_fxmss_bytes :=
  nseq (Z.to_nat (Z.pow 2 61)) (uint U8 0).

Lemma shrincs_fxmss_rom_refused_payload_invalid :
  Z.leb (Z.of_nat (size shrincs_fxmss_rom_refused_payload))
    (Z.sub (Z.pow 2 61) 111) = false.
Proof.
rewrite /shrincs_fxmss_rom_refused_payload size_nseq Znat.Z2Nat.id; lia.
Qed.

Definition shrincs_fxmss_rom_route_query (x : fxmss_sf_hash_input) :
  shrincs_fxmss_hmsg_input :=
  if fxmss_sf_hash_valid x then shrincs_fxmss_rom_internal_query x
  else (x.1, (x.2.1, ((uint U8 0, uint U64 0), shrincs_fxmss_rom_refused_payload))).

Lemma shrincs_fxmss_rom_route_query_valid x :
  fxmss_sf_hash_valid x ->
  shrincs_fxmss_rom_route_query x = shrincs_fxmss_rom_internal_query x.
Proof. by rewrite /shrincs_fxmss_rom_route_query => ->. Qed.

Lemma shrincs_fxmss_rom_route_query_domain x :
  Z.leb (Z.of_nat (size (shrincs_fxmss_rom_route_query x).2.2.2))
    (Z.sub (Z.pow 2 61) 111) = fxmss_sf_hash_valid x.
Proof.
rewrite /shrincs_fxmss_rom_route_query.
case hx: (fxmss_sf_hash_valid x).
- move: hx.
  rewrite /fxmss_sf_hash_valid.
  by move/andP=> [_ ->].
- exact: shrincs_fxmss_rom_refused_payload_invalid.
Qed.

Definition shrincs_fxmss_rom_partner_loc := mkloc 2100 (zeros 16).
Definition shrincs_fxmss_rom_adapter_locs : Locations := [fmap
  shrincs_fxmss_rom_partner_loc].

Definition shrincs_fxmss_rom_adapter :
    package I_forge (stateful_rom.I_EUCMA fxmss_sf_scheme) :=
  [package shrincs_fxmss_rom_adapter_locs;
    [ stateful_rom.GEN ] : { fxmss_sf_setup ~> bytes 48 } (sp) {
      pk ← opr (mkopsig shrincs_fxmss_op_gen shrincs_fxmss_setup (bytes 48)) sp (fun pk
        => ret pk) ;;
      #put shrincs_fxmss_rom_partner_loc := sp.2 ;; ret pk
    };
    [ stateful_rom.SIGN ] : { fxmss_sf_message ~> 'option shrincs_fxmss_bytes } (cm) {
      partner ← get shrincs_fxmss_rom_partner_loc ;;
      opr (mkopsig shrincs_fxmss_op_sign shrincs_fxmss_message ('option
        shrincs_fxmss_bytes))
        (shrincs_fxmss_rom_embed_message partner cm) (fun sg => ret sg)
    };
    [ stateful_rom.HASH ] : { fxmss_sf_hash_input ~> 'option (bytes 32) } (x) {
      opr (mkopsig shrincs_fxmss_op_hash shrincs_fxmss_hmsg_input ('option (bytes 32)))
        (shrincs_fxmss_rom_route_query x) (fun md => ret md)
    };
    [ stateful_rom.FORGE ] : { fxmss_sf_message × shrincs_fxmss_bytes ~> 'bool } (c) {
      partner ← get shrincs_fxmss_rom_partner_loc ;;
      opr shrincs_fxmss_forge_op (shrincs_fxmss_rom_embed_message partner c.1, c.2) (fun
        b => ret b)
    }
  ].

Lemma shrincs_fxmss_rom_adapter_valid :
  ValidPackage (loc shrincs_fxmss_rom_adapter) I_forge
    (stateful_rom.I_EUCMA fxmss_sf_scheme) shrincs_fxmss_rom_adapter.
Proof. exact: pack_valid. Qed.
