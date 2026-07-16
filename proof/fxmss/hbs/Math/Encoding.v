(** * HBS.Math.Encoding

    Base-w message encodings for Winternitz-type one-time signatures:
    digit decomposition, the WOTS+/WOTS-TW checksum, and the
    target-sum combinatorics behind WOTS+C grinding.

    Counterparts:
    - [resources/FV-SPHINCSPLUS-EC/proofs/WOTS_TW_ES.ec]: what that
      development takes as the axiom [two_encodings] (any two distinct
      encoded messages have a coordinate where the first digit vector
      is strictly below the second) is *proved* here, both for the
      checksum encoding ([checksum_exists_lt], wotstw.tex) and for the
      fixed-digit-sum encoding of WOTS+C ([eq_sumn_exists_lt],
      wotsc.tex, "the fixed digit sum playing the role of the WOTS+
      checksum").
    - [resources/SHRINCS-security-specification/wotstw.tex]: checksum
      [C = \sum_i (w - 1 - a_i)], appended to the message digits in
      base-w representation.
    - [resources/SHRINCS-security-specification/wotsc.tex]: grinding
      forces the digit sum to the target [S_wn]; two distinct digit
      vectors with equal sums must each be strictly smaller than the
      other somewhere.

    Why "strictly smaller somewhere" is the security-relevant fact:
    from the chain value at depth [d] a verifier (or forger) can
    compute the values at every depth [d' >= d], so a forged digit
    vector is only useful at coordinates where the forged digit is
    *strictly smaller* than the honest one — there the forger must
    invert the chain.  The lemmas below are the pure combinatorial
    halves of that argument; the encodings are consumed with
    [u := forged] and [v := honest] digit vectors.

    Conventions:
    - digit vectors are [seq nat]; well-formedness is
      [wf_digits w ds = all (fun d => d < w) ds];
    - [digits_w w l m] is the length-[l] base-[w] decomposition of
      [m], least significant digit first (LSB first), truncating [m]
      modulo [w ^ l]; the [w = 2] case is [bits_lsb] in
      HBS.Math.BinTree, deliberately not reused here;
    - digit sums are plain [sumn]; no [dsum] wrapper is introduced;
    - "exists k < size u" is rendered as [exists2 k, k < size u & _].

    Pure MathComp; no SSProve imports (see docs/STYLE.md rule 5). *)

Set Warnings "-notation-overridden,-ambiguous-paths".
From mathcomp Require Import all_ssreflect.
Set Warnings "notation-overridden,ambiguous-paths".

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ------------------------------------------------------------------ *)
(** ** Pointwise digit-sum lemmas

    Pure [sumn]-vs-[nth] facts on equal-length [seq nat]; no base-w
    structure involved.  These culminate in [eq_sumn_exists_lt], the
    WOTS+C target-sum lemma. *)

(** Pointwise dominated vectors have dominated sums. *)
Lemma leq_sumn_nth (u v : seq nat) :
  size u = size v ->
  (forall k, k < size u -> nth 0 u k <= nth 0 v k) ->
  sumn u <= sumn v.
Proof.
elim: u v => [|a u IH] [|b v] //= [sz] hle.
apply: leq_add; first exact: (hle 0).
by apply: IH => // k hk; exact: (hle k.+1 hk).
Qed.

(** Strict version: pointwise domination plus a difference somewhere
    gives a strictly smaller sum. *)
Lemma ltn_sumn_nth (u v : seq nat) :
  size u = size v ->
  (forall k, k < size u -> nth 0 u k <= nth 0 v k) ->
  u <> v -> sumn u < sumn v.
Proof.
elim: u v => [|a u IH] [|b v] //= [sz] hle hne.
have hab : a <= b := hle 0 isT.
case: (eqVneq u v) => [huv | /eqP huv].
- rewrite huv ltn_add2r ltn_neqAle hab andbT.
  by apply/eqP => e; apply: hne; rewrite e huv.
- have hlt : sumn u < sumn v.
    by apply: IH => // k hk; exact: (hle k.+1 hk).
  apply: (@leq_ltn_trans (b + sumn u)); first by rewrite leq_add2r.
  by rewrite ltn_add2l.
Qed.

(** A strictly smaller sum forces a strictly smaller coordinate. *)
Lemma ltn_sumn_exists_lt (u v : seq nat) :
  size u = size v -> sumn u < sumn v ->
  exists2 k, k < size u & nth 0 u k < nth 0 v k.
Proof.
elim: u v => [|a u IH] [|b v] //= [sz] hlt.
case: (ltnP a b) => hab; first by exists 0.
have hlt' : sumn u < sumn v.
  rewrite -(ltn_add2l b); apply: leq_ltn_trans hlt.
  by rewrite leq_add2r.
have [k hk hd] := IH v sz hlt'.
by exists k.+1.
Qed.

(** THE WOTS+C TARGET-SUM LEMMA (wotsc.tex, one-time security
    paragraph): if two digit vectors have the same size and the same
    digit sum (both grinded to the target [S_wn]) but differ, then
    [u] is strictly below [v] at some coordinate.  Consumed with
    [u := forged] and [v := honest] digit vector; the symmetric
    coordinate (with [v] strictly below [u]) follows by applying the
    lemma with the arguments swapped. *)
Lemma eq_sumn_exists_lt (u v : seq nat) :
  size u = size v -> sumn u = sumn v -> u <> v ->
  exists2 k, k < size u & nth 0 u k < nth 0 v k.
Proof.
elim: u v => [|a u IH] [|b v] //= [sz] hsum hne.
case: (ltngtP a b) => hab.
- by exists 0.
- have hlt : sumn u < sumn v by rewrite -(ltn_add2l b) -hsum ltn_add2r.
  have [k hk hd] := ltn_sumn_exists_lt sz hlt.
  by exists k.+1.
- have hsum' : sumn u = sumn v by move: hsum; rewrite hab => /addnI.
  have hne' : u <> v by move=> e; apply: hne; rewrite hab e.
  have [k hk hd] := IH v sz hsum' hne'.
  by exists k.+1.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Base-w digit decomposition

    [digits_w l m] = the [l] least-significant base-[w] digits of [m],
    LSB first; [num_of_digits] is the recomposition.  Mirrors
    [bits_lsb] / [idx_of_lsb] of HBS.Math.BinTree, generalized from
    [w = 2] to arbitrary [w].  Lemmas needing positivity take [0 < w]
    explicitly (or derive it from well-formedness of a digit). *)

Section BaseW.

Variable w : nat.

Fixpoint digits_w (l m : nat) : seq nat :=
  if l is l'.+1 then m %% w :: digits_w l' (m %/ w) else [::].

Fixpoint num_of_digits (ds : seq nat) : nat :=
  if ds is d :: ds' then d + num_of_digits ds' * w else 0.

(** Well-formed digit vectors: every digit below the radix. *)
Definition wf_digits (ds : seq nat) : bool := all (fun d => d < w) ds.

Lemma size_digits_w l m : size (digits_w l m) = l.
Proof. by elim: l m => [//|l IH] m /=; rewrite IH. Qed.

Lemma wf_digits_w l m : 0 < w -> wf_digits (digits_w l m).
Proof.
move=> w_gt0; rewrite /wf_digits; elim: l m => [//|l IH] m /=.
by rewrite ltn_pmod // IH.
Qed.

(** Recomposing the digits recovers [m] modulo [w ^ l]. *)
Lemma num_of_digits_w l m :
  0 < w -> num_of_digits (digits_w l m) = m %% w ^ l.
Proof.
move=> w_gt0; elim: l m => [|l IH] m /=; first by rewrite expn0 modn1.
rewrite IH expnSr [in X in _ = X](divn_eq m w) -modnDml -muln_modl.
have hlt : (m %/ w) %% w ^ l * w + m %% w < w ^ l * w.
  apply: leq_trans (_ : ((m %/ w) %% w ^ l).+1 * w <= w ^ l * w).
  - by rewrite mulSn addnC ltn_add2r ltn_pmod.
  - rewrite leq_mul2r ltn_pmod ?orbT //.
    by rewrite expn_gt0 w_gt0.
by rewrite (modn_small hlt) addnC.
Qed.

(** Cancellation on the small domain. *)
Lemma digits_wK l m :
  0 < w -> m < w ^ l -> num_of_digits (digits_w l m) = m.
Proof. by move=> w_gt0 hm; rewrite num_of_digits_w // modn_small. Qed.

(** Cancellation the other way, on well-formed digit vectors. *)
Lemma num_of_digitsK (ds : seq nat) :
  wf_digits ds -> digits_w (size ds) (num_of_digits ds) = ds.
Proof.
rewrite /wf_digits; elim: ds => [//|d ds IH] /= /andP[hd hds].
have w_gt0 : 0 < w := leq_ltn_trans (leq0n d) hd.
by rewrite addnC modnMDl divnMDl // (modn_small hd) (divn_small hd) addn0 (IH hds).
Qed.

Lemma num_of_digits_lt (ds : seq nat) :
  wf_digits ds -> num_of_digits ds < w ^ size ds.
Proof.
rewrite /wf_digits; elim: ds => [//|d ds IH] /= /andP[hd hds].
rewrite expnSr; apply: (@leq_trans ((num_of_digits ds).+1 * w)).
- by rewrite mulSn ltn_add2r.
- by rewrite leq_mul2r (IH hds) orbT.
Qed.

(** [digits_w l] is injective below [w ^ l]. *)
Lemma digits_w_inj l :
  0 < w -> {in [pred m | m < w ^ l] &, injective (digits_w l)}.
Proof.
move=> w_gt0 m m'; rewrite !inE => hm hm' /(congr1 num_of_digits).
by rewrite !num_of_digits_w // !modn_small.
Qed.

(** The most-significant-differing-digit lemma: if [a < b] (and [b]
    fits in [l] digits) then some digit of [a] is strictly below the
    corresponding digit of [b].  (At the most significant position
    where the digits differ, [a]'s digit must be smaller.)  This is
    the arithmetic core of the checksum argument. *)
Lemma digits_w_exists_lt l a b :
  0 < w -> a < b -> b < w ^ l ->
  exists2 k, k < l & nth 0 (digits_w l a) k < nth 0 (digits_w l b) k.
Proof.
move=> w_gt0; elim: l a b => [|l IH] a b hab hb.
  by move: hb hab; rewrite expn0 ltnS leqn0 => /eqP ->.
case: (ltngtP (a %/ w) (b %/ w)) => hq.
- (* quotients differ: recurse on the higher digits *)
  have hb' : b %/ w < w ^ l by rewrite ltn_divLR // -expnSr.
  have [k hk hd] := IH _ _ hq hb'.
  by exists k.+1.
- (* a %/ w > b %/ w contradicts a < b *)
  by move: (leq_div2r w (ltnW hab)); rewrite leqNgt hq.
- (* equal quotients: the least significant digits compare like a, b *)
  exists 0 => //.
  by move: hab; rewrite /= {1}(divn_eq a w) {1}(divn_eq b w) hq ltn_add2l.
Qed.

(* ------------------------------------------------------------------ *)
(** ** WOTS+ / WOTS-TW checksum (wotstw.tex)

    [checksum ds = \sum_i (w - 1 - ds_i)]; the encoded message is the
    message digits followed by the checksum rendered as [len2] base-w
    digits (LSB first; the lemma below is insensitive to the digit
    order of the checksum block, as long as it is fixed).  The
    parameter side condition [size ds * (w-1) < w ^ len2] says the
    checksum always fits in [len2] digits. *)

Definition checksum (ds : seq nat) : nat := sumn [seq w.-1 - d | d <- ds].

Definition encode_chk (len2 : nat) (ds : seq nat) : seq nat :=
  ds ++ digits_w len2 (checksum ds).

Lemma size_encode_chk len2 ds : size (encode_chk len2 ds) = size ds + len2.
Proof. by rewrite /encode_chk size_cat size_digits_w. Qed.

Lemma wf_encode_chk len2 ds :
  0 < w -> wf_digits ds -> wf_digits (encode_chk len2 ds).
Proof.
move=> w_gt0 h; rewrite /encode_chk /wf_digits all_cat.
by apply/andP; split; [exact: h | exact: wf_digits_w].
Qed.

(** On well-formed vectors, checksum and digit sum are complementary:
    their sum is the constant [size ds * (w - 1)].  Hence a larger
    digit sum means a *smaller* checksum. *)
Lemma checksum_sumn (ds : seq nat) :
  wf_digits ds -> checksum ds + sumn ds = size ds * w.-1.
Proof.
rewrite /wf_digits /checksum; elim: ds => [//|d ds IH] /= /andP[hd hds].
have w_gt0 : 0 < w := leq_ltn_trans (leq0n d) hd.
have hd' : d <= w.-1 by rewrite -ltnS prednK.
by rewrite mulSn addnACA subnK // (IH hds).
Qed.

Lemma checksum_leq (ds : seq nat) :
  wf_digits ds -> checksum ds <= size ds * w.-1.
Proof. by move=> h; rewrite -(checksum_sumn h) leq_addr. Qed.

(** THE WOTS+/WOTS-TW CHECKSUM LEMMA (wotstw.tex, one-time security
    paragraph; EasyCrypt [two_encodings]): two distinct well-formed
    message digit vectors of the same length have checksum-extended
    encodings such that the first is strictly below the second at some
    coordinate.  Consumed with [ds' := forged] and [ds := honest]
    message digits.  Either the forged message digits are already
    smaller somewhere, or they dominate the honest ones pointwise, in
    which case the forged checksum is strictly smaller and
    [digits_w_exists_lt] locates a smaller checksum digit. *)
Lemma checksum_exists_lt (len2 : nat) (ds ds' : seq nat) :
  0 < w -> size ds' = size ds ->
  wf_digits ds -> wf_digits ds' ->
  size ds * w.-1 < w ^ len2 ->
  ds' <> ds ->
  exists2 k, k < size ds + len2 &
    nth 0 (encode_chk len2 ds') k < nth 0 (encode_chk len2 ds) k.
Proof.
move=> w_gt0 sz hds hds' hfit hne.
case: (boolP [forall k : 'I_(size ds), nth 0 ds k <= nth 0 ds' k]) => [hall|].
- (* forged digits dominate pointwise: the checksum block decides *)
  have hsum : sumn ds < sumn ds'.
    apply: ltn_sumn_nth; first by rewrite sz.
    + by move=> k hk; exact: (forallP hall (Ordinal hk)).
    + by move=> e; apply: hne; rewrite e.
  have hchk : checksum ds' < checksum ds.
    rewrite -(ltn_add2r (sumn ds')) (checksum_sumn hds') sz.
    by rewrite -(checksum_sumn hds) ltn_add2l.
  have hcb : checksum ds < w ^ len2 := leq_ltn_trans (checksum_leq hds) hfit.
  have [k hk hd] := digits_w_exists_lt w_gt0 hchk hcb.
  exists (size ds + k); first by rewrite ltn_add2l.
  have hc : (size ds + k < size ds) = false by rewrite ltnNge leq_addr.
  by rewrite /encode_chk !nth_cat sz hc addKn.
- (* otherwise the message block already has a smaller coordinate *)
  rewrite negb_forall => /existsP[k hk'].
  have hk : nth 0 ds' k < nth 0 ds k by rewrite ltnNge.
  exists k; first by apply: ltn_addr; apply: ltn_ord.
  by rewrite /encode_chk !nth_cat sz ltn_ord /=.
Qed.

End BaseW.
