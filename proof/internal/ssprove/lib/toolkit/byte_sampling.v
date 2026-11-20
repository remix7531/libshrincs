(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.toolkit.byte_sampling

    Uniform byte tuples, their ordinal encodings, and independent sequence
    sampling. The tuple sampler is supplied with its defining equations:
    this applies to the public sample_bytes without duplicating that sampler
    or importing the concrete schemes into the library. *)

From HB Require Import structures.
From Shrincs.internal.ssprove.lib Require Import prelude.
From Shrincs.internal.ssprove.lib.toolkit Require Import sample_seq probability.
From mathcomp Require Import word_ssrZ word reals distr realsum.
From SSProve.Crypt Require Import jasmin_word jasmin_wsize.
From Stdlib Require Import BinInt Lia.
Import PackageNotation.
Local Close Scope Z_scope.
Local Open Scope package_scope.
(* ------------------------------------------------------------------ *)
(** ** Byte and ordinal conversions *)

Definition byte_of_ord (i : 'I_256) : word U8 :=
  wrepr U8 (Z.of_nat i).
Lemma byte_value_range (b : word U8) : Z.to_nat (wunsigned b) < 256.
Proof.
have h := wunsigned_range b.
change (0 <= wunsigned b < 256)%Z in h.
apply/ltP.
lia.
Qed.
Definition ord_of_byte (b : word U8) : 'I_256 :=
  Ordinal (byte_value_range b).
Lemma byte_of_ordK : cancel byte_of_ord ord_of_byte.
Proof.
move=> i; apply/val_inj.
change (Z.to_nat (wunsigned (wrepr U8 (Z.of_nat i))) = i).
rewrite wunsigned_repr_small.
- have hi := ltn_ord i; move/ltP: hi => hi.
  change (0 <= Z.of_nat i < 256)%Z.
  lia.
- lia.
Qed.
Lemma ord_of_byteK : cancel ord_of_byte byte_of_ord.
Proof.
move=> b.
change (wrepr U8 (Z.of_nat (Z.to_nat (wunsigned b))) = b).
have heq : Z.of_nat (Z.to_nat (wunsigned b)) = wunsigned b.
{ have h := wunsigned_range b; lia. }
by rewrite heq wrepr_unsigned.
Qed.

Definition byte_fin : finType := HB.pack (word U8) (CanIsFinite ord_of_byteK).
Lemma card_byte : #|byte_fin| = 256%nat.
Proof.
rewrite -(card_ord 256).
exact: (@bij_eq_card byte_fin _ ord_of_byte (Bijective ord_of_byteK byte_of_ordK)).
Qed.
Lemma card_bytes n : #|{: n.-tuple byte_fin}| = (256 ^ n)%nat.
Proof. by rewrite card_tuple card_byte. Qed.
Definition bytes_rank n (bs : n.-tuple byte_fin) : 'I_(256 ^ n) :=
  cast_ord (card_bytes n) (enum_rank bs).
Definition bytes_unrank n (i : 'I_(256 ^ n)) : n.-tuple byte_fin :=
  enum_val (cast_ord (esym (card_bytes n)) i).
Lemma bytes_rankK n : cancel (bytes_rank n) (bytes_unrank n).
Proof. by move=> bs; rewrite /bytes_rank /bytes_unrank cast_ordK enum_rankK. Qed.
Lemma bytes_unrankK n : cancel (bytes_unrank n) (bytes_rank n).
Proof. by move=> i; rewrite /bytes_rank /bytes_unrank enum_valK cast_ord_comp cast_ord_id. Qed.
Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.
(* ------------------------------------------------------------------ *)
(** ** Point probabilities *)

Lemma byte_sampler_uniform (b : word U8) :
  Pr_fst (x ← sample uniform 256 ;; ret (byte_of_ord x)) b = (256%:R)^-1.
Proof.
rewrite Pr_fst_sample.
under eq_dlet do rewrite Pr_fst_ret.
rewrite dlet_uniform (bigD1 (ord_of_byte b)) //= ord_of_byteK dunit1E eqxx.
have -> : (\sum_(i < 256 | i != ord_of_byte b) dunit (byte_of_ord i) b : Axioms.R) = 0.
{ apply: big1 => i hi.
  rewrite dunit1E.
  have hn : byte_of_ord i != b.
  { apply/eqP => heq.
    have := congr1 ord_of_byte heq.
    rewrite byte_of_ordK => heqi.
    by move: hi; rewrite heqi eqxx. }
  by rewrite (negbTE hn). }
by rewrite addr0 div1r -pmulrn.
Qed.
Lemma dmargin_inj_at (A B : choiceType) (f : A -> B)
  (hf : injective f) (mu : {distr A / Axioms.R}) (a : A) :
  dmargin f mu (f a) = mu a.
Proof.
rewrite dmargin_psumE (psum_finseq (r := [:: a])).
- by [].
- move=> x /=; rewrite !inE (inj_eq hf) => hx.
  case heq: (x == a) => //.
  by move: hx; rewrite heq mul0r eqxx.
- by rewrite big_seq1 eqxx mul1r ger0_norm //.
Qed.
Lemma dmargin_cons_point (A : choiceType) (mu : {distr (seq A) / Axioms.R})
  (x b : A) (s : seq A) :
  dmargin (cons x) mu (b :: s) = (x == b)%:R * mu s.
Proof.
case: eqP => [->|hne].
- rewrite mul1r.
  apply: dmargin_inj_at.
  by move=> a c [].
- rewrite mul0r dmarginE.
  apply: dlet_eq0 => ys _.
  apply/eqP => [[heq _]].
  exact: hne heq.
Qed.
Lemma dlet_cons_point (A : choiceType) (mu : {distr A / Axioms.R})
  (nu : {distr (seq A) / Axioms.R}) (b : A) (s : seq A) :
  (\dlet_(x <- mu) dmargin (cons x) nu) (b :: s) = mu b * nu s.
Proof.
rewrite dletE.
have -> : (PosSum.psum (fun x => mu x * dmargin (cons x) nu (b :: s))) =
  PosSum.psum (fun x => mu x * ((x == b)%:R * nu s)).
{ apply: eq_psum => x; by rewrite dmargin_cons_point. }
rewrite (psum_finseq (r := [:: b])).
- by [].
- move=> x /=; rewrite !inE => hx.
  case heq: (x == b) => //.
  by move: hx; rewrite heq mul0r mulr0 eqxx.
- by rewrite big_seq1 eqxx mul1r ger0_norm // mulr_ge0.
Qed.
Lemma sample_seq_succ_distribution (A : choice_type) (d : dist A) n :
  Pr_fst (sample_seq d n.+1) =
  \dlet_(x <- Pr_fst d) dmargin (cons x) (Pr_fst (sample_seq d n)).
Proof.
rewrite /= Pr_fst_bind //.
apply: eq_dlet => x.
rewrite Pr_fst_bind //.
apply: eq_dlet => xs.
exact: Pr_fst_ret.
Qed.
Lemma sample_seq_cons_point (A : choice_type) (d : dist A) n b s :
  Pr_fst (sample_seq d n.+1) (b :: s) =
  Pr_fst d b * Pr_fst (sample_seq d n) s.
Proof. by rewrite sample_seq_succ_distribution dlet_cons_point. Qed.
Lemma sample_seq_nil_point (A : choice_type) (d : dist A) n :
  Pr_fst (sample_seq d n.+1) [::] = 0.
Proof.
rewrite sample_seq_succ_distribution.
apply: dlet_at0 => x.
rewrite dmarginE.
apply: dlet_eq0 => xs _.
by [].
Qed.
Lemma sample_seq_point (A : choice_type) (d : dist A) n (s : seq A) :
  Pr_fst (sample_seq d n) s =
  if size s == n then \prod_(x <- s) Pr_fst d x else 0.
Proof.
elim: n s => [|n ih] [|b s].
- by rewrite /= Pr_fst_ret dunit1E eqxx big_nil.
- by rewrite /= Pr_fst_ret dunit1E.
- exact: sample_seq_nil_point.
- rewrite sample_seq_cons_point ih /= big_cons.
  by rewrite eqSS; case: (size s == n); rewrite ?mulr0.
Qed.
Lemma sample_seq_byte_uniform (d : dist ('word U8))
  (hd : forall b, Pr_fst d b = (256%:R)^-1) n (s : seq (word U8)) :
  Pr_fst (sample_seq d n) s =
  if size s == n then ((256 ^ n)%nat)%:R^-1 else 0.
Proof.
rewrite sample_seq_point.
case: eqP => [hs|hne] //.
rewrite (eq_bigr (fun _ => (256%:R)^-1)); first by move=> b _; rewrite hd.
by rewrite big_const_seq count_predT -hs iter_mulr_1 exprVn natrX.
Qed.
(* ------------------------------------------------------------------ *)
(** ** Tuple transport *)

Lemma sample_tuple_to_seq (A : choice_type) (d : dist A)
  (s : forall n, raw_code (chTuple A n))
  (hs0 : s 0 = ret (nil_tuple A))
  (hsS : forall n, s n.+1 = (b ← d ;; bs ← s n ;; ret (cons_tuple b bs))) n :
  (bs ← s n ;; ret (tval bs)) = sample_seq d n.
Proof.
elim: n => [|n ih].
- by rewrite hs0.
- rewrite hsS !bind_assoc /= -ih.
  congr (bind _ _).
  apply functional_extensionality => b.
  by rewrite !bind_assoc.
Qed.
Lemma sample_tuple_valid (A : choice_type) (d : dist A)
  (s : forall n, raw_code (chTuple A n))
  (hs0 : s 0 = ret (nil_tuple A))
  (hsS : forall n, s n.+1 = (b ← d ;; bs ← s n ;; ret (cons_tuple b bs))) n :
  ValidCode emptym emptym (s n).
Proof.
elim: n => [|n ih].
- rewrite hs0; apply valid_ret.
- rewrite hsS.
  apply valid_bind; first exact: (prog_valid d).
  move=> b; apply valid_bind; first exact: ih.
  move=> bs; apply valid_ret.
Qed.
Lemma tuple_sampler_point (A : choice_type) n (c : raw_code (chTuple A n))
  (hc : ValidCode emptym emptym c) (bs : n.-tuple A) :
  Pr_fst (xs ← c ;; ret (tval xs)) (tval bs) = Pr_fst c bs.
Proof.
rewrite Pr_fst_bind //.
have -> : (\dlet_(xs <- Pr_fst c) Pr_fst (ret (tval xs))) =
  dmargin (fun xs : n.-tuple A => tval xs) (Pr_fst c).
{ apply: eq_dlet => xs; exact: Pr_fst_ret. }
apply: dmargin_inj_at.
exact: val_inj.
Qed.
Lemma sample_tuple_byte_uniform (d : dist ('word U8))
  (hd : forall b, Pr_fst d b = (256%:R)^-1)
  (s : forall n, raw_code (chTuple ('word U8) n))
  (hs0 : s 0 = ret (nil_tuple (word U8)))
  (hsS : forall n, s n.+1 = (b ← d ;; bs ← s n ;; ret (cons_tuple b bs)))
  n (bs : n.-tuple (word U8)) :
  Pr_fst (s n) bs = ((256 ^ n)%nat)%:R^-1.
Proof.
rewrite -(tuple_sampler_point _ _ _ (sample_tuple_valid _ _ _ hs0 hsS n) bs).
rewrite (sample_tuple_to_seq _ _ _ hs0 hsS).
by rewrite (sample_seq_byte_uniform d hd) size_tuple eqxx.
Qed.

(** Independent blocks concatenate to the existing sequence sampler. *)
Lemma sample_seq_cat (A : choice_type) (d : dist A) m n :
  sample_seq d (m + n)%nat =
  (xs ← sample_seq d m ;; ys ← sample_seq d n ;; ret (xs ++ ys)).
Proof.
elim: m => [|m ih].
- by rewrite add0n /= bind_ret.
- (* The nonempty prefix contributes its head sample first. *)
  rewrite addSn /= ih !bind_assoc.
  congr (bind _ _).
  apply functional_extensionality => b.
  rewrite !bind_assoc.
  congr (bind _ _).
  apply functional_extensionality => xs.
  by rewrite bind_assoc.
Qed.

Lemma uniform_point n (i : 'I_n) : (uniform n).π2 i = n%:R^-1.
Proof.
by rewrite /uniform /= /UniformDistrLemmas.r card_ord -!pmulrn mulr1n div1r.
Qed.

Section ByteTransport.
Context (d : dist ('word U8))
  (hd : forall b, Pr_fst d b = (256%:R)^-1)
  (s : forall n, raw_code (chTuple ('word U8) n))
  (hs0 : s 0 = ret (nil_tuple (word U8)))
  (hsS : forall n, s n.+1 = (b ← d ;; bs ← s n ;; ret (cons_tuple b bs))).

Lemma sample_tuple_unrank_uniform n :
  dmargin (bytes_unrank n) (uniform (256 ^ n)%nat).π2 = Pr_fst (s n).
Proof.
apply distr_ext => bs.
rewrite -[bs in LHS](bytes_rankK n bs) dmargin_inj_at.
- exact: (can_inj (bytes_unrankK n)).
- by rewrite uniform_point (sample_tuple_byte_uniform d hd s hs0 hsS).
Qed.

End ByteTransport.
