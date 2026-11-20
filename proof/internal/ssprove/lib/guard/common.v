(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.guard.common

    Constant-output adversaries for protocol-abort regression guards. They
    issue a fixed number of calls with fixed arguments, ignore every answer,
    and return either chosen bit. The count includes calls whose execution
    is cut short by an abort. *)

From Shrincs.internal.ssprove.lib Require Export prelude.
From mathcomp Require Export reals.

Import PackageNotation.
#[local] Open Scope package_scope.
#[local] Open Scope sep_scope.

Fixpoint guard_repeat (o : opsig) (x : src o) (n : nat)
    (answer : bool) : raw_code 'bool :=
  match n with
  | 0 => ret answer
  | n'.+1 => _ ← op o ⋅ x ;; guard_repeat o x n' answer
  end.

Lemma guard_repeat_valid (o : opsig) (x : src o) (n : nat) (answer : bool) :
  ValidCode emptym [fmap o] (guard_repeat o x n answer).
Proof.
elim: n => [|n ih] /=.
- exact: valid_ret.
- apply valid_opr.
  + by case: o x ih => [i [s t]] x ih; fmap_solve.
  + by move=> y.
Qed.

Definition guard_calls (o : opsig) (x : src o) (n : nat)
    (answer : bool) : package [fmap o] A_export.
Proof.
notypeclasses refine [package emptym ;
  [ RUN.1 ] : { 'unit ~> 'bool } (_) { guard_repeat o x n answer }
].
ssprove_valid.
exact: guard_repeat_valid.
Defined.

Lemma guard_calls_disj (o : opsig) (x : src o) (n : nat)
    (answer : bool) (G : nom_package) :
  disj (guard_calls o x n answer : nom_package) G.
Proof.
change (supp (emptym : Locations) `#` supp G).
by rewrite supp_empty_Location fdisjoint0s.
Qed.

(** Equality of the two initial executions implies zero advantage. *)
Lemma guard_adv_eq (G0 G1 : nom_package) (o : opsig) (x : src o)
    (n : nat) (answer : bool) :
  Pr_code (code_link (guard_repeat o x n answer) G0) empty_heap =
    Pr_code (code_link (guard_repeat o x n answer) G1) empty_heap ->
  Adv G0 G1 (guard_calls o x n answer) = 0%R.
Proof.
move=> heq.
rewrite (Adv_AdvantageE G0 G1 (guard_calls o x n answer)
  (guard_calls_disj o x n answer G0)
  (guard_calls_disj o x n answer G1)).
rewrite /AdvantageE !Pr_Pr_code !resolve_link /guard_calls.
simplify_linking.
by rewrite heq GRing.subrr Num.Theory.normr0.
Qed.

Lemma guard_repeat_link_eq (G0 G1 : raw_package) (o : opsig) (x : src o)
    (n : nat) (answer : bool) :
  resolve G0 o x = resolve G1 o x ->
  code_link (guard_repeat o x n answer) G0 =
    code_link (guard_repeat o x n answer) G1.
Proof.
move=> heq.
elim: n => [|n ih] //=.
by rewrite heq ih.
Qed.

(** An oracle whose code does not depend on the game bit can abort,
    including inside arbitrary scheme samplers, with no distinguishing gap. *)
Lemma guard_adv_oracle_eq (G0 G1 : nom_package) (o : opsig) (x : src o)
    (n : nat) (answer : bool) :
  resolve G0 o x = resolve G1 o x ->
  Adv G0 G1 (guard_calls o x n answer) = 0%R.
Proof.
move=> heq.
apply: guard_adv_eq.
by rewrite (guard_repeat_link_eq G0 G1 o x n answer heq).
Qed.

(** The output marginal suffices when the branches write different heaps. *)
Lemma guard_adv_fst_eq (G0 G1 : nom_package) (o : opsig) (x : src o)
    (n : nat) (answer : bool) :
  distr.dmargin fst
      (Pr_code (code_link (guard_repeat o x n answer) G0) empty_heap) =
    distr.dmargin fst
      (Pr_code (code_link (guard_repeat o x n answer) G1) empty_heap) ->
  Adv G0 G1 (guard_calls o x n answer) = 0%R.
Proof.
move=> heq.
rewrite (Adv_AdvantageE G0 G1 (guard_calls o x n answer)
  (guard_calls_disj o x n answer G0)
  (guard_calls_disj o x n answer G1)).
rewrite /AdvantageE !Pr_Pr_code !resolve_link /guard_calls.
simplify_linking.
by rewrite heq GRing.subrr Num.Theory.normr0.
Qed.

(** Two fixed calls exercise an actual phase transition before the query. *)
Definition guard_then (o0 : opsig) (x0 : src o0) (o1 : opsig)
    (x1 : src o1) (hneq : o0.1 != o1.1) (answer : bool) : package [fmap o0; o1] A_export.
Proof.
notypeclasses refine [package emptym ;
  [ RUN.1 ] : { 'unit ~> 'bool } (_) {
    _ ← op o0 ⋅ x0 ;;
    _ ← op o1 ⋅ x1 ;;
    ret answer
  }
].
ssprove_valid.
apply valid_opr.
- by clear hneq; case: o0 x0 => [i [s t]] x0; fmap_solve.
- move=> y.
  apply valid_opr.
  + clear y.
    case: o0 x0 hneq => [i [s t]] x0.
    case: o1 x1 => [j [u v]] x1 /= hneq.
    by rewrite /fhas /= setmE eq_sym (negbTE hneq) setmE eqxx.
  + move=> z.
    exact: valid_ret.
Defined.

Lemma guard_then_disj (o0 : opsig) (x0 : src o0) (o1 : opsig)
    (x1 : src o1) (hneq : o0.1 != o1.1) (answer : bool) (G : nom_package) :
  disj (guard_then o0 x0 o1 x1 hneq answer : nom_package) G.
Proof.
change (supp (emptym : Locations) `#` supp G).
by rewrite supp_empty_Location fdisjoint0s.
Qed.

Lemma guard_then_adv_eq (G0 G1 : nom_package)
    (o0 : opsig) (x0 : src o0) (o1 : opsig) (x1 : src o1) (hneq : o0.1 != o1.1) (answer : bool) :
  Pr_code (_ ← resolve G0 o0 x0 ;; _ ← resolve G0 o1 x1 ;; ret answer)
      empty_heap =
    Pr_code (_ ← resolve G1 o0 x0 ;; _ ← resolve G1 o1 x1 ;; ret answer)
      empty_heap ->
  Adv G0 G1 (guard_then o0 x0 o1 x1 hneq answer) = 0%R.
Proof.
move=> heq.
rewrite (Adv_AdvantageE G0 G1 (guard_then o0 x0 o1 x1 hneq answer)
  (guard_then_disj o0 x0 o1 x1 hneq answer G0)
  (guard_then_disj o0 x0 o1 x1 hneq answer G1)).
rewrite /AdvantageE !Pr_Pr_code !resolve_link /guard_then.
simplify_linking.
by rewrite heq GRing.subrr Num.Theory.normr0.
Qed.
