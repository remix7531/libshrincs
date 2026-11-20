(* SPDX-License-Identifier: MIT
 *
 * libshrincs - formally verified SHRINCS implementations.
 *)

(** * Shrincs.internal.ssprove.lib.math.full_tree_paths

    All-node paths in right/left/parent order, including leaf positions.
    The two child values are available before their parent's target query. *)

From mathcomp Require Import boot order.
From Shrincs.internal.ssprove.lib.math Require Import bin_tree tree_paths.
From Stdlib Require Import Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Set Default Goal Selector "!".
Set Bullet Behavior "Strict Subproofs".

Fixpoint full_paths {A : Type} (t : bt A) : seq (seq bool) :=
  match t with
  | BLeaf _ => [:: [::]]
  | BNode l r => [::] ::
      ([seq false :: p | p <- full_paths l] ++
       [seq true :: p | p <- full_paths r])
  end.

Definition full_postorder {A : Type} pos (t : bt A) :=
  [seq pos ++ p | p <- rev (full_paths t)].

Lemma cons_path_mem b c p (ps : seq (seq bool)) :
  (b :: p \in [seq c :: q | q <- ps]) = ((b == c) && (p \in ps)).
Proof.
case: b; case: c; elim: ps => [|q ps ih] //=;
  by rewrite !inE /= ih.
Qed.

Lemma full_paths_mem {A : Type} (t : bt A) p :
  (p \in full_paths t) =
    ((p \in internal_paths t) || (p \in leaf_paths t)).
Proof.
elim: t p => [a|l ihl r ihr] [|b p] //=.
rewrite !inE !mem_cat !cons_path_mem /= ihl ihr.
by case: b; rewrite /= ?orbF.
Qed.

Lemma full_paths_uniq {A : Type} (t : bt A) : uniq (full_paths t).
Proof.
elim: t => [a|l ihl r ihr] //=.
apply/andP; split.
- rewrite mem_cat negb_or.
  apply/andP; split; apply/negP=> /mapP[p _]; by [].
- have hinj (b : bool) : injective (cons b) by move=> p q [].
  rewrite cat_uniq !(map_inj_uniq (hinj _)) ihl ihr /= andbT.
  apply/hasPn=> p /mapP[q _ ->].
  by apply/negP=> /mapP[q' _].
Qed.

Lemma full_paths_size {A : Type} (t : bt A) :
  size (full_paths t) = 2 * bt_nleaves t - 1.
Proof.
elim: t => [a|l ihl r ihr] //=.
rewrite size_cat !size_map ihl ihr.
have hl := bt_nleaves_pos l.
have hr := bt_nleaves_pos r.
move/ltP: hl=> hl; move/ltP: hr=> hr.
rewrite !subnE !mulnE !addnE.
lia.
Qed.

Lemma full_postorder_leaf {A : Type} pos (a : A) :
  full_postorder pos (BLeaf a) = [:: pos].
Proof. by rewrite /full_postorder /= cats0. Qed.

Lemma full_postorder_node {A : Type} pos (l r : bt A) :
  full_postorder pos (BNode l r) =
    full_postorder (rcons pos true) r ++
    full_postorder (rcons pos false) l ++ [:: pos].
Proof.
rewrite /full_postorder /= rev_cons rev_cat -!map_rev
  map_rcons !map_cat -!map_comp /= cats0 -cats1 catA.
congr (_ ++ [:: pos]).
congr (_ ++ _); apply: eq_map=> q /=; by rewrite cat_rcons.
Qed.

Lemma full_postorder_root {A : Type} (t : bt A) :
  full_postorder [::] t = rev (full_paths t).
Proof. by rewrite /full_postorder /= map_id. Qed.

Lemma full_postorder_size {A : Type} pos (t : bt A) :
  size (full_postorder pos t) = 2 * bt_nleaves t - 1.
Proof. by rewrite /full_postorder size_map size_rev full_paths_size. Qed.

Lemma full_postorder_uniq {A : Type} (t : bt A) :
  uniq (full_postorder [::] t).
Proof. by rewrite full_postorder_root rev_uniq full_paths_uniq. Qed.
