From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq choice.
From mathcomp Require Import fintype finfun bigop finset fingroup perm order.
From mathcomp Require Import div prime binomial ssralg finalg zmodp matrix.
From mathcomp Require Import mxalgebra vector tuple.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.

Section RoucheCapelliTheorems.

Variable R : fieldType.


Lemma mxrank_sub_eqmx m n p (A : 'M[R]_(m,n)) (B : 'M[R]_(p,n)) :
  \rank A = \rank B -> (A <= B)%MS -> (A == B)%MS.
Proof.
by move/eqP => Hr /mxrank_leqif_eq/leqifP; rewrite ltn_neqAle Hr; case: ifPn.
Qed.

Lemma rouche1 m n (A : 'M[R]_(m,n)) (B : 'rV_n) :
  (exists x, x *m A = B) <-> (\rank A = \rank (col_mx A B)).
Proof.
rewrite -addsmxE; split.
  case=> x AB; apply/eqmx_rank.
  by rewrite -AB addsmx_sub submx_refl addsmxSl submxMl.
move/mxrank_sub_eqmx/(_ (addsmxSl A B)).
case/eqmxP/eqmx_sym/addsmx_idPl/submxP => x ->.
by exists x.
Qed.

Lemma rouche2 m n (A : 'M[R]_(m,n)) (B : 'rV_n) :
  \rank A = \rank (col_mx A B) -> \rank A = m ->
  exists! x, x *m A = B.
Proof.
move=> AB Am.
case/rouche1: (AB) => x Hx.
exists x; split => // x' Hx'.
move/eqP: Hx' (sub_kermx A (x'-x)).
rewrite -Hx -GRing.subr_eq0 -mulmxBl => -> /submxP [y] Hx'.
have := mxrank_sub_eqmx _ (sub0mx m (kermx A)).
rewrite  mxrank_ker Am subnn mxrank0 andbC => /(_ erefl) /eqmx0P Hker.
by move: Hx'; rewrite Hker mulmx0 => /GRing.subr0_eq /esym.
Qed.

Lemma exists_nonzero_kernel m n (A : 'M[R]_(m, n)) :
  (\rank A < m)%N -> exists y : 'rV_m, y *m A = 0 /\ y != 0.
Proof.
rewrite -subn_gt0 -mxrank_ker lt0n mxrank_eq0 => /matrix0Pn [i] [j] Hij.
exists (row i (kermx A)); split.
  exact/sub_kermxP/row_sub.
by apply/rV0Pn; exists j; rewrite mxE.
Qed.

Lemma kernel_membership m n p (A : 'M[R]_(m, n)) (X : 'M[R]_(n, p)) :
  A *m X = 0 -> (X^T <= kermx A^T)%MS.
Proof.
move=> HX; apply/sub_kermxP.
by rewrite -(trmx_mul A X) HX trmx0.
Qed.
Lemma kernel_coeff_exists m n p (A : 'M[R]_(m, n)) (X : 'M[R]_(n, p)) :
  A *m X = 0 -> exists P : 'M[R]_(p, n),
    X^T = P *m kermx A^T.
Proof.
move=> HX.
have /submxP [P ->] : (X^T <= kermx A^T)%MS.
  by apply: kernel_membership.
by exists P.
Qed.

End RoucheCapelliTheorems.
Section FiniteFieldCounting.

Variable K : finFieldType.

Lemma bij_card_image (aT rT : finType) (f : aT -> rT) (A : {set aT}) :
  bijective f -> #|A| = #|f @: A|.
Proof.
move=> bij_f.
have inj_f: injective f by apply: bij_inj.
by rewrite card_in_imset // => x y _ _; apply: inj_f.
Qed.

Lemma card_vspace_fin_helper n (U : {vspace 'cV[K]_n}) :
  #|U| = (#| {:K} | ^ (\dim U))%N.
Proof.
pose d := (\dim U).
pose to_row (w : subvs_of U) := \row_i coord (vbasis U) i (val w).
pose sum_rw (rw : 'rV_d) : 'cV[K]_n := \sum_i (rw ord0 i *: (vbasis U)`_i).
have mem_sum_rw rw : sum_rw rw \in U.
  apply: memv_suml => j _.
  by apply: memvZ; apply: (vbasis_mem (U:=U)); apply: memt_nth.
pose from_row (rw : 'rV_d) : subvs_of U := Sub (sum_rw rw) (mem_sum_rw rw).
have to_from : forall rw, to_row (from_row rw) = rw.
  move=> rw; apply/rowP=> i; rewrite mxE.
  have -> : val (from_row rw) = sum_rw rw by [].
  by rewrite coord_sum_free ?(basis_free (vbasisP U)).
have from_to : forall w : subvs_of U, from_row (to_row w) = w.
  move=> w; apply/val_inj.
  rewrite /from_row /sum_rw /to_row /=.
  have -> : \sum_i (to_row w) ord0 i *: (vbasis U)`_i
           = \sum_i (coord (vbasis U) i (val w)) *: (vbasis U)`_i.
    by apply: eq_bigr => i _; rewrite mxE.
  by rewrite (coord_vbasis (subvsP w)).
have bij_to_row : bijective to_row.
  by exists from_row; split => [x | x]; [exact: from_to | exact: to_from].
rewrite -(bij_card_image bij_to_row [set: subvs_of U]).
rewrite cardsT card_mx /d.
by rewrite muln1.
Qed.

Lemma card_vspace_fin n (U : {vspace 'cV[K]_n}) :
  #|U| = (#| {:K} | ^ (\dim U))%N.
Proof.
pose d := (\dim U).
pose to_row (w : subvs_of U) := \row_i coord (vbasis U) i (val w).
pose sum_rw (rw : 'rV_d) : 'cV[K]_n := \sum_i (rw ord0 i *: (vbasis U)`_i).
have mem_sum_rw rw : sum_rw rw \in U.
  apply: memv_suml => j _.
  by apply: memvZ; apply: (vbasis_mem (U:=U)); apply: memt_nth.
pose from_row (rw : 'rV_d) : subvs_of U := Sub (sum_rw rw) (mem_sum_rw rw).
have to_from : forall rw, to_row (from_row rw) = rw.
  move=> rw; apply/rowP=> i; rewrite mxE.
  have -> : val (from_row rw) = sum_rw rw by [].
  by rewrite coord_sum_free ?(basis_free (vbasisP U)).
have from_to : forall w : subvs_of U, from_row (to_row w) = w.
  move=> w; apply/val_inj.
  rewrite /from_row /sum_rw /to_row /=.
  have -> : \sum_i (to_row w) ord0 i *: (vbasis U)`_i
           = \sum_i (coord (vbasis U) i (val w)) *: (vbasis U)`_i.
    by apply: eq_bigr => i _; rewrite mxE.
  by rewrite (coord_vbasis (subvsP w)).
have bij_to_row : bijective to_row.
  by exists from_row; split => [x | x]; [exact: from_to | exact: to_from].
rewrite -(bij_card_image bij_to_row [set: subvs_of U]).
rewrite cardsT card_mx /d.
by rewrite muln1.
Qed.

Lemma count_kernel_vectors m n (A : 'M[K]_(m, n)) :
  #| [set x : 'cV_n | A *m x == 0] | = (#| {:K} | ^ (n - \rank A))%N.
Proof.
pose S := [set x : 'cV_n | A *m x == 0].
have sub_coker x : x \in colspan (cokermx A) -> A *m x == 0.
  by case/colP=> y ->; rewrite -mulmxA mulmx_coker mul0mx.
have sub_kernel x : A *m x == 0 -> x \in colspan (cokermx A).
  move=> HAx0.
  have /submxP [Y HY] : (x^T <= kermx A^T)%MS by apply: kernel_membership.
  have hx : x = (kermx A^T)^T *m Y^T.
    by move: HY; rewrite -trmxK trmx_mul trmx_tr.
  rewrite hx /cokermx; exact/colP.
have kerE : S = colspan (cokermx A).
  apply/setP=> x; rewrite !inE; apply/idP/idP; [exact: sub_kernel | exact: sub_coker].
rewrite kerE card_vspace_fin; congr (_ ^ _)%N.
by rewrite dim_col mxrank_coker.
Qed.

End FiniteFieldCounting.
