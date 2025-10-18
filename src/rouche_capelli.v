From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Import GRing.Theory.
Import VectorInternalTheory.
(*Import passmx.*)

HB.mixin Record isFinVector
  (R : nzRingType) (V : Type) of Vector R V & Finite V := {}.

#[short(type="finVectType")]
HB.structure Definition FinVector
  (R : nzRingType) := { V of isFinVector R V & }.

HB.instance Definition _ (K : finFieldType) m n := isFinVector.Build K 'M[K]_(m,n).
HB.instance Definition _ (K : finFieldType) m := isFinVector.Build K {poly_m K}.
(*HB.instance Definition _ (K : fieldType) (fvT : finVectType K)
  := [Finite of {vspace fvT} by <:].*)
HB.instance Definition _ (K : fieldType) (fvT : finVectType K) (U : {vspace fvT}) :=
  [Finite of subvs_of U by <:].
HB.instance Definition _ (K : fieldType) (fvT : finVectType K) (U : {vspace fvT}) :=
  isFinVector.Build K (subvs_of U).

Section finvect_lemmas.

Arguments v2r_inj {R vT}.

(** 
 * Lemma: Cardinality of a Finite-Dimensional Vector Subspace
 * 
 * This lemma establishes a fundamental result in linear algebra: the cardinality 
 * of a finite-dimensional vector subspace U over a finite field K equals 
 * |K|^dim(U), where |K| is the size of the field and dim(U) is the dimension 
 * of the subspace.
 * 
 * This is a direct consequence of the fact that any d-dimensional vector space 
 * over a field K is isomorphic to K^d, and therefore has exactly |K|^d elements.
 * 
 * The proof constructs an explicit bijection between the elements of U and 
 * the coordinate vectors in K^d, establishing the cardinality equality.
 *)
Local Lemma card_vspace_helper
  (K : finFieldType) (fvT : finVectType K) (U : {vspace fvT}) :
  #|U| = #|'rV[K]_(\dim U)|.
Proof.
transitivity #|[set val x | x in subvs_of U]|.
  apply: eq_card => v /=.
  apply/idP/idP; first by move/vsprojK<-; apply: imset_f.
  by case/imsetP=> /= -[] u /= ? _ ->.
transitivity #|[set v2r x | x in subvs_of U]|.
  by rewrite !card_imset//; [exact: v2r_inj | exact: val_inj].
apply: eq_card => /= r.
rewrite !inE -/(is_true _).
by rewrite -(r2vK r) mem_imset; last exact: v2r_inj.
Qed.

Lemma card_vspace
  (K : finFieldType) (fvT : finVectType K) (U : {vspace fvT}) :
  #|U| = (#| {:K} | ^ (\dim U))%N.
Proof. by rewrite card_vspace_helper card_mx mul1n. Qed.

Local Corollary card_vspace_helper_rV {K : finFieldType} n (U : {vspace 'rV[K]_n}) :
  #|U| = #|'rV[K]_(\dim U)|.
Proof. by rewrite !card_vspace card_mx mul1n. Qed.

Local Corollary card_vspace_rV {K : finFieldType} n (U : {vspace 'rV[K]_n}) :
  #|U| = (#| {:K} | ^ (\dim U))%N.
Proof. exact: card_vspace. Qed.

Lemma card_lker_lfun
  (K : fieldType) (aT : finVectType K) (rT : vectType K) (f : {linear aT -> rT}) :
  #|lker (linfun f)| = #|[set x : aT | f x == 0]|.
Proof. by apply: eq_card=> /= x; rewrite !inE memv_ker lfunE. Qed.

End finvect_lemmas.

Section vector_ext.
Lemma diffvv {K : fieldType} {vT : vectType K} (U : {vspace vT}) :
  (U :\: U = 0)%VS.
Proof. by apply/eqP; rewrite diffv_eq0 subvv. Qed.

Lemma limg_lker {K : fieldType} {aT rT : vectType K} (f : 'Hom(aT, rT)) :
    (f @: lker f = 0)%VS.
Proof. by apply/eqP; rewrite -lkerE. Qed.

Lemma HomK {R : nzRingType} {vT wT : vectType R} (A : 'M_(dim vT, dim wT)) :
  f2mx (Hom A) = A.
Proof. by []. Qed.
End vector_ext.

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

Section FiniteSolutionCounting.
(* Proving that if exists_nonzero_kernel in a finite domain,
   the number of vectors satisify A *m X = 0 is (#| {:K} | ^ (n - \rank A))%N.
*)
Variable K : finFieldType.
Variable vT : vectType K.

(* Column span of a matrix, as a set of column vectors (boolean-quantified). *)
Definition colspan m n (B : 'M[K]_(m, n)) : {set 'cV[K]_m} :=
  [set x | [exists y : 'cV[K]_n, B *m y == x]].

(* B a left-kernel as a basis to be spanned as the row space;
   here it is used as a predicate on the row space.
*)
Definition rowspan m n (B : 'M[K]_(m, n)) : {set 'rV[K]_n} :=
  [set x | [exists y : 'rV[K]_m, y *m B == x]].

Lemma sub_coker_colspan m n (A : 'M[K]_(m, n)) :
  forall x : 'cV[K]_n, x \in colspan (cokermx A) -> A *m x == 0.
Proof.
move => x.
rewrite inE => /existsP [y /eqP Ey].
move: Ey. move/eqP.
rewrite eq_sym => /eqP ->.
apply/eqP.
by rewrite mulmxA mulmx_coker mul0mx.
Qed.

Lemma submx_castmx m1 m2 n (A : 'M[K]_(m1, n)) (B : 'M[K]_(m2, n)) e :
  (A <= B)%MS -> @submx.body K m1 m2 n A (castmx e B).
Proof.
move=> sAB.
have HB := eqmx_cast B e.
have /eqmxP HBb := HB.
rewrite -(eqmxP HBb) in sAB.
exact: sAB.
Qed.

(* Lemma for casting matrix multiplication with row vectors *)
Lemma castmx_mul_row m n p q (e_m : m = p) (e_n : n = q) 
      (w : 'rV[K]_m) (M : 'M[K]_(m, n)) :
  castmx (erefl, e_m) w *m castmx (e_m, e_n) M = castmx (erefl, e_n) (w *m M).
Proof.
  subst p q.
  by rewrite !castmx_id.
Qed.

Section card_lker.
Import passmx.

Variables (aT rT : finVectType K).
Variable f : 'Hom(aT, rT).
Variable e : (\dim {:aT}).-tuple aT.
Hypothesis be : basis_of {:aT} e.
Variable e' : (\dim {:rT}).-tuple rT.
Hypothesis be' : basis_of {:rT} e'.

Lemma card_lker_mxof : #|(lker f)| =
                      #|[set x : 'rV[K]_(\dim {:aT}) | x *m (mxof e e' f) == 0]|.
Proof.
have/card_imset<-/= := (can_inj (vecofK be)).
apply: eq_card=> /= v.
rewrite -[in RHS](rVofK be v) mem_imset; last by exact: can_inj (vecofK be).
rewrite !inE memv_ker mul_mxof (rVofK be).
by rewrite -[LHS](can_eq (rVofK be')) linear0.
Qed.

End card_lker.

Section counting.
  
Variables (m n : nat) (A : 'M[K]_(m, n)).

Definition stdbasis {n} := [tuple 'e_i : 'rV[K]_(\dim {:'rV[K]_n}) | i < \dim {:'rV[K]_n}].

Lemma dim_rV p : \dim {:'rV[K]_p} = p.
Proof. by rewrite dimvf /dim /= mul1n. Qed.

Lemma card_lker_Hom : #|lker (Hom A)| = #|[set x : 'rV[K]_m | x *m A == 0]|.
Proof.
have/card_imset<-/= := (can_inj (@r2vK K {poly_m K})).
apply: eq_card=> /= v.
rewrite -[in RHS](v2rK v) mem_imset; last exact: r2v_inj.
rewrite !inE memv_ker.
rewrite -[RHS](inj_eq (@r2v_inj _ _)) linear0.
by rewrite [in LHS]unlock.
Qed.

Lemma cancel_row_free p q (g : {linear 'rV[K]_p -> 'rV[K]_q})
                          (h : {linear 'rV[K]_q -> 'rV[K]_p}) :
  cancel g h -> row_free (lin1_mx g).
Proof.
move=> gh.
apply/row_freeP.
exists (lin1_mx h).
rewrite -[lin1_mx g]mul1mx.
apply/row_matrixP => i.
by rewrite !row_mul !mul_rV_lin1 /= gh.
Qed.

Lemma row_free_tr p q (M : 'M[K]_(p,q)) : p = q -> row_free M^T = row_free M.
Proof. by move=> pq; rewrite -row_leq_rank mxrank_tr -{1}pq row_leq_rank. Qed.

Lemma count_kernel_vectors :
  #| [set x : 'rV[K]_m | x *m A == 0] | = (#| {:K} | ^ (m - \rank A))%N.
Proof.
by rewrite -card_lker_Hom /lker HomK card_vspace /dimv mx2vsK mxrank_ker.
Qed.

End counting.

End FiniteSolutionCounting.

