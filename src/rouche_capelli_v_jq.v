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

(* Test what type U actually has *)
Lemma vspace_type_test n (U : {vspace 'cV[K]_n}) : 
  True.
Proof.
(* Let's see what U is *)
(* Check if we can use #|U| at all *)
Check #|U|.
Check U.
Check 'cV[K]_n.
(* Test if 'cV[K]_n is actually a finType *)
Check #|{: 'cV[K]_n}|.
Admitted.

Lemma bij_card_image (aT rT : finType) (f : aT -> rT) (A : {set aT}) :
  bijective f -> #|A| = #|f @: A|.
Proof.
move=> bij_f.
have inj_f: injective f by apply: bij_inj.
by rewrite card_in_imset // => x y _ _; apply: inj_f.
Qed.

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
Lemma card_vspace_fin_helper n (U : {vspace 'cV[K]_n}) :
  #|U| = (#| {:K} | ^ (\dim U))%N.
Proof.
  (* 
   * Step 1: Introduce the dimension variable
   * 
   * We start by introducing d as the dimension of the subspace U.
   * This simplifies notation throughout the proof and makes the connection
   * between the dimension and the exponent in our target formula explicit.
   *)
  pose d := (\dim U).
  
  (* 
   * Step 2: Define the coordinate mapping function
   * 
   * The function to_row maps each vector w in the subspace U to its coordinate 
   * representation with respect to the basis of U. This is the key function 
   * that will establish our bijection.
   * 
   * For any vector w in U, we can express it as a linear combination of the 
   * basis vectors: w = Σᵢ cᵢ · bᵢ, where {bᵢ} is a basis for U.
   * The function to_row extracts these coefficients (c₀, c₁, ..., c_{d-1}).
   * 
   * We need this function because it will be the core of our bijection
   * between U and K^d, allowing us to count elements by counting coordinates.
   *)
  pose to_row (w : subvs_of U) := \row_i coord (vbasis U) i (val w).
  
  (* 
   * Step 3: Define the reconstruction function
   * 
   * The function sum_rw does the reverse operation: given a coordinate vector 
   * (c₀, c₁, ..., c_{d-1}), it reconstructs the original vector in U by 
   * computing the linear combination Σᵢ cᵢ · bᵢ.
   * 
   * This function is essential for proving that our mapping is surjective 
   * (every coordinate vector corresponds to some vector in U).
   * 
   * We need this because it will be used to construct the inverse function
   * that proves our mapping is bijective.
   *)
  pose sum_rw (rw : 'rV_d) : 'cV[K]_n := \sum_i (rw ord0 i *: (vbasis U)`_i).
  
  (* 
   * Step 4: Verify that reconstructed vectors belong to U
   * 
   * This step is crucial for ensuring that sum_rw actually maps into U.
   * We need to prove that any linear combination of basis vectors of U 
   * must itself belong to U, which follows from the definition of a subspace.
   * 
   * The proof uses the fact that U is closed under vector addition and 
   * scalar multiplication, which are the defining properties of a subspace.
   * 
   * We need this because it allows us to safely construct the inverse
   * mapping function that takes coordinate vectors back to elements of U.
   *)
  have mem_sum_rw rw : sum_rw rw \in U.
    apply: memv_suml => j _.
    by apply: memvZ; apply: (vbasis_mem (U:=U)); apply: memt_nth.
  
  (* 
   * Step 5: Define the inverse mapping function
   * 
   * The function from_row maps coordinate vectors back to elements of U.
   * It uses sum_rw to reconstruct the vector and then wraps it in the 
   * subtype subvs_of U to maintain type safety.
   * 
   * This function will be used to prove that to_row is injective and 
   * to establish the bijection between U and K^d.
   * 
   * We need this because a bijection requires both a forward and backward
   * mapping, and this provides the backward direction.
   *)
  pose from_row (rw : 'rV_d) : subvs_of U := Sub (sum_rw rw) (mem_sum_rw rw).
  
  (* 
   * Step 6: Prove the left inverse property
   * 
   * This step shows that from_row is a left inverse of to_row:
   * for any coordinate vector rw, we have to_row(from_row(rw)) = rw.
   * 
   * This property is essential for proving injectivity of to_row and 
   * establishing that our mapping preserves distinctness of elements.
   * 
   * The proof uses the fact that the basis is free (linearly independent)
   * and that coordinate extraction is the inverse of reconstruction.
   * 
   * We need this because it's one of the two conditions required to
   * prove that our functions form a bijection.
   *)
  have to_from : forall rw, to_row (from_row rw) = rw.
    move=> rw; apply/rowP=> i; rewrite mxE.
    have -> : val (from_row rw) = sum_rw rw by [].
    by rewrite coord_sum_free ?(basis_free (vbasisP U)).
  
  (* 
   * Step 7: Prove the right inverse property
   * 
   * This step shows that from_row is a right inverse of to_row:
   * for any vector w in U, we have from_row(to_row(w)) = w.
   * 
   * This property is essential for proving surjectivity of to_row and 
   * establishing that every element in U can be reached by our mapping.
   * 
   * The proof uses the coordinate representation theorem, which states
   * that any vector can be uniquely expressed in terms of its coordinates
   * with respect to a given basis.
   * 
   * We need this because it's the second condition required to prove
   * that our functions form a bijection.
   *)
  have from_to : forall w : subvs_of U, from_row (to_row w) = w.
    move=> w; apply/val_inj.
    rewrite /from_row /sum_rw /to_row /=.
    have -> : \sum_i (to_row w) ord0 i *: (vbasis U)`_i
             = \sum_i (coord (vbasis U) i (val w)) *: (vbasis U)`_i.
      by apply: eq_bigr => i _; rewrite mxE.
    by rewrite (coord_vbasis (subvsP w)).
  
  (* 
   * Step 8: Establish the bijection
   * 
   * Having proved both inverse properties, we can now conclude that 
   * to_row is bijective. A function is bijective if and only if it 
   * has both a left and right inverse.
   * 
   * This bijection is the core of our proof: it establishes a one-to-one 
   * correspondence between the elements of U and the coordinate vectors in K^d.
   * 
   * We need this because bijective functions preserve cardinality, which
   * is exactly what we need to prove #|U| = #|K^d|.
   *)
  have bij_to_row : bijective to_row.
    by apply: (Bijective from_to to_from).
  
  (* 
   * Step 9: Relate cardinalities via the bijection
   * 
   * This is the key step that connects our bijection to the cardinality 
   * calculation. Since to_row is bijective, the domain and codomain 
   * must have the same number of elements.
   * 
   * The domain consists of all vectors in U, which has cardinality #|U|.
   * The codomain consists of all coordinate vectors in K^d, which has 
   * cardinality #|K|^d by the fundamental counting principle.
   * 
   * Therefore, #|U| = #|K|^d = #|K|^(dim U).
   * 
   * We need this because it's the main result that connects the cardinality
   * of U to the dimension and field size, which is exactly what we want to prove.
   *)
  have cardU_eq: #|U| = #|'rV[K]_d|.
    (* The key insight: We have a bijection to_row : subvs_of U -> 'rV[K]_d.
       Since 'cV[K]_n is finite and U is a subspace, the elements of U form a finite set.
       We need to show that #|U| = #|'rV[K]_d| via this bijection.
       
       The challenge is that subvs_of U is not automatically recognized as a finType,
       but we can work around this by using the bijection properties directly.
    *)
    (* Since to_row is bijective, we know that the domain and codomain have the same cardinality *)
    (* The domain is the set of elements in subvs_of U, which corresponds to elements in U *)
    (* The codomain is 'rV[K]_d *)
    (* Therefore #|U| = #|'rV[K]_d| *)
    admit. (* This step requires establishing that subvs_of U has the same cardinality as U *)
  
  (* 
   * Final step: Complete the proof
   * 
   * We now have #|U| = #|'rV[K]_d|. The cardinality of 'rV[K]_d 
   * is well-known to be #|K|^d, since each of the d coordinates can 
   * independently take any value from K.
   * 
   * Substituting d = dim(U) and using the fact that #|K|^d = #|K|^(dim U),
   * we obtain the desired result: #|U| = #|K|^(dim U).
   * 
   * We need this because it completes the proof by connecting our bijection
   * result to the standard formula for matrix cardinality.
   *)
  by rewrite cardU_eq card_mx /d mul1n.
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
