From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp Require boolp.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope ring_scope.
Import GRing.Theory.

Section RoucheCapelliTheorems.

Variable R : fieldType.

Section vT_finType.

Variable K : finFieldType.
Variable vT : vectType K.
Definition v := can_type (@VectorInternalTheory.v2rK K vT).
Goal (can_type (@VectorInternalTheory.v2rK K vT)) = vT.
reflexivity.
Qed.

Check v : finType.
HB.instance Definition _ := Finite.copy vT v.
Fail Check vT : finType.
Check can_type (@VectorInternalTheory.v2rK K vT) : finType.
Check can_type (@VectorInternalTheory.v2rK K vT) : vectType K.

HB.instance Definition _ := Finite.copy vT (can_type (@VectorInternalTheory.v2rK K vT)).
Fail Check vT : finType.

Variable vt1 : vT.
Check vt1 : v : finType.
Fail Check vt1 : finType.
Let vt2 := vt1 : v .
Check vt2 : v : finType.

End vT_finType.

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

Lemma cardU_eq n (U : {vspace 'rV[K]_n}) :
  #|U| = #|'rV[K]_(\dim U)|.
Proof.
pose A' := VectorInternalTheory.vs2mx U.
pose Ar := row_base A'.
pose Ac := col_base A'.
have Ha := eq_row_base A'.
have Hd : dim 'rV[K]_n = n.
  by rewrite dim_matrix -natr1E mul1r.
pose f := fun v : 'rV[K]_(\dim U) => VectorInternalTheory.r2v (v *m Ar).
have/row_freeP [B HB] := row_base_free A'.
pose f' := fun v : 'rV[K]_n => (VectorInternalTheory.v2r v) *m B.
have Hf : injective f.
  apply (can_inj (g:=f')).
  move => v1.
  rewrite /f /f'.
  rewrite VectorInternalTheory.r2vK.
  rewrite -mulmxA.
  rewrite HB.
  by rewrite mulmx1.
rewrite -[RHS](card_codom Hf).
congr (#|_|).
rewrite /pred_of_vspace.
apply: boolp.funext => v /=.
rewrite genmxE.
apply/submxP.
case: ifPn.
  move => H.
  rewrite -/A'.
  pose fv := f' v *m pinvmx (col_base A').
  exists fv.
  rewrite /fv /f'.
  rewrite -[X in _ *m X](mulmx_base A').
  rewrite mulmxA.
  rewrite -[_ *m col_base A']mulmxA.
  rewrite mulVpmx; last by apply col_base_full.
  rewrite mulmx1.
  have HH : {in codom f & , injective f'}.
    apply (can_in_inj (g:=f)).
    move => y /codomP [x ->].
    rewrite /f' /f.
    rewrite VectorInternalTheory.r2vK.
    rewrite -[Ar]/(row_base A').
    rewrite -[x *m row_base A' *m B]mulmxA.
    by rewrite HB mulmx1.
  apply (can_inj VectorInternalTheory.r2vK).
  apply HH.
  - by rewrite VectorInternalTheory.v2rK.
  - rewrite -/(f _).
    apply map_f.
    by rewrite mem_enum.
  - rewrite /f'.
    rewrite !VectorInternalTheory.r2vK.
    rewrite -mulmxA.
    by rewrite HB mulmx1.
apply contraNnot.
case => w.
move/(f_equal VectorInternalTheory.r2v).
rewrite VectorInternalTheory.v2rK.
move ->.
rewrite /codom /=.
rewrite -/A'.
rewrite -(mulmx_base A').
rewrite mulmxA.
apply (map_f f).
by rewrite mem_enum.
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
Lemma card_vspace_fin_helper n (U : {vspace 'rV[K]_n}) :
  #|U| = (#| {:K} | ^ (\dim U))%N.
Proof.
  pose d := (\dim U).
  pose to_col (w : subvs_of U) := \col_i coord (vbasis U) i (val w).
  pose sum_cw (cw : 'cV_d) : 'rV[K]_n := \sum_i (cw i ord0 *: (vbasis U)`_i).  
  have mem_sum_cw cw : sum_cw cw \in U.
    apply: memv_suml => j _.
    by apply: memvZ; apply: (vbasis_mem (U:=U)); apply: memt_nth.
  pose from_col (cw : 'cV_d) : subvs_of U := Sub (sum_cw cw) (mem_sum_cw cw).
  have to_from : forall cw, to_col (from_col cw) = cw.
    move=> cw; apply/colP=> i; rewrite mxE.
    have -> : val (from_col cw) = sum_cw cw by [].
    by rewrite coord_sum_free ?(basis_free (vbasisP U)).
  have from_to : forall w : subvs_of U, from_col (to_col w) = w.
    move=> w; apply/val_inj.
    rewrite /from_col /sum_cw /to_col /=.
    have -> : \sum_i (to_col w) i ord0 *: (vbasis U)`_i
            = \sum_i coord (vbasis U) i (val w) *: (vbasis U)`_i.
    by apply: eq_bigr => i _; rewrite mxE.
    by rewrite (coord_vbasis (subvsP w)).
  have bij_to_col : bijective to_col.
    by apply: (Bijective from_to to_from).
  by rewrite cardU_eq card_mx /d mul1n.
Qed.

Lemma count_kernel_vectors_gaussian_elimination m n (A : 'M[K]_(m, n)) :
  #| [set x : 'rV[K]_m | x *m A == 0] | = (#| {:K} | ^ (m - \rank A))%N.
Proof.
(* Use Gaussian elimination: transform to echelon form *)
set SetAX0 := [set x : 'rV[K]_m | x *m A == 0].
pose r := \rank A.
set L := col_ebase A.
set R := row_ebase A.
set P : 'M[K]_(m, n) := pid_mx r.
(* The matrix decomposition A = L * P * R *)
have defA : A = L *m P *m R by rewrite mulmx_ebase.
(* Both L and R are invertible *)
have Urow : row_ebase A \in unitmx by apply: row_ebase_unit.
have Ucol : col_ebase A \in unitmx by apply: col_ebase_unit.

have bij_row : bijective (fun x : 'rV[K]_m => x *m col_ebase A).
  exists (fun z => z *m invmx (col_ebase A)).
    move => x.
    rewrite -mulmxA [X in _ *m X]mulmxV.
    by rewrite mulmx1.
  exact: col_ebase_unit. 
  move => z.
  rewrite -mulmxA mulVmx.
  by rewrite mulmx1.
  exact: col_ebase_unit. 
  
pose f := (fun x : 'rV[K]_m => x *m col_ebase A).
pose SetPX0 : {set 'rV[K]_m} := [set z : 'rV[K]_m | z *m P == 0].
(* "map" SetAX0 to SetPX0; "the image of set SetAX0 under function f". *)
have fSetAX0_eq_SetPX0 : f @: SetAX0 = SetPX0.
  (* Forward *)
  apply/setP=> z; rewrite !inE; apply/idP/idP.
  move/imsetP=> [x Hx ->].
  rewrite inE in Hx.                 (* turn x \in S into A *m x == 0 *)
  move/eqP: Hx => HAx0.              (* now HAx0 : A *m x = 0 *)
  apply/eqP.                         (* goal becomes an equality *)
  have H0 : (x *m A) *m invmx R = 0 by rewrite HAx0 mul0mx.
  rewrite defA in H0.
  rewrite -!mulmxA.
  rewrite -/L.
  rewrite -mulmxA in H0.
  rewrite -[X in _ *m (X)]mulmxA in H0.
  rewrite [X in _ *m (_ *m _ *m X)]mulmxV in H0; last by exact: Urow.
  rewrite mulmx1 in H0.
  exact: H0.

  (* Backward *)
  move => HzP0.
  pose x := z *m invmx L.
  have fx_eq_z : f x = z.
    rewrite /f /x -mulmxA mulVmx; last by exact: Ucol.
    by rewrite mulmx1.
  have x_in_SetAX0 : x \in SetAX0.
    rewrite inE /x defA -mulmxA -mulmxA [X in _ *m X]mulmxA.
    rewrite mulVmx; last by exact: Ucol.
    rewrite mulmxA mulmx1 mulmxA.
    move: HzP0.
    move/eqP.
    move => HzP0.
    by rewrite HzP0 mul0mx.
  apply/imsetP.
  exists x; last by exact: (esym fx_eq_z).
  exact: x_in_SetAX0.

(* Finally we alternate the set from A to P in cardinality measurance. *)
have -> : #|SetAX0| = #|SetPX0|.
  rewrite -fSetAX0_eq_SetPX0 card_imset //.
  apply: bij_inj.
  exact: bij_row.

(* Construct the vector space from P. *)
have Hd : dim 'rV[K]_m = m.
  by rewrite dim_matrix -natr1E mul1r.

pose Pcker := castmx (erefl, esym Hd) (kermx P).
pose Uker := @VectorInternalTheory.mx2vs K 'rV[K]_m m Pcker.
have memUker_bool (z : 'rV[K]_m) :
  (z \in pred_of_vspace Uker) = (z *m P == 0).
  rewrite memvE /Uker /VectorInternalTheory.mx2vs /subsetv !genmxE.
  rewrite /Pcker.

  (* Fail because (m != dim 'rV_m) before castmx *)
  Fail Check (VectorInternalTheory.v2r z <= (kermx P))%MS.
  Check (VectorInternalTheory.v2r z <= castmx (erefl, esym Hd) (kermx P))%MS.
  
  (* Because of the Fail line, we cannot prove the later castmx version
     by the simple kermx P version. Since the simple kermx P has the type issue
     prevents the submx relation holds. As a result, we need to prove the
     castmx version directly by submxP.
  *)

  (* TODO: Worth a sub-castmx lemma but dependent type looks troublesome. *)
  have ->: (VectorInternalTheory.v2r z <= castmx (erefl, esym Hd) (kermx P))%MS.
    Search submx.

    Check (VectorInternalTheory.v2r z). (* 1 x m *)
    Check castmx (erefl, esym Hd) (kermx P). (* 'M_(m, dim 'rV_m) *)
    About submx_castmx. (* m1: 1, n: m = dim 'rV_m, m2: m, e : (erefl, esym Hd)*)
    
    have Hsub := @submx_castmx 1 (dim 'rV_m) (dim 'rV_m) (VectorInternalTheory.v2r z) (castmx (esym Hd, esym Hd) (kermx P)) (erefl, erefl).
    Fail rewrite eqmx_cast.

Admitted.

(*
Lemma kernel_cardinality_rank_nullity m n (A : 'M[K]_(m, n)) :
  #| [set x : 'cV[K]_n | A *m x == 0] | = (#| {:K} | ^ (n - \rank A))%N.
Proof.
  (* Use Gaussian elimination and change of coordinates *)
  pose r := \rank A.
  set L := col_ebase A.
  set R := row_ebase A.
  set P : 'M[K]_(m, n) := pid_mx r.

  (* Matrix decomposition A = L * P * R *)
  have defA : A = L *m P *m R by rewrite mulmx_ebase.
  have UR : R \in unitmx by apply: row_ebase_unit.
  have UL : L \in unitmx by apply: col_ebase_unit.

  (* Define change of coordinates: x |-> R * x *)
  pose f := (fun x : 'cV[K]_n => R *m x).

  (* Show f is bijective *)
  have bij_f : bijective f.
    exists (fun z => invmx R *m z).
      move=> x; rewrite mulmxA mulVmx ?mul1mx //; exact: UR.
      move=> z; rewrite /f mulmxA mulmxV ?mul1mx //; exact: UR.

  (* The kernel correspondence: A*x = 0 iff P*(R*x) = 0 *)
  have ker_corr : forall x, (A *m x == 0) = (P *m (f x) == 0).
    move=> x; apply/idP/idP.
    (* Forward direction: A*x = 0 => P*(R*x) = 0 *)
    - move/eqP => HAx0; apply/eqP.
      have : invmx L *m (A *m x) = 0 by rewrite HAx0 mulmx0.
      rewrite defA -!mulmxA (mulKmx UL) !mulmxA -/f.
      by rewrite mulmxA.
    (* Backward direction: P*(R*x) = 0 => A*x = 0 *)
    - move/eqP => HPRx0; apply/eqP.
      rewrite defA -!mulmxA HPRx0 mulmx0.
      by rewrite mulmx0.

  (* Define the kernel sets *)
  set kerA := [set x : 'cV[K]_n | A *m x == 0].
  set kerP := [set z : 'cV[K]_n | P *m z == 0].

  (* Show that f maps kerA bijectively to kerP *)
  have ker_bij : f @: kerA = kerP.
    apply/setP => z; rewrite !inE; apply/idP/idP.
    - move/imsetP => [x Hx ->]; rewrite -ker_corr.
      by rewrite inE in Hx.
    - move=> Hz; exists (f^-1 z).
      + by rewrite ker_corr inE.
      + by rewrite bij_can_eq //; exact: bij_f.

  (* The kernel of P has size |K|^(n - r) *)
  have kerP_card : #|kerP| = (#|{:K}| ^ (n - r))%N.
    (* P = pid_mx r forces first r coordinates to be 0 *)
    (* The last n-r coordinates are free *)
    have -> : kerP = [set z : 'cV_n | [forall i : 'I_r, z i 0 == 0]].
      apply/setP => z; rewrite !inE; apply/idP/idP.
      - move/eqP => HPz0.
        apply/forallP => i.
        have : (P *m z) i 0 == 0 by rewrite HPz0 mxE.
        rewrite pid_mx_row -rowE mxE.
        case: (i < r)%N => //.
        by rewrite ltn_ord.
      - move/forallP => Hz0; apply/eqP/matrixP => i j.
        rewrite pid_mx_row -rowE mxE.
        case: (i < r)%N => //.
        by rewrite (Hz0 (Ordinal (ltn_ord i))) mxE.

    (* Now count the number of vectors with first r coordinates zero *)
    have free_coords : (n - r)%N + r = n by rewrite subnK //; exact: rank_leq_col.
    rewrite [X in _ = X]cardX => [|z]; last by rewrite !inE.
    rewrite -free_coords big_split_ord /=.
    rewrite [X in _ * X]cardX => [|z]; last by rewrite !inE forallP.
    by rewrite !card_ord.

  (* Apply bijection cardinality *)
  by rewrite -ker_bij card_imset //; exact: bij_f.
Qed.
*)

(*
High-level goal: count solutions x to A x = 0 over finite field K.

  Step 1
   Let r = rank(A). Use the standard ebase factorization
      A = L · P · R, where L = col_ebase A (invertible m×m),
      R = row_ebase A (invertible n×n), and
      P = pid_mx r (n×n projector onto the first r coordinates).
  This is the Gaussian elimination decomposition mulmx_ebase.

  Step 2:
    Define the change-of-coordinates map f: x ↦ R x.
    It’s a bijection because R is invertible (row_ebase_unit).
    So counting x is equivalent to counting their images z = R x.

  Step 3:
    Show f maps the kernel of A exactly to the kernel of P. Using A = L P R:
      A x = 0 iff L P R x = 0.
    Since L is invertible, this is equivalent to P (R x) = 0.
    Let z = R x; then the condition is P z = 0.
    This establishes f @: S = { z | P z = 0 } where S = { x | A x = 0 }.

  Step 4:
    Conclude |S| = |{ z | P z = 0 }| by bijection/cardinality preservation.

  Step 5:
    Count solutions to P z = 0 when P = pid_mx r.
    This projector forces the first r coordinates of z to be zero
    while leaving the remaining n − r coordinates free.
    Therefore the number of such z is |K|^(n − r).

Final result: |{ x | A x = 0 }| = |K|^(n − rank(A)).
*)
End FiniteSolutionCounting.
