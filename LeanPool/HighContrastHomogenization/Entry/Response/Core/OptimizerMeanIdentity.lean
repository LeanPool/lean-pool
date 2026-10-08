/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Response.Core.ScalarMaximizerExistence
public import LeanPool.HighContrastHomogenization.Entry.Response.Core.SkewShearCongruence

/-!
# High-contrast homogenization: Entry.Response.Core.OptimizerMeanIdentity

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The optimizer-mean identity

This file proves the optimizer-mean identity for adapted cells: the cell average of the doubled
optimizer field equals the block response mean. It develops the shear-state congruence that
carries the coarse block matrix to its skew-corrected form, the corresponding identities for the
sheared block-matrix-vector product and the block energy density, and shows the shear preserves
the admissible class of Radon measures. It also shows that multiplying a skew matrix into a vector
field produces a solenoidal field with zero normal trace, which is what lets the shear be absorbed
into the cell average without changing it.
This is the pathwise optimizer-mean identity and skew-shear congruence used in the proof of
`p.response.transfer`.
-/

section
/-!
## HC bridge I, part 3 of 4: the optimizer-mean identity, STEPs 1-3
-/

open HCPolySupport.HighContrast.CG

namespace HCPolySupport.HighContrast.Multiscale

open MeasureTheory
open scoped Matrix.Norms.L2Operator
open scoped Matrix MatrixOrder

noncomputable section

variable {d : ℕ} [NeZero d]

omit [NeZero d] in
private theorem toFullBlockMat_eq_fromBlocks (M : BlockMat d) :
    toFullBlockMat M =
      Matrix.fromBlocks M.upperLeft M.upperRight M.lowerLeft M.lowerRight := by
  ext (i | i) (j | j) <;> rfl

omit [NeZero d] in
/-- AUX (helper, NEW). Transposed-pair bilinear swap. -/
theorem vecDot_matVecMul_swap_aux {d : ℕ} (M N : Mat d) (hMN : ∀ i j, M i j = N j i)
    (x y : Vec d) : vecDot x (matVecMul M y) = vecDot y (matVecMul N x) := by
  simp only [vecDot, matVecMul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hMN j i]
  ring

omit [NeZero d] in
/-- AUX (helper, NEW). -/
theorem blockMatVecMul_blockSwap_fst {d : ℕ} (Y : BlockVec d) :
    (blockMatVecMul (blockSwap d) Y).1 = Y.2 := by
  funext i
  simp [blockMatVecMul, blockSwap, Book.Ch02.blockR, matVecMul, Matrix.one_apply]

omit [NeZero d] in
/-- AUX (helper, NEW). -/
theorem blockMatVecMul_blockSwap_snd {d : ℕ} (Y : BlockVec d) :
    (blockMatVecMul (blockSwap d) Y).2 = Y.1 := by
  funext i
  simp [blockMatVecMul, blockSwap, Book.Ch02.blockR, matVecMul, Matrix.one_apply]

/-- Pathwise (2.32) on an adapted cell, for any elliptic coefficient field `b` and any
response maximizer `u`: the cell average of the doubled optimizer field is
`x + R A(U) x`, `x = (-p, r)`, with `A(U)` the set-level coarse block matrix. -/
theorem cellAverage_optimizerField_eq_blockResponseMean (q : Mat d) (hq : IsUnit q) (t : ℤ)
    {lam Lam : ℝ} {b : CoeffField d} (hb : IsEllipticFieldOn lam Lam (HighContrast.adaptedCell q
      t) b)
    (p r : Vec d) (u : AHarmonicFunction b (HighContrast.adaptedCell q t))
    (hu : IsResponseMaximizer (HighContrast.adaptedCell q t) p r b u) :
    cellAverage (HighContrast.adaptedCell q t) (optimizerField b u) =
      blockResponseMean (coarseBlockMatrix (HighContrast.adaptedCell q t) b) (-p, r) := by
  have hset : HighContrast.adaptedCell q t =
      translateSet 0 ((matVecMul q) '' (openCubeSet (originCube d t))) := by
    rw [← Annealed.adaptedCellTranslate_eq_cg_affine q t 0]
    simp [HighContrast.adaptedCellTranslate]
  have hconv : IsOpenBoundedConvexDomain (HighContrast.adaptedCell q t) := by
    rw [hset]; exact isOpenBoundedConvexDomain_affine_openCube q hq t 0
  have hvol : 0 < (volume (HighContrast.adaptedCell q t)).toReal := by
    rw [hset]; exact volume_affine_openCube_toReal_pos q hq t 0
  have : IsFiniteMeasure (volumeMeasureOn (HighContrast.adaptedCell q t)) := by
    simpa [volumeMeasureOn] using hconv.isFiniteMeasure_restrict_volume
  have hne : (HighContrast.adaptedCell q t).Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hvol
    simp at hvol
  have hInt : ResponseLinearIntegrabilityData (HighContrast.adaptedCell q t) b :=
    ResponseLinearIntegrabilityData.of_isEllipticFieldOn hb
  have hA : IsCoarseBlockMatrix (HighContrast.adaptedCell q t) b (coarseBlockMatrix
    (HighContrast.adaptedCell q t) b) :=
    isCoarseBlockMatrix_of_isOpenBoundedConvexDomain hconv hb hvol
  have hJ : ∀ x y : Vec d, ResponseJ (HighContrast.adaptedCell q t) x y b =
      (1 / 2 : ℝ) * blockVecDot (-x, y)
        (blockMatVecMul (coarseBlockMatrix (HighContrast.adaptedCell q t) b) (-x, y)) - vecDot x
          y := fun x y =>
    responseJ_eq_block_quadratic_of_isOpenBoundedConvexDomain hconv hb hvol x y
  set A : BlockMat d := coarseBlockMatrix (HighContrast.adaptedCell q t) b with hAdef
  have hsym := hA.1
  have hURLL : ∀ i j, A.upperRight i j = A.lowerLeft j i := fun i j => hsym (Sum.inl i) (Sum.inr j)
  have hLRs : ∀ i j, A.lowerRight i j = A.lowerRight j i := fun i j => hsym (Sum.inr i) (Sum.inr j)
  have hULs : ∀ i j, A.upperLeft i j = A.upperLeft j i := fun i j => hsym (Sum.inl i) (Sum.inl j)
  have hsw : ∀ x y : Vec d, vecDot x (matVecMul A.upperRight y) =
      vecDot y (matVecMul A.lowerLeft x) := fun x y =>
    vecDot_matVecMul_swap_aux _ _ hURLL x y
  have hlr : ∀ x y : Vec d, vecDot x (matVecMul A.lowerRight y) =
      vecDot y (matVecMul A.lowerRight x) := fun x y =>
    vecDot_matVecMul_swap_aux _ _ hLRs x y
  have hul : ∀ x y : Vec d, vecDot x (matVecMul A.upperLeft y) =
      vecDot y (matVecMul A.upperLeft x) := fun x y =>
    vecDot_matVecMul_swap_aux _ _ hULs x y
  have hQ : ∀ x y : Vec d, ResponseJ (HighContrast.adaptedCell q t) x y b =
      (1 / 2 : ℝ) * (vecDot x (matVecMul A.upperLeft x) - vecDot x (matVecMul A.upperRight y)
        - vecDot y (matVecMul A.lowerLeft x) + vecDot y (matVecMul A.lowerRight y))
        - vecDot x y := by
    intro x y
    rw [hJ x y]
    simp only [blockVecDot, blockMatVecMul, vecDot_add_right, vecDot_neg_left, matVecMul_neg,
      vecDot_neg_right]
    ring
  have hgrad : ∀ i : Fin d, volumeAverage (HighContrast.adaptedCell q t) (fun x => u.toH1.grad x
    i) =
      -p i + (matVecMul A.lowerRight r) i - (matVecMul A.lowerLeft p) i := by
    intro i
    obtain ⟨ug⟩ := ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hconv hb 0
      (Pi.single i 1)
    rw [basic_cg_identities_average_gradient_coordinate_of_isResponseMaximizer
      (HighContrast.adaptedCell q t) b p r hInt u hu i
      (ug : AHarmonicFunction b (HighContrast.adaptedCell q t)) ug.isResponseMaximizer]
    have e1 : vecDot p (matVecMul A.upperRight (Pi.single i 1)) = (matVecMul A.lowerLeft p) i := by
      rw [hsw p (Pi.single i 1), vecDot_single_left]
    have e3 : vecDot r (matVecMul A.lowerRight (Pi.single i 1)) = (matVecMul A.lowerRight r) i := by
      rw [hlr r (Pi.single i 1), vecDot_single_left]
    have e4 : vecDot (Pi.single i 1) (matVecMul A.lowerLeft p) = (matVecMul A.lowerLeft p) i :=
      vecDot_single_left _ _
    have e2 : vecDot (Pi.single i 1) (matVecMul A.lowerRight r) = (matVecMul A.lowerRight r) i :=
      vecDot_single_left _ _
    have e5 : vecDot p (Pi.single i 1) = p i := vecDot_single_right _ _
    rw [hQ p r, hQ 0 (Pi.single i 1), hQ p (r - Pi.single i 1)]
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right, vecDot_add_left,
      vecDot_neg_right, vecDot_neg_left, matVecMul_zero, vecDot_zero_left, vecDot_zero_right]
    linarith only [e1, e2, e3, e4, e5]
  have hflux : ∀ i : Fin d, volumeAverage (HighContrast.adaptedCell q t) (fun x => matVecMul (b
    x) (u.toH1.grad x) i) =
      r i + (matVecMul A.upperRight r) i - (matVecMul A.upperLeft p) i := by
    intro i
    obtain ⟨uf⟩ := ScalarCanonicalMaximizer.nonempty_of_isOpenBoundedConvexDomain hne hconv hb
      (Pi.single i 1) 0
    rw [basic_cg_identities_average_flux_coordinate_of_isResponseMaximizer
      (HighContrast.adaptedCell q t) b p r hInt u hu i
      (uf : AHarmonicFunction b (HighContrast.adaptedCell q t)) uf.isResponseMaximizer]
    have f1 : vecDot p (matVecMul A.upperLeft (Pi.single i 1)) = (matVecMul A.upperLeft p) i := by
      rw [hul p (Pi.single i 1), vecDot_single_left]
    have f2 : vecDot (Pi.single i 1) (matVecMul A.upperLeft p) = (matVecMul A.upperLeft p) i :=
      vecDot_single_left _ _
    have f3 : vecDot (Pi.single i 1) (matVecMul A.upperRight r) = (matVecMul A.upperRight r) i :=
      vecDot_single_left _ _
    have f4 : vecDot r (matVecMul A.lowerLeft (Pi.single i 1)) = (matVecMul A.upperRight r) i := by
      rw [← hsw (Pi.single i 1) r, vecDot_single_left]
    have f5 : vecDot (Pi.single i 1) r = r i := vecDot_single_left _ _
    rw [hQ (p - Pi.single i 1) r, hQ p r, hQ (Pi.single i 1) 0]
    simp only [sub_eq_add_neg, matVecMul_add, matVecMul_neg, vecDot_add_right, vecDot_add_left,
      vecDot_neg_right, vecDot_neg_left, matVecMul_zero, vecDot_zero_left, vecDot_zero_right]
    linarith only [f1, f2, f3, f4, f5]
  have hrhs1 : (blockResponseMean A (-p, r)).1 =
      fun i => -p i + (matVecMul A.lowerRight r) i - (matVecMul A.lowerLeft p) i := by
    funext i
    simp only [blockResponseMean, Prod.fst_add, blockMatVecMul_blockSwap_fst]
    simp [blockMatVecMul, matVecMul_neg]
    ring
  have hrhs2 : (blockResponseMean A (-p, r)).2 =
      fun i => r i + (matVecMul A.upperRight r) i - (matVecMul A.upperLeft p) i := by
    funext i
    simp only [blockResponseMean, Prod.snd_add, blockMatVecMul_blockSwap_snd]
    simp [blockMatVecMul, matVecMul_neg]
    ring
  refine Prod.ext ?_ ?_
  · rw [hrhs1]; funext i; exact hgrad i
  · rw [hrhs2]; funext i; exact hflux i

omit [NeZero d] in
private theorem ofFullBlockMat_fromBlocks (A B C D : Mat d) :
    ofFullBlockMat (Matrix.fromBlocks A B C D) = ⟨A, B, C, D⟩ := rfl

omit [NeZero d] in
theorem blockCongr_shear (c : Mat d) (B : BlockMat d) :
    blockCongr ⟨1, 0, c, 1⟩ B =
      ⟨B.upperLeft + matTranspose c * B.lowerLeft + B.upperRight * c
          + matTranspose c * B.lowerRight * c,
       B.upperRight + matTranspose c * B.lowerRight,
       B.lowerLeft + B.lowerRight * c,
       B.lowerRight⟩ := by
  rw [blockCongr, toFullBlockMat_eq_fromBlocks (⟨1, 0, c, 1⟩ : BlockMat d),
    toFullBlockMat_eq_fromBlocks B]
  rw [Matrix.fromBlocks_transpose, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [matTranspose, Matrix.transpose_one, Matrix.transpose_zero, one_mul, mul_one,
    zero_mul, mul_zero, zero_add]
  rw [ofFullBlockMat_fromBlocks]
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> noncomm_ring

/-! ### STEP 1: the pointwise matrix identity -/

omit [NeZero d] in
private theorem blockMatrixOfCoeff_eq (A : Mat d) :
    blockMatrixOfCoeff A =
      ⟨symmPart A + matTranspose (skewPart A) * (symmPart A)⁻¹ * skewPart A,
       -(matTranspose (skewPart A) * (symmPart A)⁻¹),
       -((symmPart A)⁻¹ * skewPart A),
       (symmPart A)⁻¹⟩ :=
  rfl

omit [NeZero d] in
private theorem entry_of_skew {g : Mat d} (hg : matTranspose g = -g) (i j : Fin d) :
    g j i = -(g i j) := by
  have := congrArg (fun M : Mat d => M i j) hg
  simpa [matTranspose, Matrix.transpose_apply] using this

omit [NeZero d] in
theorem symmPart_sub_skew {g : Mat d} (hg : matTranspose g = -g) (A : Mat d) :
    symmPart (A - g) = symmPart A := by
  ext i j
  have h1 : g j i = -(g i j) := entry_of_skew hg i j
  simp only [symmPart, Matrix.sub_apply, h1]
  ring

omit [NeZero d] in
theorem skewPart_sub_skew {g : Mat d} (hg : matTranspose g = -g) (A : Mat d) :
    skewPart (A - g) = skewPart A - g := by
  ext i j
  have h1 : g j i = -(g i j) := entry_of_skew hg i j
  simp only [skewPart, Matrix.sub_apply, h1]
  ring

omit [NeZero d] in
/-- STEP 1. Subtracting a constant skew matrix from the coefficient is the shear congruence
of the pointwise block matrix. -/
theorem blockMatrixOfCoeff_sub_skew {g : Mat d} (hg : matTranspose g = -g) (A : Mat d) :
    blockMatrixOfCoeff (A - g) = blockCongr ⟨1, 0, g, 1⟩ (blockMatrixOfCoeff A) := by
  have hgT : (g : Mat d)ᵀ = -g := hg
  have hkT : matTranspose (skewPart A - g) = matTranspose (skewPart A) + g := by
    change (skewPart A - g)ᵀ = (skewPart A)ᵀ + g
    rw [Matrix.transpose_sub, hgT, sub_neg_eq_add]
  rw [blockMatrixOfCoeff_eq, blockMatrixOfCoeff_eq, blockCongr_shear,
    symmPart_sub_skew hg, skewPart_sub_skew hg, hkT]
  simp only [hg]
  refine blockMat_ext ?_ ?_ ?_ ?_ <;> noncomm_ring

/-! ### STEP 2: the analytic input -/

omit [NeZero d] in
/-- `L²` closure under a constant matrix. -/
theorem memVectorL2_matVecMul_const {U : Set (Vec d)} (g : Mat d) {w : Vec d → Vec d}
    (hw : MemVectorL2 U w) : MemVectorL2 U (fun x => matVecMul g (w x)) := by
  simpa using! (matContinuousLinearMap g).comp_memLp' hw

omit [NeZero d] in
/-- The `L²` pairing against a fixed `L²` scalar is continuous along `L²`-convergent
sequences. -/
private theorem tendsto_integral_mul_of_tendsto_eLpNorm
    {U : Set (Vec d)} {f : Vec d → ℝ} (hf : MemScalarL2 U f)
    {F : ℕ → Vec d → ℝ} {G : Vec d → ℝ}
    (hF : ∀ n, MemScalarL2 U (F n)) (hG : MemScalarL2 U G)
    (hconv : Filter.Tendsto
      (fun n => MeasureTheory.eLpNorm (fun x => F n x - G x) 2
        (MeasureTheory.volume.restrict U))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => ∫ x in U, f x * F n x ∂MeasureTheory.volume)
      Filter.atTop (nhds (∫ x in U, f x * G x ∂MeasureTheory.volume)) := by
  classical
  have hf_int :
      MeasureTheory.Integrable (fun x => f x * G x)
        (MeasureTheory.volume.restrict U) := hf.integrable_mul hG
  have hFn_int :
      ∀ᶠ n in Filter.atTop,
        MeasureTheory.Integrable (fun x => f x * F n x)
          (MeasureTheory.volume.restrict U) :=
    Filter.Eventually.of_forall fun n => hf.integrable_mul (hF n)
  have hbound : ∀ n,
      MeasureTheory.eLpNorm (fun x => f x * (F n x - G x)) 1
          (MeasureTheory.volume.restrict U) ≤
        1 * MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict U) *
          MeasureTheory.eLpNorm (fun x => F n x - G x) 2
            (MeasureTheory.volume.restrict U) := by
    intro n
    exact MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
      (μ := MeasureTheory.volume.restrict U)
      (p := (2 : ENNReal)) (q := (2 : ENNReal)) (r := (1 : ENNReal))
      (fun a b : ℝ => a * b) 1 continuous_mul
      hf.aestronglyMeasurable ((hF n).sub hG).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simp)
  have hne : MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict U) ≠ ⊤ :=
    hf.eLpNorm_lt_top.ne
  have hscaled :
      Filter.Tendsto
        (fun n =>
          1 * MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict U) *
            MeasureTheory.eLpNorm (fun x => F n x - G x) 2
              (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0) := by
    have h :=
      ENNReal.Tendsto.const_mul
        (a := 1 * MeasureTheory.eLpNorm f 2 (MeasureTheory.volume.restrict U))
        hconv (Or.inr (by simpa using hne))
    simpa using h
  have hL1 :
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm (fun x => f x * (F n x - G x)) 1
          (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hscaled
      (fun _ => zero_le) hbound
  have hL1' :
      Filter.Tendsto
        (fun n => MeasureTheory.eLpNorm
          ((fun x => f x * F n x) - fun x => f x * G x) 1
          (MeasureTheory.volume.restrict U))
        Filter.atTop (nhds 0) := by
    refine hL1.congr fun n => ?_
    congr 1
    funext x
    simp [mul_sub]
  exact MeasureTheory.tendsto_integral_of_L1'
    (μ := MeasureTheory.volume.restrict U) (fun x => f x * G x)
    hFn_int hL1'

omit [NeZero d] in
/-- Coordinate expansion of the `L²` pairing of a matrix-transformed field with a gradient. -/
private theorem integral_vecDot_matVecMul_eq_sum
    {U : Set (Vec d)} (g : Mat d) (φ : H1Function U) {v : Vec d → Vec d}
    (hv : MemVectorL2 U v) :
    ∫ x in U, vecDot (matVecMul g (v x)) (φ.grad x) ∂MeasureTheory.volume
      = ∑ i, ∑ j, g i j *
          ∫ x in U, φ.grad x i * v x j ∂MeasureTheory.volume := by
  classical
  have hvj : ∀ j : Fin d, MemScalarL2 U (fun x => v x j) := fun j =>
    CorrectionFieldData.memScalarL2_coord_of_memVectorL2 hv j
  have hint : ∀ i j : Fin d,
      MeasureTheory.Integrable (fun x => g i j * (φ.grad x i * v x j))
        (MeasureTheory.volume.restrict U) := by
    intro i j
    exact ((φ.gradMemL2 i).integrable_mul (hvj j)).const_mul _
  have hpt : ∀ x : Vec d,
      vecDot (matVecMul g (v x)) (φ.grad x)
        = ∑ i, ∑ j, g i j * (φ.grad x i * v x j) := by
    intro x
    have h1 : vecDot (matVecMul g (v x)) (φ.grad x)
        = ∑ i, (∑ j, g i j * v x j) * φ.grad x i := rfl
    rw [h1]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [show (fun x => vecDot (matVecMul g (v x)) (φ.grad x))
        = fun x => ∑ i, ∑ j, g i j * (φ.grad x i * v x j) from funext hpt]
  rw [MeasureTheory.integral_finsetSum _
    (fun i _ => MeasureTheory.integrable_finsetSum _ (fun j _ => hint i j))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MeasureTheory.integral_finsetSum _ (fun j _ => hint i j)]
  exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _

omit [NeZero d] in
/-- Symmetry of the mixed pairing of an `H¹` gradient with the derivatives of a smooth
compactly supported test function. -/
private theorem integral_grad_mul_coordDeriv_comm
    {U : Set (Vec d)} (φ : H1Function U) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) (i j : Fin d) :
    ∫ x in U, φ.grad x i * euclideanCoordDeriv j ψ x ∂MeasureTheory.volume
      = ∫ x in U, φ.grad x j * euclideanCoordDeriv i ψ x ∂MeasureTheory.volume := by
  have key : ∀ a b : Fin d,
      ∫ x in U, φ.grad x a * euclideanCoordDeriv b ψ x ∂MeasureTheory.volume
        = -∫ x in U, φ.toFun x * euclideanCoordSecondDeriv b a ψ x
            ∂MeasureTheory.volume := by
    intro a b
    have h : ∫ x in U, φ.toFun x * euclideanCoordSecondDeriv b a ψ x
          ∂MeasureTheory.volume
        = -∫ x in U, φ.grad x a * euclideanCoordDeriv b ψ x ∂MeasureTheory.volume :=
      φ.hasWeakGradient a (euclideanCoordDeriv b ψ)
        (contDiff_euclideanCoordDeriv hψ b)
        (hasCompactSupport_euclideanCoordDeriv hψc b)
        ((tsupport_euclideanCoordDeriv_subset_tsupport b ψ).trans hψU)
    linarith only [h]
  rw [key i j, key j i]
  congr 1
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  change φ.toFun x * euclideanCoordSecondDeriv j i ψ x
      = φ.toFun x * euclideanCoordSecondDeriv i j ψ x
  rw [euclideanCoordSecondDeriv_comm hψ j i x]

omit [NeZero d] in
/-- The smooth case: a constant skew matrix applied to the gradient of a smooth compactly
supported test is `L²`-orthogonal to every `H¹` gradient. -/
private theorem integral_vecDot_matVecMul_skew_smooth_eq_zero
    {U : Set (Vec d)} {g : Mat d} (hg : matTranspose g = -g) (φ : H1Function U)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψU : tsupport ψ ⊆ U) :
    ∫ x in U, vecDot (matVecMul g (euclideanGradient ψ x)) (φ.grad x)
      ∂MeasureTheory.volume = 0 := by
  classical
  have hv : MemVectorL2 U (euclideanGradient ψ) :=
    memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport hψ hψc
  rw [integral_vecDot_matVecMul_eq_sum g φ hv]
  have hsym : ∀ i j : Fin d,
      (∫ x in U, φ.grad x i * euclideanGradient ψ x j ∂MeasureTheory.volume)
        = ∫ x in U, φ.grad x j * euclideanGradient ψ x i ∂MeasureTheory.volume :=
    fun i j => integral_grad_mul_coordDeriv_comm φ hψ hψc hψU i j
  set S : Fin d → Fin d → ℝ :=
    fun i j => ∫ x in U, φ.grad x i * euclideanGradient ψ x j ∂MeasureTheory.volume
      with hSdef
  have hneg : ∑ i, ∑ j, g i j * S i j = -∑ i, ∑ j, g i j * S i j := by
    calc ∑ i, ∑ j, g i j * S i j
        = ∑ j, ∑ i, g i j * S i j := Finset.sum_comm
      _ = ∑ i, ∑ j, g j i * S j i := rfl
      _ = ∑ i, ∑ j, -(g i j * S i j) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          rw [entry_of_skew hg i j, hSdef]
          simp only []
          rw [hsym j i, neg_mul]
      _ = ∑ i, -∑ j, g i j * S i j := by
          exact Finset.sum_congr rfl fun i _ => Finset.sum_neg_distrib _
      _ = -∑ i, ∑ j, g i j * S i j := Finset.sum_neg_distrib _
  linarith only [hneg]

/-- `g ∇u` is divergence free with vanishing normal
trace whenever `g` is a constant skew matrix and `u ∈ H¹₀(U)`.  For `u ∈ C_c^∞(U)` and any
`φ ∈ H¹(U)` one has `∫_U g ∇u · ∇φ = -∫_U (Σ_{i,j} g_{ij} ∂_i∂_j u) φ = 0` because the Hessian
is symmetric and `g` is skew; the general `u ∈ H¹₀(U)` follows by density.
This is needed for the admissible-class shear of STEP 3 (the flux correction of a sheared
state acquires the term `g·(X.potential − P.1)`, which must itself be solenoidal with zero
normal trace), and it is the ONLY genuinely analytic input of the admissible-class shear:
every other step is matrix algebra, `sInf` congruence, or linearity of the integral. -/
theorem isSolenoidalZeroNormalTraceOn_matVecMul_of_skew {d : ℕ} {U : Set (Vec d)}
    {g : Mat d} (hg : matTranspose g = -g) {w : Vec d → Vec d}
    (hw : IsPotentialZeroTraceOn U w) :
    IsSolenoidalZeroNormalTraceOn U (fun x => matVecMul g (w x)) := by
  classical
  obtain ⟨u, rfl⟩ := hw
  intro φ
  have hDmem : ∀ n : ℕ, MemVectorL2 U (euclideanGradient (u.approx n)) := fun n =>
    memVectorL2_euclideanGradient_of_contDiff_hasCompactSupport
      (u.approx_smooth n) (u.approx_hasCompactSupport n)
  have hzero : ∀ n : ℕ,
      ∫ x in U, vecDot (matVecMul g (euclideanGradient (u.approx n) x)) (φ.grad x)
        ∂MeasureTheory.volume = 0 := fun n =>
    integral_vecDot_matVecMul_skew_smooth_eq_zero hg φ (u.approx_smooth n)
      (u.approx_hasCompactSupport n) (u.approx_support_subset n)
  have hcoord : ∀ i j : Fin d,
      Filter.Tendsto
        (fun n => ∫ x in U, φ.grad x i * euclideanGradient (u.approx n) x j
          ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∫ x in U, φ.grad x i * u.toH1Function.grad x j
          ∂MeasureTheory.volume)) := by
    intro i j
    refine tendsto_integral_mul_of_tendsto_eLpNorm (φ.gradMemL2 i)
      (fun n => CorrectionFieldData.memScalarL2_coord_of_memVectorL2 (hDmem n) j)
      (u.toH1Function.gradMemL2 j) ?_
    exact u.tendsto_approx_grad j
  have hsum :
      Filter.Tendsto
        (fun n => ∑ i, ∑ j, g i j *
          ∫ x in U, φ.grad x i * euclideanGradient (u.approx n) x j
            ∂MeasureTheory.volume)
        Filter.atTop
        (nhds (∑ i, ∑ j, g i j *
          ∫ x in U, φ.grad x i * u.toH1Function.grad x j ∂MeasureTheory.volume)) :=
    tendsto_finsetSum _ fun i _ =>
      tendsto_finsetSum _ fun j _ => (hcoord i j).const_mul _
  have hsum0 :
      Filter.Tendsto (fun _ : ℕ => (0 : ℝ)) Filter.atTop
        (nhds (∑ i, ∑ j, g i j *
          ∫ x in U, φ.grad x i * u.toH1Function.grad x j ∂MeasureTheory.volume)) := by
    refine hsum.congr fun n => ?_
    rw [← integral_vecDot_matVecMul_eq_sum g φ (hDmem n)]
    exact hzero n
  have hgoal :
      ∫ x in U, vecDot (matVecMul g (u.toH1Function.grad x)) (φ.grad x)
          ∂MeasureTheory.volume
        = ∑ i, ∑ j, g i j *
            ∫ x in U, φ.grad x i * u.toH1Function.grad x j ∂MeasureTheory.volume :=
    integral_vecDot_matVecMul_eq_sum g φ
      (MeasureTheory.MemLp.of_eval fun j => u.toH1Function.gradMemL2 j)
  rw [hgoal]
  exact tendsto_nhds_unique hsum0 tendsto_const_nhds

omit [NeZero d] in
/-! ### STEP 3: the admissible-class shear -/

omit [NeZero d] in
private theorem one_matVecMul_eq (x : Vec d) : matVecMul (1 : Mat d) x = x := by
  change (1 : Mat d).mulVec x = x
  exact Matrix.one_mulVec x

omit [NeZero d] in
private theorem zero_matVecMul_eq (x : Vec d) : matVecMul (0 : Mat d) x = 0 := by
  change (0 : Mat d).mulVec x = 0
  exact Matrix.zero_mulVec x

omit [NeZero d] in
theorem blockMatVecMul_shear (g : Mat d) (P : BlockVec d) :
    blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) P = (P.1, matVecMul g P.1 + P.2) := by
  rcases P with ⟨p, q⟩
  simp [blockMatVecMul, one_matVecMul_eq, zero_matVecMul_eq]

omit [NeZero d] in
theorem blockMatVecMul_shear_neg (g : Mat d) (P : BlockVec d) :
    blockMatVecMul (⟨1, 0, -g, 1⟩ : BlockMat d) (blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) P)
      = P := by
  rw [blockMatVecMul_shear, blockMatVecMul_shear]
  refine Prod.ext rfl ?_
  simp [neg_matVecMul]

/-- The state shear: the potential slot is untouched, the flux acquires `g · potential`. -/
@[expose]
def shearState (g : Mat d) (X : BlockState d) : BlockState d :=
  { potential := X.potential
    flux := fun x => matVecMul g (X.potential x) + X.flux x }

omit [NeZero d] in
@[simp] theorem shearState_eval (g : Mat d) (X : BlockState d) (x : Vec d) :
    (shearState g X).eval x = blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) (X.eval x) := by
  rw [blockMatVecMul_shear]
  rfl

omit [NeZero d] in
theorem shearState_neg_shearState (g : Mat d) (X : BlockState d) :
    shearState (-g) (shearState g X) = X := by
  refine BlockState.ext rfl ?_
  funext x
  simp [shearState, neg_matVecMul]

omit [NeZero d] in
/-- STEP 1, transported to the energy density. -/
theorem blockEnergyDensity_sub_skew {g : Mat d} (hg : matTranspose g = -g)
    (a : CoeffField d) (X : BlockState d) (x : Vec d) :
    blockEnergyDensity (fun y => a y - g) X x = blockEnergyDensity a (shearState g X) x := by
  unfold blockEnergyDensity blockCoeffField
  rw [shearState_eval]
  congr 1
  rw [show (fun y => a y - g) x = a x - g from rfl, blockMatrixOfCoeff_sub_skew hg,
    blockVecDot_blockCongr]

omit [NeZero d] in
theorem isBlockMuAdmissible_shearState {g : Mat d} (hg : matTranspose g = -g)
    {U : Set (Vec d)} {P : BlockVec d} {X : BlockState d} (hX : IsBlockMuAdmissible U P X) :
    IsBlockMuAdmissible U (blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) P) (shearState g X) := by
  obtain ⟨hpL2, hpot, hfL2, hsol⟩ := hX
  have hfluxeq :
      (fun x => (shearState g X).flux x -
          (blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) P).2)
        = (fun x => matVecMul g (X.potential x - P.1)) + (fun x => X.flux x - P.2) := by
    funext x
    rw [blockMatVecMul_shear]
    simp only [shearState, Pi.add_apply, sub_eq_add_neg, matVecMul_add, matVecMul_neg]
    abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [blockMatVecMul_shear]
    exact hpL2
  · rw [blockMatVecMul_shear]
    exact hpot
  · rw [hfluxeq]
    exact (memVectorL2_matVecMul_const g hpL2).add hfL2
  · rw [hfluxeq]
    exact isSolenoidalZeroNormalTraceOn_add_of_memVectorL2
      (memVectorL2_matVecMul_const g hpL2) hfL2
      (isSolenoidalZeroNormalTraceOn_matVecMul_of_skew hg hpot) hsol

omit [NeZero d] in
private theorem matTranspose_neg_skew {g : Mat d} (hg : matTranspose g = -g) :
    matTranspose (-g) = -(-g) := by
  change (-g : Mat d)ᵀ = -(-g)
  rw [Matrix.transpose_neg]
  exact congrArg Neg.neg hg

omit [NeZero d] in
/-- STEP 3. The shear bijection on admissible states identifies the two `mu`-value sets. -/
theorem muValueSet_sub_skew {g : Mat d} (hg : matTranspose g = -g) (U : Set (Vec d))
    (P : BlockVec d) (a : CoeffField d) :
    muValueSet U P (fun x => a x - g)
      = muValueSet U (blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) P) a := by
  have hgn : matTranspose (-g) = -(-g) := matTranspose_neg_skew hg
  ext m
  constructor
  · rintro ⟨X, hX, rfl⟩
    refine ⟨shearState g X, isBlockMuAdmissible_shearState hg hX, ?_⟩
    exact congrArg (volumeAverage U) (funext fun x => blockEnergyDensity_sub_skew hg a X x)
  · rintro ⟨Y, hY, rfl⟩
    refine ⟨shearState (-g) Y, ?_, ?_⟩
    · have h := isBlockMuAdmissible_shearState hgn hY
      rwa [blockMatVecMul_shear_neg] at h
    · have hY' : shearState g (shearState (-g) Y) = Y := by
        have := shearState_neg_shearState (-g) Y
        rwa [neg_neg] at this
      calc volumeAverage U (blockEnergyDensity a Y)
          = volumeAverage U (blockEnergyDensity a (shearState g (shearState (-g) Y))) := by
            rw [hY']
        _ = volumeAverage U (blockEnergyDensity (fun x => a x - g) (shearState (-g) Y)) :=
            congrArg (volumeAverage U)
              (funext fun x =>
                (blockEnergyDensity_sub_skew hg a (shearState (-g) Y) x).symm)

omit [NeZero d] in
/-- STEP 3, conclusion: the shear identity for `Mu`. -/
theorem Mu_sub_skew {g : Mat d} (hg : matTranspose g = -g) (U : Set (Vec d))
    (P : BlockVec d) (a : CoeffField d) :
    Mu U P (fun x => a x - g) = Mu U (blockMatVecMul (⟨1, 0, g, 1⟩ : BlockMat d) P) a := by
  unfold Mu
  rw [muValueSet_sub_skew hg]

/-! ### STEP 4: the block-level shear -/

end

end HCPolySupport.HighContrast.Multiscale
end
