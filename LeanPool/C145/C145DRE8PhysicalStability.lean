/-
Copyright (c) 2026 Mark Gladden. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mark Gladden
-/
module

public import LeanPool.C145.C145DRE8PositiveGridKernel
public import LeanPool.C145.C145DRE8HilbertStability
public import LeanPool.C145.C145DRE8ActualFrame
public import LeanPool.C145.C145DRE8OrthogonalTransport

/-! Theorem E uses Lemma B on the full actual physical secant, without H2 equality.
The modal and vertex slices are related by the same calibrated orthogonal frame. -/

@[expose] public section

noncomputable section
namespace C145DRE8
open scoped BigOperators
open C145.H2
variable {n : ℕ} {ρ : Type*} [Fintype ρ]

/-- Full actual physical secant estimate. No equality of second-transfer data
is assumed. All source signatures may be used jointly. -/
theorem actual_full_physical_slice_rigidity
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c)
    (g : ρ → Fin (n + 1) → ℝ) (delta : ℝ)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤
      signatureSq (fun r => (Matrix.of U).mulVec (g r)) j k) :
    delta ^ 2 * tensorSq (C145PhysicalFrame.C V-C145PhysicalFrame.C U) ≤
      ((n + 1 : ℕ) + 2 : ℝ) * sliceSq (C145PhysicalFrame.C V-C145PhysicalFrame.C U) g := by
  let Q : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ := Matrix.of U * (Matrix.of V).transpose
  have hQ : Q.transpose * Q = 1 := by
    have hh := columnOrthonormal_matrix (C145CoordinatePermutation.transport V U)
      (C145CoordinatePermutation.transport_columnOrthonormal V U hV hU)
    rw [C145CoordinatePermutation.transport_eq_matrix_mul_transpose] at hh
    exact hh
  have hunit : ∀ i, ∑ v, Q i v = 1 := actual_frame_common_unit U V c hU hV hGU hGV
  have hh := physical_slice_rigidity Q hQ hunit
    (fun r => (Matrix.of U).mulVec (g r)) delta hsep
  rw [actual_frame_physical_difference U V hU,
    tensorSq_rotateTensor (Matrix.of U) (columnOrthonormal_matrix U hU)] at hh
  simpa only [sliceSq, matrixSq_slice_rotateTensor (Matrix.of U)
    (columnOrthonormal_matrix U hU), Fintype.card_fin] using hh


/-- The fixed signed-ground calibration removes every slot containing mode zero.
This is the source space V0; projection and its singular value are taken here. -/
def physicalDifferenceSpace (n : ℕ) : Submodule ℝ (TensorSpace (n + 1)) where
  carrier := {E | FullSymTensor (toTensor E) ∧
    ∀ i j k, i = 0 ∨ j = 0 ∨ k = 0 → toTensor E i j k = 0}
  zero_mem' := by
    constructor
    · intro e a; rfl
    · intro i j k h; rfl
  add_mem' := by
    intro E F hE hF
    constructor
    · intro e a
      exact congrArg₂ (· + ·) (hE.1 e a) (hF.1 e a)
    · intro i j k h
      change toTensor E i j k + toTensor F i j k = 0
      rw [hE.2 i j k h, hF.2 i j k h, add_zero]
  smul_mem' := by
    intro a E hE
    constructor
    · intro e v
      exact congrArg (fun t : ℝ => a * t) (hE.1 e v)
    · intro i j k h
      change a * toTensor E i j k = 0
      rw [hE.2 i j k h, mul_zero]

/-- Actual secants lie in V0 solely from orthonormality and common signed ground. -/
theorem actual_difference_mem_physicalDifferenceSpace
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c) :
    fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U) ∈ physicalDifferenceSpace n := by
  constructor
  · rw [toTensor_fromTensor]
    exact fullSymTensor_sub _ _ (actual_cubic_fullSym V) (actual_cubic_fullSym U)
  · intro i j k h
    rw [toTensor_fromTensor]
    exact sub_eq_zero.mpr (actual_cubic_common_ground U V c hU hV hGU hGV i j k h)

/-- All signature slices in a single Euclidean vector, with Frobenius matrix norms. -/
def sliceBundle {N : ℕ} (g : ρ → Fin N → ℝ) :
    TensorSpace N →ₗ[ℝ] EuclideanSpace ℝ (ρ × Fin N × Fin N) where
  toFun E := WithLp.toLp 2 (fun p => tensorSlice (toTensor E) (g p.1) p.2.1 p.2.2)
  map_add' := by
    intro E F
    ext p
    simp [tensorSlice, toTensor, mul_add, Finset.sum_add_distrib]
  map_smul' := by
    intro a E
    ext p
    simp [tensorSlice, toTensor, Finset.mul_sum, mul_left_comm]

/-- The bundle norm is exactly the source sum of squared Frobenius slice norms. -/
theorem norm_sliceBundle_sq {N : ℕ} (g : ρ → Fin N → ℝ) (E : TensorSpace N) :
    ‖sliceBundle g E‖ ^ 2 = sliceSq (toTensor E) g := by
  simp [EuclideanSpace.real_norm_sq_eq, sliceBundle, sliceSq, matrixSq,
    Fintype.sum_prod_type]

/-- Source B_H uses Euclidean norms on the signatures in modal coordinates. -/
def signatureNorm (g : ρ → Fin (n + 1) → ℝ) : ℝ :=
  Real.sqrt (∑ r, ∑ i, (g r i) ^ 2)

/-- Orthogonal modal transport preserves B_H, so this is also the norm of
exactly the vertex signature family appearing in separation. -/
theorem signatureNorm_rotate
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hU : U.transpose * U = 1)
    (g : ρ → Fin (n + 1) → ℝ) :
    signatureNorm (fun r => U.mulVec (g r)) = signatureNorm g := by
  unfold signatureNorm
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  exact orthogonal_energy U hU (g r)

/-- Cauchy--Schwarz gives the global slice estimate on every ambient tensor;
no physicality is assumed for any projected component. -/
theorem sliceBundle_global_bound (g : ρ → Fin (n + 1) → ℝ) (E : TensorSpace (n + 1)) :
    ‖sliceBundle g E‖ ≤ signatureNorm g * ‖E‖ := by
  have hh : sliceSq (toTensor E) g ≤ (∑ r, ∑ i, (g r i) ^ 2) * tensorSq (toTensor E) := by
    calc
      _ ≤ ∑ r, (∑ i, (g r i) ^ 2) * tensorSq (toTensor E) := by
        apply Finset.sum_le_sum
        intro r hr
        exact tensorSlice_cauchy (toTensor E) (g r)
      _ = _ := by rw [Finset.sum_mul]
  have hnon : (0 : ℝ) ≤ ∑ r, ∑ i, (g r i) ^ 2 := by positivity
  have hs := Real.sq_sqrt hnon
  have hE := norm_sq_eq_tensorSq E
  have hS := norm_sliceBundle_sq g E
  have hB : 0 ≤ signatureNorm g := Real.sqrt_nonneg _
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg hB (norm_nonneg _))).mp
  simpa only [mul_pow, signatureNorm, hs, hE, hS] using hh

/-- Lemma B in precisely the Euclidean/Frobenius norm used for Theorem E. -/
theorem actual_full_physical_norm_bound
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c)
    (g : ρ → Fin (n + 1) → ℝ) (delta : ℝ) (hd : 0 < delta)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤
      signatureSq (fun r => (Matrix.of U).mulVec (g r)) j k) :
    ‖fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U)‖ ≤
      (Real.sqrt ((n + 1 : ℕ) + 2) / delta)*
        ‖sliceBundle g (fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U))‖ := by
  let E := fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U)
  have hr := actual_full_physical_slice_rigidity U V c hU hV hGU hGV g delta hsep
  have hE := norm_sq_eq_tensorSq E
  have hS := norm_sliceBundle_sq g E
  simp only [E, toTensor_fromTensor] at hE hS
  have hN : (0 : ℝ) ≤ ((n + 1 : ℕ) + 2 : ℝ) := by positivity
  have hs := Real.sq_sqrt hN
  have hn : 0 ≤ Real.sqrt ((n + 1 : ℕ) + 2) := Real.sqrt_nonneg _
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hd).mpr
  apply (sq_le_sq₀ (mul_nonneg (norm_nonneg _) hd.le)
    (mul_nonneg hn (norm_nonneg _))).mp
  rw [mul_pow, mul_pow, hs]
  nlinarith only [hr, hE, hS]


/-- The exact sampled operator on the source V0, with its inherited Frobenius norm. -/
def physicalGridMap (a rates : Fin (n + 1) → ℝ)
    (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ) :=
  (positiveGridMap a rates sNodes tNodes).comp (physicalDifferenceSpace n).subtype

/-- The full actual positive-response kernel inside V0. -/
def physicalH2Kernel (a rates : Fin (n + 1) → ℝ) :=
  (actualPositiveKernel a rates).comap (physicalDifferenceSpace n).subtype

/-- The bundle is restricted to the same V0 as the orthogonal projection. -/
def physicalSliceBundle (g : ρ → Fin (n + 1) → ℝ) :=
  (sliceBundle g).comp (physicalDifferenceSpace n).subtype

/-- Source Lemma D, now with the exact domain used by source Theorem E. -/
theorem ker_physicalGridMap (a rates : Fin (n + 1) → ℝ)
    (hRates : ∀ i, 0 < rates i) (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (hsPos : ∀ i, 0 < sNodes i) (htPos : ∀ i, 0 < tNodes i) :
    LinearMap.ker (physicalGridMap a rates sNodes tNodes) = physicalH2Kernel a rates := by
  exact ker_positiveGridMap_restrict (by omega) a rates hRates sNodes tNodes
    hsNodes htNodes hsPos htPos (physicalDifferenceSpace n)

/-- A positive measurement lower gain exists on K-perp *inside V0*.
For nontrivial K-perp the Hilbert engine also proves that its least value is attained. -/
theorem physicalGrid_exists_positive_gain (a rates : Fin (n + 1) → ℝ)
    (hRates : ∀ i, 0 < rates i) (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (hsPos : ∀ i, 0 < sNodes i) (htPos : ∀ i, 0 < tNodes i) :
    ∃ sigma : ℝ, 0 < sigma ∧ ∀ r : physicalDifferenceSpace n,
      r ∈ (physicalH2Kernel a rates)ᗮ →
        sigma * ‖r‖ ≤ ‖physicalGridMap a rates sNodes tNodes r‖ := by
  exact C145DRE8HilbertStability.exists_positive_complement_gain
    (physicalGridMap a rates sNodes tNodes) (physicalH2Kernel a rates)
    (ker_physicalGridMap a rates hRates sNodes tNodes hsNodes htNodes hsPos htPos)

/-- The source least singular value is attained on the unit sphere of the
actual response-kernel complement inside V0, whenever that complement is nonzero. -/
theorem physicalGrid_exists_least_gain (a rates : Fin (n + 1) → ℝ)
    (hRates : ∀ i, 0 < rates i) (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (hsPos : ∀ i, 0 < sNodes i) (htPos : ∀ i, 0 < tNodes i)
    [Nontrivial (physicalH2Kernel a rates)ᗮ] :
    ∃ (sigma : ℝ) (u : (physicalH2Kernel a rates)ᗮ),
      0 < sigma ∧ ‖u‖ = 1 ∧
      ‖physicalGridMap a rates sNodes tNodes (u : physicalDifferenceSpace n)‖ = sigma ∧
      (∀ v : (physicalH2Kernel a rates)ᗮ, ‖v‖ = 1 →
        sigma ≤ ‖physicalGridMap a rates sNodes tNodes (v : physicalDifferenceSpace n)‖) ∧
      (∀ r : physicalDifferenceSpace n, r ∈ (physicalH2Kernel a rates)ᗮ →
        sigma * ‖r‖ ≤ ‖physicalGridMap a rates sNodes tNodes r‖) := by
  exact C145DRE8HilbertStability.exists_attained_positive_complement_gain
    (physicalGridMap a rates sNodes tNodes) (physicalH2Kernel a rates)
    (ker_physicalGridMap a rates hRates sNodes tNodes hsNodes htNodes hsPos htPos)

/-- A pure one-mode cube; its only nonzero entry is (i,i,i). -/
def pureModeCube (i : Fin (n + 1)) : Tensor (n + 1) :=
  C145PhysicalFrame.C (fun v j => if v = 0 ∧ j = i then 1 else 0)

@[simp] theorem pureModeCube_apply (i j k l : Fin (n + 1)) :
    pureModeCube i j k l = if j = i ∧ k = i ∧ l = i then 1 else 0 := by
  classical
  by_cases hj : j = i <;> by_cases hk : k = i <;> by_cases hl : l = i <;>
    simp [pureModeCube, C145PhysicalFrame.C, hj, hk, hl]

/-- A nonground pure cube belongs to the source symmetric ground-zero space. -/
theorem pureModeCube_mem (i : Fin (n + 1)) (hi : i ≠ 0) :
    fromTensor (pureModeCube i) ∈ physicalDifferenceSpace n := by
  constructor
  · simpa only [toTensor_fromTensor, pureModeCube] using
      (actual_cubic_fullSym (fun v j : Fin (n + 1) => if v = 0 ∧ j = i then 1 else 0))
  · intro j k l h
    simp only [toTensor_fromTensor, pureModeCube_apply]
    rcases h with rfl | rfl | rfl <;> simp [Ne.symm hi]

/-- Its calibrated actual response is a single nonzero rational summand. -/
theorem pureModeCube_response (i : Fin (n + 1)) (a rates : Fin (n + 1) → ℝ)
    (s t : ℝ) :
    responseMap a rates s t (fromTensor (pureModeCube i)) =
      a i ^ 3 / ((s + rates i) * (t + rates i) * (s + t + rates i)) := by
  classical
  simp [responseMap, H, weightedTensor, pureModeCube_apply, ite_and, mul_ite, ite_div, pow_succ]

/-- A nonzero calibrated nonground overlap makes this cube observable at every
positive response pair; positivity derives every denominator guard. -/
theorem pureModeCube_response_ne_zero (i : Fin (n + 1))
    (a rates : Fin (n + 1) → ℝ) (ha : a i ≠ 0) (hRates : ∀ j, 0 < rates j)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    responseMap a rates s t (fromTensor (pureModeCube i)) ≠ 0 := by
  rw [pureModeCube_response]
  have hp := hRates i
  exact div_ne_zero (pow_ne_zero 3 ha) (ne_of_gt (by positivity))

/-- The full actual response kernel is proper in V0 as soon as one nonground
overlap is nonzero, in particular under the source cyclic calibration. -/
theorem physicalH2Kernel_ne_top_of_nonzero_overlap
    (a rates : Fin (n + 1) → ℝ) (hRates : ∀ j, 0 < rates j)
    (i : Fin (n + 1)) (hi : i ≠ 0) (ha : a i ≠ 0) :
    physicalH2Kernel a rates ≠ ⊤ := by
  let x : physicalDifferenceSpace n := ⟨fromTensor (pureModeCube i), pureModeCube_mem i hi⟩
  have hx : x ∉ physicalH2Kernel a rates := by
    intro h
    change ∀ s t, 0 < s → 0 < t → responseMap a rates s t (x : TensorSpace (n + 1)) = 0 at h
    exact pureModeCube_response_ne_zero i a rates ha hRates 1 1 (by norm_num) (by norm_num)
      (h 1 1 (by norm_num) (by norm_num))
  intro htop
  exact hx (by rw [htop]; trivial)

/-- The kernel complement inside V0 is derived to be nontrivial. -/
theorem physicalH2Kernel_orthogonal_nontrivial_of_nonzero_overlap
    (a rates : Fin (n + 1) → ℝ) (hRates : ∀ j, 0 < rates j)
    (i : Fin (n + 1)) (hi : i ≠ 0) (ha : a i ≠ 0) :
    Nontrivial (physicalH2Kernel a rates)ᗮ := by
  apply Submodule.nontrivial_iff_ne_bot.mpr
  intro hzero
  exact physicalH2Kernel_ne_top_of_nonzero_overlap a rates hRates i hi ha
    (Submodule.orthogonal_eq_bot_iff.mp hzero)

/-- In particular the literal sampled response operator on V0 is nonzero. -/
theorem physicalGrid_nonzero_of_nonzero_overlap
    (a rates : Fin (n + 1) → ℝ) (hRates : ∀ j, 0 < rates j)
    (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (hsPos : ∀ j, 0 < sNodes j) (htPos : ∀ j, 0 < tNodes j)
    (i : Fin (n + 1)) (hi : i ≠ 0) (ha : a i ≠ 0) :
    physicalGridMap a rates sNodes tNodes ≠ 0 := by
  intro hzero
  apply physicalH2Kernel_ne_top_of_nonzero_overlap a rates hRates i hi ha
  rw [← ker_physicalGridMap a rates hRates sNodes tNodes hsNodes htNodes hsPos htPos,
    hzero]
  exact LinearMap.ker_zero

/-- Source-level genuine least singular value: no nontriviality certificate is
supplied. One nonzero nonground overlap proves it from a pure mode cube. -/
theorem physicalGrid_exists_least_gain_of_nonzero_overlap
    (a rates : Fin (n + 1) → ℝ) (hRates : ∀ j, 0 < rates j)
    (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (hsPos : ∀ j, 0 < sNodes j) (htPos : ∀ j, 0 < tNodes j)
    (i : Fin (n + 1)) (hi : i ≠ 0) (ha : a i ≠ 0) :
    ∃ (sigma : ℝ) (u : (physicalH2Kernel a rates)ᗮ),
      0 < sigma ∧ ‖u‖ = 1 ∧
      ‖physicalGridMap a rates sNodes tNodes (u : physicalDifferenceSpace n)‖ = sigma ∧
      (∀ v : (physicalH2Kernel a rates)ᗮ, ‖v‖ = 1 →
        sigma ≤ ‖physicalGridMap a rates sNodes tNodes (v : physicalDifferenceSpace n)‖) ∧
      (∀ r : physicalDifferenceSpace n, r ∈ (physicalH2Kernel a rates)ᗮ →
        sigma * ‖r‖ ≤ ‖physicalGridMap a rates sNodes tNodes r‖) := by
  have := physicalH2Kernel_orthogonal_nontrivial_of_nonzero_overlap a rates hRates i hi ha
  exact physicalGrid_exists_least_gain a rates hRates sNodes tNodes
    hsNodes htNodes hsPos htPos


/-- Fixed-calibration source Theorem E for the actual full physical tensor secant.
The two H2 responses may differ. The kernel bundle estimate is exactly source (8.1);
physical rigidity and the global slice bound are derived, not supplied premises.
The singular-value gain and all projections use K-perp inside V0. -/
theorem actual_calibrated_grid_stability
    (a rates : Fin (n + 1) → ℝ) (hRates : ∀ i, 0 < rates i)
    (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ)
    (hsNodes : Function.Injective sNodes) (htNodes : Function.Injective tNodes)
    (hsPos : ∀ i, 0 < sNodes i) (htPos : ∀ i, 0 < tNodes i)
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ) (c : ℝ)
    (hU : C145PhysicalFrame.ColumnOrthonormal U)
    (hV : C145PhysicalFrame.ColumnOrthonormal V)
    (hGU : ∀ v, U v 0 = c) (hGV : ∀ v, V v 0 = c)
    (g : ρ → Fin (n + 1) → ℝ) (delta beta sigma : ℝ)
    (hd : 0 < delta) (hb : 0 ≤ beta) (hsigma : 0 < sigma)
    (hsep : ∀ j k, j ≠ k → delta ^ 2 ≤
      signatureSq (fun r => (Matrix.of U).mulVec (g r)) j k)
    (hq : Real.sqrt ((n + 1 : ℕ) + 2) * beta / delta < 1)
    (hgain : ∀ r : physicalDifferenceSpace n,
      r ∈ (physicalH2Kernel a rates)ᗮ →
        sigma * ‖r‖ ≤ ‖physicalGridMap a rates sNodes tNodes r‖)
    (hkernel : ∀ k : physicalDifferenceSpace n, k ∈ physicalH2Kernel a rates →
      ‖physicalSliceBundle g k‖ ≤ beta * ‖k‖) :
    ‖fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U)‖ ≤
      (Real.sqrt ((n + 1 : ℕ) + 2) * signatureNorm g /
        (delta * (1-Real.sqrt ((n + 1 : ℕ) + 2) * beta / delta) * sigma)) *
      ‖positiveGridMap a rates sNodes tNodes
        (fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U))‖ := by
  let x : physicalDifferenceSpace n :=
    ⟨fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U),
      actual_difference_mem_physicalDifferenceSpace U V c hU hV hGU hGV⟩
  have hphysical : ‖x‖ ≤ (Real.sqrt ((n + 1 : ℕ) + 2) / delta) * ‖physicalSliceBundle g x‖ :=
    actual_full_physical_norm_bound U V c hU hV hGU hGV g delta hd hsep
  have hglobal (r : physicalDifferenceSpace n) :
      ‖physicalSliceBundle g r‖ ≤ signatureNorm g * ‖r‖ :=
    sliceBundle_global_bound g r
  exact C145DRE8HilbertStability.fixed_calibration_tensor_stability
    (physicalGridMap a rates sNodes tNodes) (physicalH2Kernel a rates)
    (physicalSliceBundle g)
    (ker_physicalGridMap a rates hRates sNodes tNodes hsNodes htNodes hsPos htPos)
    x (n + 1) delta beta (signatureNorm g) sigma hd hb (Real.sqrt_nonneg _) hsigma
    hq hgain hphysical hkernel hglobal

/-- The measured vector in the stability theorem consists of the literal
second-transfer differences of the two physical tensors with common a/rates. -/
theorem actual_grid_coordinate_difference
    (a rates : Fin (n + 1) → ℝ) (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ)
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ)
    (p : Fin (2 * (n + 1) - 1) × Fin (2 * (n + 1) - 1)) :
    positiveGridMap a rates sNodes tNodes
      (fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U)) p =
      H rates (weightedTensor a (C145PhysicalFrame.C V)) (sNodes p.1) (tNodes p.2) -
      H rates (weightedTensor a (C145PhysicalFrame.C U)) (sNodes p.1) (tNodes p.2) := by
  change responseMap a rates (sNodes p.1) (tNodes p.2)
    (tensorEquiv.symm (C145PhysicalFrame.C V-C145PhysicalFrame.C U)) = _
  rw [map_sub, map_sub]
  rfl


/-- The same coordinate identity in the accepted physical response notation T. -/
theorem actual_grid_coordinate_physical_response
    (a rates : Fin (n + 1) → ℝ) (sNodes tNodes : Fin (2 * (n + 1) - 1) → ℝ)
    (U V : Fin (n + 1) → Fin (n + 1) → ℝ)
    (p : Fin (2 * (n + 1) - 1) × Fin (2 * (n + 1) - 1)) :
    positiveGridMap a rates sNodes tNodes
      (fromTensor (C145PhysicalFrame.C V-C145PhysicalFrame.C U)) p =
      H rates (C145PhysicalFrame.T V a) (sNodes p.1) (tNodes p.2) -
      H rates (C145PhysicalFrame.T U a) (sNodes p.1) (tNodes p.2) :=
  actual_grid_coordinate_difference a rates sNodes tNodes U V p

end C145DRE8

end
