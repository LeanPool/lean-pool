/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap

/-!
# Arbitrary Hilbert direct-sum amplification

The carrier is the genuine vector-valued ℓ² space, with no finite index
assumption. A bounded operator acts on every coordinate. Coordinate matrix
units characterize exactly the operators of this form, by continuity from
single-coordinate vectors. This supplies an actual operator extraction
lemma needed by the finite-source density purification.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace ENNReal

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (ι : Type*)

/-- Hilbert amplification linear. -/
noncomputable def hilbertAmplificationLinear (A : H →L[ℂ] H) :
    lp (fun _ : ι => H) 2 →ₗ[ℂ] lp (fun _ : ι => H) 2 where
  toFun v := ⟨fun i => A (v i),
    ((lp.memℓp v).norm.const_smul ‖A‖).mono (fun i => A.le_opNorm (v i))⟩
  map_add' v w := by
    ext i
    change A (v i + w i) = A (v i) + A (w i)
    exact A.map_add _ _
  map_smul' _ _ := by ext i; simp

omit [CompleteSpace H] in
theorem hilbertAmplificationLinear_norm_le (A : H →L[ℂ] H)
    (v : lp (fun _ : ι => H) 2) : ‖hilbertAmplificationLinear ι A v‖ ≤ ‖A‖ * ‖v‖ := by
  calc
    ‖hilbertAmplificationLinear ι A v‖ ≤ ‖‖A‖ • lp.toNorm v‖ := by
      apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      intro i
      simpa [hilbertAmplificationLinear, norm_smul] using A.le_opNorm (v i)
    _ = ‖A‖ * ‖v‖ := by rw [norm_smul, norm_norm, lp.norm_toNorm]

/-- Diagonal action on the genuine Hilbert direct sum. -/
noncomputable def hilbertAmplification (A : H →L[ℂ] H) :
    lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2 :=
  (hilbertAmplificationLinear ι A).mkContinuous ‖A‖ (hilbertAmplificationLinear_norm_le ι A)

omit [CompleteSpace H] in
@[simp] theorem hilbertAmplification_apply (A : H →L[ℂ] H)
    (v : lp (fun _ : ι => H) 2) (i : ι) : hilbertAmplification ι A v i = A (v i) := rfl

omit [CompleteSpace H] in
theorem norm_hilbertAmplification_le (A : H →L[ℂ] H) :
    ‖hilbertAmplification ι A‖ ≤ ‖A‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A) (hilbertAmplificationLinear_norm_le ι A)

theorem hilbertAmplification_star (A : H →L[ℂ] H) :
    hilbertAmplification ι (star A) = star (hilbertAmplification ι A) := by
  apply (ContinuousLinearMap.eq_adjoint_iff _ _).mpr
  intro v w
  simp only [lp.inner_eq_tsum, hilbertAmplification_apply,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_left]

/-- Hilbert amplification hom. -/
noncomputable def hilbertAmplificationHom : (H →L[ℂ] H) →⋆ₐ[ℂ]
    (lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2) where
  toFun := hilbertAmplification ι
  map_zero' := by ext v i; simp
  map_one' := by ext v i; simp
  map_add' A B := by ext v i; simp
  map_mul' A B := by ext v i; rfl
  commutes' c := by ext v i; simp [Algebra.algebraMap_eq_smul_one]
  map_star' := hilbertAmplification_star ι

/-- The operator from the input component to the output component of a Hilbert-space
amplification. -/
noncomputable def hilbertAmplificationBlock
    (B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2) (i j : ι) : H →L[ℂ] H := by
  classical
  exact (lp.evalCLM ℂ (fun _ : ι => H) 2 i).comp
    (B.comp (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 j))

omit [CompleteSpace H] in
@[simp] theorem hilbertAmplificationBlock_apply [DecidableEq ι]
    (B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2) (i j : ι) (x : H) :
    hilbertAmplificationBlock ι B i j x = B (lp.single 2 j x) i := by
  classical
  unfold hilbertAmplificationBlock
  simp only [ContinuousLinearMap.comp_apply, lp.evalCLM, LinearMap.mkContinuous_apply,
    lp.evalₗ_apply]
  apply congrArg (fun v : lp (fun _ : ι => H) 2 => B v i)
  apply lp.ext
  funext k
  by_cases hk : k = j <;> simp [lp.singleContinuousLinearMap_apply, lp.single_apply, hk]

/-- Hilbert coordinate unit. -/
noncomputable def hilbertCoordinateUnit (i j : ι) :
    lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2 := by
  classical
  exact (lp.singleContinuousLinearMap ℂ (fun _ : ι => H) 2 i).comp
    (lp.evalCLM ℂ (fun _ : ι => H) 2 j)

omit [CompleteSpace H] in
theorem hilbertCoordinateUnit_apply [DecidableEq ι] (i j : ι) (v : lp (fun _ : ι => H) 2) :
    hilbertCoordinateUnit (H := H) ι i j v = lp.single 2 i (v j) := by
  classical
  simp only [hilbertCoordinateUnit, ContinuousLinearMap.comp_apply,
    lp.singleContinuousLinearMap_apply, lp.evalCLM]
  congr 2; exact Subsingleton.elim _ _

omit [CompleteSpace H] in
theorem hilbertAmplification_single [DecidableEq ι] (A : H →L[ℂ] H) (j : ι) (x : H) :
    hilbertAmplification ι A (lp.single 2 j x) = lp.single 2 j (A x) := by
  classical
  ext i
  by_cases h : j = i
  · subst i; simp
  · simp [Ne.symm h]

omit [CompleteSpace H] in
theorem hilbertAmplification_commutes_coordinateUnit (A : H →L[ℂ] H) (i j : ι) :
    hilbertAmplification ι A * hilbertCoordinateUnit ι i j =
      hilbertCoordinateUnit ι i j * hilbertAmplification ι A := by
  classical
  ext v
  simp only [mul_apply_eq_comp, hilbertCoordinateUnit_apply,
    hilbertAmplification_single, hilbertAmplification_apply]

omit [CompleteSpace H] in
/-- Commutation with all coordinate matrix units extracts one actual bounded
operator on H. The anchor is explicit, so no nonempty-index assumption is hidden. -/
theorem eq_hilbertAmplification_of_commutes_coordinateUnits
    (B : lp (fun _ : ι => H) 2 →L[ℂ] lp (fun _ : ι => H) 2) (k : ι)
    (hB : ∀ i j, B * hilbertCoordinateUnit ι i j = hilbertCoordinateUnit ι i j * B) :
    B = hilbertAmplification ι (hilbertAmplificationBlock ι B k k) := by
  classical
  apply lp.ext_continuousLinearMap (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  intro j
  apply ContinuousLinearMap.ext
  intro x
  have h := congrArg (fun T => T (lp.single 2 k x)) (hB j k)
  simpa only [mul_apply_eq_comp, hilbertCoordinateUnit_apply,
    lp.single_apply_self, hilbertAmplification_single, hilbertAmplificationBlock_apply,
    ContinuousLinearMap.comp_apply, lp.singleContinuousLinearMap_apply] using h

end VacuumBellSeparation
