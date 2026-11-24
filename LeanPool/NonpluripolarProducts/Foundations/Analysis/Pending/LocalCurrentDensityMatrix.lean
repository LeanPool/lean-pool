/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.LocalCurrentDeterminant
public import LeanPool.NonpluripolarProducts.Foundations.Analysis.Pending.CoordinateDensityHermitian

/-!
# The density form of `T_ac` is unique and measurable

Blueprint `ana:ac-density-form-measurable` (`blueprint/src/analytic.tex`; TN.5,
    toward `ana:volume-semicontinuity`, route
item 2).  Source: Boucksom 2002 (`bou02-volume`), the absolutely continuous part `T_ac` of a
    positive `(1,1)`-current as a
measurable `(1,1)`-form with locally integrable coefficients (Section 3 of the arXiv version).

`Pending.LocalCurrentDeterminant` represents the density `acWeight(x) L_x` of `T_ac` at `x` (a
    linear functional on the constant
`(n-1,n-1)`-forms `Λ_m`, `n = m + 1`) by a real `(1,1)`-form `α_x`,
    `acWeight(x) L_x(γ) = ⟨γ ∧ α_x⟩`, chosen pointwise
(`acForm`).  Here:

* `eq_zero_of_normalizedHermitianMatrix_eq_zero`: a real `(1,1)`-form with coefficient matrix
    `H_α = 0` is zero (the Hermitian
  entry `α(v, iw) - i α(v, w)` is sesquilinear, and its imaginary part is `-α(v, w)`);
* **`eq_of_forall_topDensity_eq`**: the representing `(1,1)`-form is UNIQUE: if
    `⟨γ ∧ α⟩ = ⟨γ ∧ α'⟩` for every `γ ∈ Λ_m` then
  `α = α'` (`H_{α - α'}` and `H_{α' - α}` are both positive semidefinite by
    `posSemidef_of_nonneg`);
* `acForm_eq_of_forall`: every `(1,1)`-form representing `acWeight(x) L_x` is `acForm hT x`;
* `dualForm`, `topDensity_dualForm`: the `(1,1)`-forms `α_i` representing the coordinate
    functionals of the basis of `Λ_m`;
  **`acForm_eq_sum`**: `acForm hT x = ∑ᵢ acWeight(x) f_{bᵢ}(x) • α_i`;
* **`measurable_acForm_apply`**, **`measurable_acMatrix_apply`**, **`measurable_det_acMatrix`**:
    `x ↦ acForm hT x (v, w)`, the
  entries of the density matrix `A_T(x) = acMatrix hT x` and `x ↦ det A_T(x)` are measurable.

Sorry-free.
-/

@[expose] public section

noncomputable section

open Finset Matrix MeasureTheory TopologicalSpace
open scoped ComplexOrder MatrixOrder

namespace SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix

open FirstPass FirstPass.MongeAmpere FirstPass.PositiveClasses StronglyPositiveForms
    TopDegreeDensity
  LocalProductCurrents LocalCurrentLebesgue LocalCurrentDeterminant OneOneFormMixedTrace

attribute [local instance] addCommGroupFormSpan

/-! ### A `(1,1)`-form is determined by its coefficient matrix -/

section Forms

variable {n : ℕ}

/-- A vector of `ℂⁿ` in the standard basis. -/
theorem eq_sum_coordinateVector (v : ComplexModel n) : v = ∑ j, v.ofLp j • coordinateVector j := by
  ext q
  rw [show ((∑ j, v.ofLp j • coordinateVector j : ComplexModel n)).ofLp q =
      ∑ j, (v.ofLp j • coordinateVector j : ComplexModel n).ofLp q by simp]
  rw [Finset.sum_eq_single q]
  · simp [coordinateVector]
  · intro b _ hb
    simp [coordinateVector, Ne.symm hb]
  · simp

/-- **A real `(1,1)`-form with vanishing coefficient matrix is zero.** -/
theorem eq_zero_of_normalizedHermitianMatrix_eq_zero {α : RealForm n 2} (hα : IsOneOne α)
    (h : normalizedHermitianMatrix α = 0) : α = 0 := by
  classical
  have hent : ∀ j k : Fin n, hermitianEntry α (coordinateVector j) (coordinateVector k) = 0 := by
    intro j k
    have hjk := congrFun (congrFun h j) k
    rw [normalizedHermitianMatrix_apply', Matrix.zero_apply] at hjk
    exact (mul_eq_zero.mp hjk).resolve_left (by exact_mod_cast Real.pi_ne_zero)
  have hall : ∀ v w : ComplexModel n, hermitianEntry α v w = 0 := by
    intro v w
    rw [eq_sum_coordinateVector v, eq_sum_coordinateVector w,
      hermitianEntry_sum_left hα]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [hermitianEntry_sum_right]
    simp [hent]
  have hval : ∀ v w : ComplexModel n, α ![v, w] = 0 := by
    intro v w
    have him := congrArg Complex.im (hall v w)
    simp only [hermitianEntry, Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add, zero_sub, Complex.zero_im,
      neg_eq_zero] at him
    exact him
  ext f
  have hf : f = ![f 0, f 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hf, hval]
  rfl

theorem isOneOne_sub {α α' : RealForm n 2} (hα : IsOneOne α) (hα' : IsOneOne α')
    : IsOneOne (α - α') := by
  intro u v
  simp only [ContinuousAlternatingMap.sub_apply, hα u v, hα' u v]

theorem isOneOne_add {α α' : RealForm n 2} (hα : IsOneOne α) (hα' : IsOneOne α')
    : IsOneOne (α + α') := by
  intro u v
  simp only [ContinuousAlternatingMap.add_apply, hα u v, hα' u v]

theorem isOneOne_smul {α : RealForm n 2} (hα : IsOneOne α) (c : ℝ) : IsOneOne (c • α) := by
  intro u v
  simp only [ContinuousAlternatingMap.smul_apply, hα u v]

theorem isOneOne_zero : IsOneOne (0 : RealForm n 2) := by
  intro u v
  simp

theorem isOneOne_sum {ι : Type*} (s : Finset ι) {α : ι → RealForm n 2} (hα : ∀ i ∈ s,
    IsOneOne (α i)) :
    IsOneOne (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isOneOne_zero
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact isOneOne_add (hα a (Finset.mem_insert_self a s))
        (ih fun i hi => hα i (Finset.mem_insert_of_mem hi))

end Forms

/-! ### Uniqueness of the representing `(1,1)`-form -/

section Unique

variable {m : ℕ}

/-- The wedge pairing `α ↦ ⟨γ ∧ α⟩` with a fixed form `γ` of degree `2m`, as a linear map on the
    real two-forms. -/
def wedgeDensity (γ : RealForm (m + 1) (2 * m)) : RealForm (m + 1) 2 →ₗ[ℝ] ℝ where
  toFun α := topDensity (n := m + 1) (coordinateWedge γ α)
  map_add' α α' := by
    rw [coordinateWedge_add_right]
    exact topDensity_add _ _
  map_smul' c α := by
    rw [coordinateWedge_smul_right]
    exact topDensity_smul _ _

theorem wedgeDensity_apply (γ : RealForm (m + 1) (2 * m)) (α : RealForm (m + 1) 2) :
    wedgeDensity γ α = topDensity (n := m + 1) (coordinateWedge γ α) :=
  rfl

/-- **The `(1,1)`-form representing a linear functional on `Λ_m` is unique.** -/
theorem eq_of_forall_topDensity_eq {α α' : RealForm (m + 1) 2} (hα : IsOneOne α)
    (hα' : IsOneOne α')
    (h : ∀ γ : formSpan (m + 1) m,
      topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α) =
        topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α')) : α = α' := by
  have hrep : ∀ (β β' : RealForm (m + 1) 2), (∀ γ : formSpan (m + 1) m,
      wedgeDensity (γ : RealForm (m + 1) (2 * m)) β = wedgeDensity (γ : RealForm (m + 1) (2 * m))
        β') →
      IsOneOne β → IsOneOne β' → (normalizedHermitianMatrix (β - β')).PosSemidef := by
    intro β β' hββ' hβ hβ'
    refine posSemidef_of_nonneg (L := 0) (fun _ _ => le_rfl) (isOneOne_sub hβ hβ') fun γ => ?_
    rw [LinearMap.zero_apply, ← wedgeDensity_apply, map_sub, hββ' γ, sub_self]
  have h1 := hrep α α' h hα hα'
  have h2 := hrep α' α (fun γ => (h γ).symm) hα' hα
  have hsub : normalizedHermitianMatrix (α' - α) = -normalizedHermitianMatrix (α - α') := by
    rw [show α' - α = (-1 : ℝ) • (α - α') from ((neg_one_smul ℝ (α - α')).trans (neg_sub α
      α')).symm,
      normalizedHermitianMatrix_smul]
    simp
  rw [hsub] at h2
  have hz : normalizedHermitianMatrix (α - α') = 0 := by
    have hle : (0 : Matrix (Fin (m + 1)) (Fin (m + 1)) ℂ) ≤ normalizedHermitianMatrix (α - α')
      := by
      rw [Matrix.le_iff, sub_zero]
      exact h1
    have hge : normalizedHermitianMatrix (α - α') ≤ 0 := by
      rw [Matrix.le_iff, zero_sub]
      exact h2
    exact le_antisymm hge hle
  exact sub_eq_zero.mp (eq_zero_of_normalizedHermitianMatrix_eq_zero (isOneOne_sub hα hα') hz)

variable {U : Opens (ComplexModel (m + 1))} {T : LocalProductCurrent (m + 1) U m}

/-- **Every `(1,1)`-form representing the density of `T_ac` at `x` is `acForm hT x`.** -/
theorem acForm_eq_of_forall (hT : IsPositive T) (x : ComplexModel (m + 1)) {α : RealForm (m + 1) 2}
    (hα : IsOneOne α)
    (hrep : ∀ γ : formSpan (m + 1) m, acWeight hT x * densityForm hT x γ =
      topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) α)) :
    acForm hT x = α :=
  eq_of_forall_topDensity_eq (isOneOne_acForm hT x) hα fun γ => by
    rw [← acWeight_mul_densityForm_eq, hrep]

end Unique

/-! ### Measurability of the density form and of the density matrix -/

section Measurable

variable {m : ℕ}

variable (m) in
/-- The `(1,1)`-form representing the `i`-th coordinate functional of the basis `formBasis` of
    `Λ_m`. -/
def dualForm (i : Fin (Module.finrank ℝ (formSpan (m + 1) m))) : RealForm (m + 1) 2 :=
  Classical.choose (exists_isOneOne_eq_topDensity ((formBasis (m + 1) m).coord i))

theorem isOneOne_dualForm (i : Fin (Module.finrank ℝ (formSpan (m + 1) m))) : IsOneOne (dualForm m
    i) :=
  (Classical.choose_spec (exists_isOneOne_eq_topDensity ((formBasis (m + 1) m).coord i))).1

theorem topDensity_dualForm (i : Fin (Module.finrank ℝ (formSpan (m + 1) m))) (γ : formSpan (m +
    1) m) :
    topDensity (n := m + 1) (coordinateWedge (γ : RealForm (m + 1) (2 * m)) (dualForm m i)) =
      (formBasis (m + 1) m).repr γ i :=
  ((Classical.choose_spec (exists_isOneOne_eq_topDensity ((formBasis (m + 1) m).coord i))).2
    γ).symm

variable {U : Opens (ComplexModel (m + 1))} {T : LocalProductCurrent (m + 1) U m}

/-- **The density form of `T_ac` in the dual basis**:
    `acForm hT x = ∑ᵢ acWeight(x) f_{bᵢ}(x) • α_i`. -/
theorem acForm_eq_sum (hT : IsPositive T) (x : ComplexModel (m + 1)) :
    acForm hT x = ∑ i, (acWeight hT x * hT.density (formBasis (m + 1) m i) x) • dualForm m i := by
  refine acForm_eq_of_forall hT x (isOneOne_sum _ fun i _ => isOneOne_smul (isOneOne_dualForm i)
    _) fun γ => ?_
  rw [← wedgeDensity_apply, map_sum, densityForm_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, wedgeDensity_apply, topDensity_dualForm, smul_eq_mul]
  ring

/-- **`x ↦ acForm hT x (v, w)` is measurable.** -/
theorem measurable_acForm_apply (hT : IsPositive T) (v : Fin 2 → ComplexModel (m + 1)) :
    Measurable fun x => acForm hT x v := by
  simp_rw [acForm_eq_sum hT, ContinuousAlternatingMap.sum_apply,
    ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  exact Finset.measurable_sum _ fun i _ =>
    ((measurable_acWeight hT).mul (hT.measurable_density _)).mul_const _

/-- **The entries of the density matrix `A_T(x)` are measurable.** -/
theorem measurable_acMatrix_apply (hT : IsPositive T) (j k : Fin (m + 1)) :
    Measurable fun x => acMatrix hT x j k := by
  simp only [acMatrix, normalizedHermitianMatrix]
  have h1 := (measurable_acForm_apply hT ![coordinateVector j, Complex.I • coordinateVector k])
  have h2 := (measurable_acForm_apply hT ![coordinateVector j, coordinateVector k])
  exact measurable_const.mul ((Complex.measurable_ofReal.comp h1).sub
    (measurable_const.mul (Complex.measurable_ofReal.comp h2)))

/-- **`x ↦ det A_T(x)` is measurable.** -/
theorem measurable_det_acMatrix (hT : IsPositive T) : Measurable fun x => (acMatrix hT x).det := by
  simp_rw [Matrix.det_apply]
  refine Finset.measurable_sum _ fun σ _ => ?_
  simp_rw [Units.smul_def]
  refine Measurable.const_smul ?_ _
  exact Finset.measurable_prod _ fun i _ => measurable_acMatrix_apply hT _ _

/-- `x ↦ det(A_T(x))^{1/n}` (real part) is measurable. -/
theorem measurable_rpow_det_acMatrix (hT : IsPositive T) :
    Measurable fun x => (acMatrix hT x).det.re ^ (((m + 1 : ℕ) : ℝ)⁻¹) :=
  (Complex.measurable_re.comp (measurable_det_acMatrix hT)).pow_const _

end Measurable

end SGPT.Foundations.Analysis.Pending.LocalCurrentDensityMatrix

end
