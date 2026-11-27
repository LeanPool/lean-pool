/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveTrace
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval

/-!
# The one-mode thermal density on the infinite-dimensional oscillator space

The oscillator space is genuinely `ℓ²(ℕ, ℂ)`. The density is a norm-convergent
series of bounded rank-one operators, with eigenvalues `(1-q) q^k`. For
`0 < q < 1` it is positive, has trace one, and is injective. This construction
does not identify this basis model with a Schrödinger or Bargmann realization,
and does not assume that the density has a bounded inverse.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped lp

open ContinuousLinearMap InnerProductSpace
open scoped ENNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

/-- A diagonal operator specified by an absolutely summable real sequence.
The convergence hypothesis is required in the evaluation theorems. -/
noncomputable def diagonalOperator (b : HilbertBasis ℕ ℂ E) (w : ℕ → ℝ) :
    E →L[ℂ] E := ∑' k, w k • rankOne ℂ (b k) (b k)

theorem summable_diagonalOperator_terms (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) :
    Summable fun k => w k • rankOne ℂ (b k) (b k) := by
  apply Summable.of_norm
  simpa only [norm_smul, norm_rankOne, b.orthonormal.norm_eq_one, mul_one] using hw.norm

theorem diagonalOperator_nonneg (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k) : 0 ≤ diagonalOperator b w := by
  apply tsum_nonneg
  intro k
  exact smul_nonneg (hw k)
    (ContinuousLinearMap.nonneg_iff_isPositive.mpr (isPositive_rankOne_self (b k)))

theorem diagonalOperator_apply_basis (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) (k : ℕ) :
    diagonalOperator b w (b k) = w k • b k := by
  rw [diagonalOperator, tsum_apply (summable_diagonalOperator_terms b hw)]
  rw [tsum_eq_single k]
  · simp [rankOne_apply, inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  · intro j hj
    simp [rankOne_apply, b.orthonormal.inner_eq_zero hj]

theorem diagonalOperator_inner (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k) (x : E) (k : ℕ) :
    inner ℂ (b k) (diagonalOperator b w x) =
      (w k : ℂ) * inner ℂ (b k) x := by
  have hA := (diagonalOperator_nonneg b hw₀).isSelfAdjoint
  simpa only [hA.adjoint_eq, diagonalOperator_apply_basis b hw,
    inner_smul_left_eq_smul, Algebra.smul_def, RCLike.algebraMap_eq_ofReal,
    RCLike.ofReal_eq_complex_ofReal] using
    ((diagonalOperator b w).adjoint_inner_left x (b k)).symm

theorem diagonalOperator_injective (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) (hwpos : ∀ k, 0 < w k) :
    Function.Injective (diagonalOperator b w) := by
  intro x y hxy
  apply b.repr.injective
  ext k
  rw [b.repr_apply_apply, b.repr_apply_apply]
  have h := congrArg (fun z => inner ℂ (b k) z) hxy
  rw [diagonalOperator_inner b hw (fun k => (hwpos k).le),
    diagonalOperator_inner b hw (fun k => (hwpos k).le)] at h
  exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr (ne_of_gt (hwpos k))) h

theorem positiveTrace_diagonalOperator (b : HilbertBasis ℕ ℂ E)
    {w : ℕ → ℝ} (hw : Summable w) (hw₀ : ∀ k, 0 ≤ w k) :
    positiveTrace (diagonalOperator b w) = ENNReal.ofReal (∑' k, w k) := by
  rw [positiveTrace_eq_tsum_diagonal b (diagonalOperator_nonneg b hw₀),
    ENNReal.ofReal_tsum_of_nonneg hw₀ hw]
  apply tsum_congr
  intro k
  rw [diagonalOperator_apply_basis b hw, inner_smul_right_eq_smul,
    inner_self_eq_norm_sq_to_K, b.orthonormal.norm_eq_one]
  simp [Algebra.smul_def]

/-- The actual infinite-dimensional one-mode oscillator Hilbert space. -/
noncomputable abbrev OscillatorSpace := ℓ²(ℕ, ℂ)

/-- The number basis, implemented by the identity identification with ℓ². -/
noncomputable def numberBasis : HilbertBasis ℕ ℂ OscillatorSpace :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- Thermal weights in the number basis. -/
def thermalWeight (q : ℝ) (k : ℕ) : ℝ := (1 - q) * q ^ k

theorem thermalWeight_pos {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) (k : ℕ) :
    0 < thermalWeight q k := mul_pos (sub_pos.mpr hq₁) (pow_pos hq₀ k)

theorem hasSum_thermalWeight {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    HasSum (thermalWeight q) 1 := by
  have h := (hasSum_geometric_of_lt_one hq₀ hq₁).mul_left (1 - q)
  unfold thermalWeight
  convert! h using 1
  exact (mul_inv_cancel₀ (ne_of_gt (sub_pos.mpr hq₁))).symm

/-- The bounded density operator `(1-q) q^N`, constructed by its convergent
rank-one expansion rather than by an assumed unbounded number operator. -/
noncomputable def thermalDensity (q : ℝ) : OscillatorSpace →L[ℂ] OscillatorSpace :=
  diagonalOperator numberBasis (thermalWeight q)

theorem thermalDensity_nonneg {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    0 ≤ thermalDensity q :=
  diagonalOperator_nonneg numberBasis fun k =>
    mul_nonneg (sub_nonneg.mpr hq₁.le) (pow_nonneg hq₀ k)

theorem thermalDensity_apply_numberBasis {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1)
    (k : ℕ) : thermalDensity q (numberBasis k) = thermalWeight q k • numberBasis k :=
  diagonalOperator_apply_basis numberBasis (hasSum_thermalWeight hq₀ hq₁).summable k

theorem positiveTrace_thermalDensity {q : ℝ} (hq₀ : 0 ≤ q) (hq₁ : q < 1) :
    positiveTrace (thermalDensity q) = 1 := by
  rw [thermalDensity, positiveTrace_diagonalOperator numberBasis
    (hasSum_thermalWeight hq₀ hq₁).summable
    (fun k => mul_nonneg (sub_nonneg.mpr hq₁.le) (pow_nonneg hq₀ k)),
    (hasSum_thermalWeight hq₀ hq₁).tsum_eq, ENNReal.ofReal_one]

theorem thermalDensity_injective {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    Function.Injective (thermalDensity q) :=
  diagonalOperator_injective numberBasis (hasSum_thermalWeight hq₀.le hq₁).summable
    (thermalWeight_pos hq₀ hq₁)

theorem thermalDensity_isFaithfulDensity {q : ℝ} (hq₀ : 0 < q) (hq₁ : q < 1) :
    IsFaithfulDensity (thermalDensity q) :=
  ⟨thermalDensity_nonneg hq₀.le hq₁, positiveTrace_thermalDensity hq₀.le hq₁,
    thermalDensity_injective hq₀ hq₁⟩

end VacuumBellSeparation.Gaussian
