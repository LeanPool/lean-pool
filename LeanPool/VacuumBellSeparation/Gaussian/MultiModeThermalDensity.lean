/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.IndexedDiagonalDensity
public import LeanPool.VacuumBellSeparation.Gaussian.FiniteProductSeries

/-!
# The actual finite-mode thermal product density

The Hilbert space is the full `ℓ²(Fin m → ℕ, ℂ)`, with no occupation-number
cutoff. The density is its convergent rank-one expansion with product
geometric weights. Trace one, faithfulness, and the genuine CFC power
trace are proved by multi-index Fubini.
-/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open scoped lp

open ContinuousLinearMap
open scoped ENNReal

/-- Multi mode oscillator space with underlying type `ℓ²(Fin m → ℕ, ℂ)`. -/
noncomputable abbrev MultiModeOscillatorSpace (m : ℕ) := ℓ²(Fin m → ℕ, ℂ)

/-- Resolve the existing Hilbert-operator calculus before specializing the lp alias. -/
theorem multiHilbert_realCFC {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] :
    IsometricContinuousFunctionalCalculus ℝ (E →L[ℂ] E) IsSelfAdjoint := inferInstance

theorem multiHilbert_starOrder {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] : StarOrderedRing (E →L[ℂ] E) := inferInstance

theorem multiHilbert_nonnegSpectrum {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E] :
    NonnegSpectrumClass ℝ (E →L[ℂ] E) := inferInstance

noncomputable instance multiModeOscillatorNormedAddCommGroup (m : ℕ) :
    NormedAddCommGroup (MultiModeOscillatorSpace m) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : Fin m → ℕ => ℂ) 2))

noncomputable instance multiModeOscillatorInnerProductSpace (m : ℕ) :
    InnerProductSpace ℂ (MultiModeOscillatorSpace m) :=
  inferInstanceAs (InnerProductSpace ℂ (lp (fun _ : Fin m → ℕ => ℂ) 2))

noncomputable instance multiModeOscillator_completeSpace (m : ℕ) :
    CompleteSpace (MultiModeOscillatorSpace m) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : Fin m → ℕ => ℂ) 2))

noncomputable instance multiModeOscillatorOperatorCStarAlgebra (m : ℕ) :
    CStarAlgebra (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :=
  inferInstanceAs (CStarAlgebra
    ((lp (fun _ : Fin m → ℕ => ℂ) 2) →L[ℂ] (lp (fun _ : Fin m → ℕ => ℂ) 2)))

instance multiModeOscillator_realCFC (m : ℕ) :
    IsometricContinuousFunctionalCalculus ℝ
      (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) IsSelfAdjoint :=
  multiHilbert_realCFC (E := MultiModeOscillatorSpace m)

instance multiModeOscillator_starOrder (m : ℕ) :
    StarOrderedRing (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :=
  multiHilbert_starOrder (E := MultiModeOscillatorSpace m)

instance multiModeOscillator_nonnegSpectrum (m : ℕ) :
    NonnegSpectrumClass ℝ (MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m) :=
  multiHilbert_nonnegSpectrum (E := MultiModeOscillatorSpace m)

/-- Multi mode number basis obtained from `HilbertBasis.ofRepr`. -/
noncomputable def multiModeNumberBasis (m : ℕ) :
    HilbertBasis (Fin m → ℕ) ℂ (MultiModeOscillatorSpace m) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

/-- Multi mode thermal weight given by `∏ j, thermalWeight (q j) (k j)`. -/
def multiModeThermalWeight {m : ℕ} (q : Fin m → ℝ) (k : Fin m → ℕ) : ℝ :=
  ∏ j, thermalWeight (q j) (k j)

theorem multiModeThermalWeight_nonneg {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (k : Fin m → ℕ) :
    0 ≤ multiModeThermalWeight q k :=
  Finset.prod_nonneg fun j _ =>
    mul_nonneg (sub_nonneg.mpr (hq₁ j).le) (pow_nonneg (hq₀ j) (k j))

theorem multiModeThermalWeight_pos {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) (k : Fin m → ℕ) :
    0 < multiModeThermalWeight q k :=
  Finset.prod_pos fun j _ => thermalWeight_pos (hq₀ j) (hq₁ j) (k j)

theorem hasSum_multiModeThermalWeight {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) :
    HasSum (multiModeThermalWeight q) 1 := by
  change HasSum (fun k : Fin m → ℕ => ∏ j, thermalWeight (q j) (k j)) 1
  simpa only [Finset.prod_const_one] using
    hasSum_fin_product_nonneg m (fun j => thermalWeight (q j)) (fun _ => 1)
      (fun j n => mul_nonneg (sub_nonneg.mpr (hq₁ j).le) (pow_nonneg (hq₀ j) n))
      (fun j => hasSum_thermalWeight (hq₀ j) (hq₁ j))

/-- Continuous linear map for the multi mode thermal density, of type `MultiModeOscillatorSpace m
→L[ℂ] MultiModeOscillatorSpace m`. -/
noncomputable def multiModeThermalDensity {m : ℕ} (q : Fin m → ℝ) :
    MultiModeOscillatorSpace m →L[ℂ] MultiModeOscillatorSpace m :=
  indexedDiagonalOperator (multiModeNumberBasis m) (multiModeThermalWeight q)

theorem multiModeThermalDensity_nonneg {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) :
    0 ≤ multiModeThermalDensity q :=
  indexedDiagonalOperator_nonneg (multiModeNumberBasis m)
    (multiModeThermalWeight_nonneg hq₀ hq₁)

theorem multiModeThermalDensity_apply_numberBasis {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (k : Fin m → ℕ) :
    multiModeThermalDensity q (multiModeNumberBasis m k) =
      multiModeThermalWeight q k • multiModeNumberBasis m k :=
  indexedDiagonalOperator_apply_basis (multiModeNumberBasis m)
    (hasSum_multiModeThermalWeight hq₀ hq₁).summable k

theorem positiveTrace_multiModeThermalDensity {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) :
    positiveTrace (multiModeThermalDensity q) = 1 := by
  rw [multiModeThermalDensity, positiveTrace_indexedDiagonalOperator (multiModeNumberBasis m)
    (hasSum_multiModeThermalWeight hq₀ hq₁).summable
    (multiModeThermalWeight_nonneg hq₀ hq₁),
    (hasSum_multiModeThermalWeight hq₀ hq₁).tsum_eq, ENNReal.ofReal_one]

theorem multiModeThermalDensity_isFaithfulDensity {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 < q j) (hq₁ : ∀ j, q j < 1) :
    IsFaithfulDensity (multiModeThermalDensity q) := by
  refine ⟨multiModeThermalDensity_nonneg (fun j => (hq₀ j).le) hq₁,
    positiveTrace_multiModeThermalDensity (fun j => (hq₀ j).le) hq₁, ?_⟩
  exact indexedDiagonalOperator_injective (multiModeNumberBasis m)
    (hasSum_multiModeThermalWeight (fun j => (hq₀ j).le) hq₁).summable
    (multiModeThermalWeight_pos hq₀ hq₁)

theorem multiModeThermalWeight_rpow {m : ℕ} {q : Fin m → ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (τ : ℝ) (k : Fin m → ℕ) :
    multiModeThermalWeight q k ^ τ = ∏ j, thermalWeight (q j) (k j) ^ τ := by
  exact (Real.finsetProd_rpow Finset.univ (fun j => thermalWeight (q j) (k j))
    (fun j _ => mul_nonneg (sub_nonneg.mpr (hq₁ j).le) (pow_nonneg (hq₀ j) (k j))) τ).symm

theorem hasSum_multiModeThermalWeight_rpow {m : ℕ} {q : Fin m → ℝ} {τ : ℝ}
    (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    HasSum (fun k => multiModeThermalWeight q k ^ τ)
      (∏ j, (1 - q j) ^ τ / (1 - q j ^ τ)) := by
  simpa only [multiModeThermalWeight_rpow hq₀ hq₁] using
    hasSum_fin_product_nonneg m (fun j n => thermalWeight (q j) n ^ τ)
      (fun j => (1 - q j) ^ τ / (1 - q j ^ τ))
      (fun j n => Real.rpow_nonneg
        (mul_nonneg (sub_nonneg.mpr (hq₁ j).le) (pow_nonneg (hq₀ j) n)) τ)
      (fun j => hasSum_thermalWeight_rpow (hq₀ j) (hq₁ j) hτ)

theorem multiModeThermalDensity_rpow_apply_numberBasis {m : ℕ} {q : Fin m → ℝ}
    {τ : ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ)
    (k : Fin m → ℕ) :
    (multiModeThermalDensity q ^ τ) (multiModeNumberBasis m k) =
      multiModeThermalWeight q k ^ τ • multiModeNumberBasis m k :=
  indexedDiagonalOperator_rpow_apply_basis (multiModeNumberBasis m)
    (hasSum_multiModeThermalWeight hq₀ hq₁).summable
    (multiModeThermalWeight_nonneg hq₀ hq₁) hτ k

theorem positiveTrace_multiModeThermalDensity_rpow {m : ℕ} {q : Fin m → ℝ}
    {τ : ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    positiveTrace (multiModeThermalDensity q ^ τ) =
      ENNReal.ofReal (∏ j, (1 - q j) ^ τ / (1 - q j ^ τ)) := by
  calc
    _ = ENNReal.ofReal (∑' k, multiModeThermalWeight q k ^ τ) := by
      rw [positiveTrace_eq_tsum_diagonal (multiModeNumberBasis m) CFC.rpow_nonneg,
        ENNReal.ofReal_tsum_of_nonneg
          (fun k => Real.rpow_nonneg (multiModeThermalWeight_nonneg hq₀ hq₁ k) τ)
          (hasSum_multiModeThermalWeight_rpow hq₀ hq₁ hτ).summable]
      apply tsum_congr
      intro k
      rw [multiModeThermalDensity_rpow_apply_numberBasis hq₀ hq₁ hτ,
        inner_smul_right_eq_smul, inner_self_eq_norm_sq_to_K,
        (multiModeNumberBasis m).orthonormal.norm_eq_one]
      simp [Algebra.smul_def]
    _ = _ := congrArg ENNReal.ofReal (hasSum_multiModeThermalWeight_rpow hq₀ hq₁ hτ).tsum_eq

theorem multiModeThermalDensity_rpow_isPositiveTraceClass {m : ℕ} {q : Fin m → ℝ}
    {τ : ℝ} (hq₀ : ∀ j, 0 ≤ q j) (hq₁ : ∀ j, q j < 1) (hτ : 0 < τ) :
    IsPositiveTraceClass (multiModeThermalDensity q ^ τ) := by
  refine ⟨CFC.rpow_nonneg, ?_⟩
  rw [positiveTrace_multiModeThermalDensity_rpow hq₀ hq₁ hτ]
  exact ENNReal.ofReal_lt_top

end VacuumBellSeparation.Gaussian
