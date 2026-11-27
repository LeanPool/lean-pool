/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Fock.SymmetricTensorTotality
public import Mathlib.Analysis.Analytic.OfScalars
public import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Totality of the literal symmetric Fock exponential vectors

Pairing with e(zv) gives an actual everywhere-convergent scalar power
series. Analytic uniqueness recovers each tensor-degree diagonal pairing.
The proved diagonal totality in each actual symmetric sector then
recovers the whole Hilbert direct-sum vector.
-/

@[expose] public section

noncomputable section
namespace VacuumBellSeparation.Fock
open Filter
open scoped Topology InnerProductSpace

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem exponentialComponent_smul (c : ℂ) (v : H) (n : ℕ) :
    exponentialComponent H (c • v) n = c ^ n • exponentialComponent H v n := by
  rw [exponentialComponent, pureSymmetricTensor_smul, smul_comm]
  rfl

/-- Exponential analysis series defined as `FormalMultilinearSeries.ofScalars ℂ (fun n => inner ℂ
(x n) (exponentialComponent H v n))`. -/
def exponentialAnalysisSeries (x : SymmetricFockSpace H) (v : H) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => inner ℂ (x n) (exponentialComponent H v n))

theorem hasSum_exponentialAnalysis (x : SymmetricFockSpace H) (v : H) (z : ℂ) :
    HasSum (fun n => z ^ n • (exponentialAnalysisSeries H x v).coeff n)
      (inner ℂ x (exponentialVector H (z • v))) := by
  have h := lp.hasSum_inner (𝕜 := ℂ) x (exponentialVector H (z • v))
  convert h using 1
  funext n
  change z ^ n • (exponentialAnalysisSeries H x v).coeff n =
    inner ℂ (x n) (exponentialComponent H (z • v) n)
  rw [exponentialComponent_smul, inner_smul_right]
  simp only [exponentialAnalysisSeries, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]

theorem hasFPowerSeriesAt_exponentialAnalysis (x : SymmetricFockSpace H) (v : H) :
    HasFPowerSeriesAt (fun z : ℂ => inner ℂ x (exponentialVector H (z • v)))
      (exponentialAnalysisSeries H x v) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  exact Eventually.of_forall fun z => by
    simpa only [zero_add] using hasSum_exponentialAnalysis H x v z

theorem eq_zero_of_inner_exponentialVector_zero (x : SymmetricFockSpace H)
    (hx : ∀ v, inner ℂ x (exponentialVector H v) = 0) : x = 0 := by
  have hcoeff (v : H) (n : ℕ) : inner ℂ (x n) (exponentialComponent H v n) = 0 := by
    have hf : (fun z : ℂ => inner ℂ x (exponentialVector H (z • v))) =
        (0 : ℂ → ℂ) := funext fun z => hx (z • v)
    have hp : HasFPowerSeriesAt (0 : ℂ → ℂ) (exponentialAnalysisSeries H x v) 0 := by
      rw [← hf]
      exact hasFPowerSeriesAt_exponentialAnalysis H x v
    have hn := congrFun hp.eq_zero n
    exact (FormalMultilinearSeries.ofScalars_eq_zero ℂ n).mp hn
  apply lp.ext
  funext n
  apply eq_zero_of_inner_pureSymmetricTensor_zero H n (x n)
  intro v
  have hn := hcoeff v n
  rw [exponentialComponent, inner_smul_right] at hn
  have hfac : (0 : ℝ) < (n.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hden : (Real.sqrt (n.factorial : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr hfac))
  exact (mul_eq_zero.mp hn).resolve_left (inv_ne_zero hden)

theorem exponentialVector_dense_span :
    (Submodule.span ℂ (Set.range (exponentialVector H))).topologicalClosure = ⊤ := by
  let K := Submodule.span ℂ (Set.range (exponentialVector H))
  have horth : Kᗮ = ⊥ := by
    apply (Submodule.eq_bot_iff _).mpr
    intro x hx
    apply eq_zero_of_inner_exponentialVector_zero H x
    intro v
    exact K.inner_left_of_mem_orthogonal (Submodule.subset_span ⟨v, rfl⟩) hx
  apply Submodule.orthogonal_eq_bot_iff.mp
  rw [Submodule.orthogonal_closure, horth]

end VacuumBellSeparation.Fock
