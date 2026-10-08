/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCGeometricTime
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Integrals over countable covers

For nonnegative integrands, a summable family of covering integrals
controls the integral on the covered set.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal

noncomputable section

namespace ESS

/-- A countable cover bounds a nonnegative real integral by the sum of
its covering integrals. -/
theorem uc_integral_le_tsum_of_cover
    (f : ParabolicPoint → ℝ) (hf : ∀ z, 0 ≤ f z)
    (S : Set ParabolicPoint) (Sₙ : ℕ → Set ParabolicPoint)
    (hcover : S ⊆ ⋃ n, Sₙ n)
    (hSInt : IntegrableOn f S volume)
    (hSnInt : ∀ n, IntegrableOn f (Sₙ n) volume)
    (hsum : Summable (fun n => ∫ z in Sₙ n, f z)) :
    (∫ z in S, f z) ≤ ∑' n, ∫ z in Sₙ n, f z := by
  have hSnonneg : 0 ≤ ∫ z in S, f z :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hf)
  have hSnnonneg (n : ℕ) : 0 ≤ ∫ z in Sₙ n, f z :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hf)
  have hsumNonneg : 0 ≤ ∑' n, ∫ z in Sₙ n, f z :=
    tsum_nonneg hSnnonneg
  have hEN : ENNReal.ofReal (∫ z in S, f z) ≤
      ENNReal.ofReal (∑' n, ∫ z in Sₙ n, f z) := by
    rw [ofReal_integral_eq_lintegral_ofReal hSInt
      (Filter.Eventually.of_forall hf),
      ENNReal.ofReal_tsum_of_nonneg hSnnonneg hsum]
    calc
      (∫⁻ z in S, ENNReal.ofReal (f z)) ≤
          ∫⁻ z in ⋃ n, Sₙ n, ENNReal.ofReal (f z) :=
        lintegral_mono_set hcover
      _ ≤ ∑' n, ∫⁻ z in Sₙ n, ENNReal.ofReal (f z) :=
        lintegral_iUnion_le Sₙ _
      _ = ∑' n, ENNReal.ofReal (∫ z in Sₙ n, f z) := by
        congr 1
        funext n
        exact (ofReal_integral_eq_lintegral_ofReal (hSnInt n)
          (Filter.Eventually.of_forall hf)).symm
  exact (ENNReal.ofReal_le_ofReal_iff hsumNonneg).mp hEN

end ESS
