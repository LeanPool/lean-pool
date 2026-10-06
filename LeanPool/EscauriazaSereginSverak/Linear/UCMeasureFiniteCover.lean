/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCMeasureCover

/-!
# Integrals over finite covers

The integral over a set covered by finitely many measurable pieces is
bounded by the sum of the piece integrals for nonnegative functions.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic
open scoped ENNReal
attribute [local instance] Classical.propDecidable

noncomputable section

namespace ESS

/-- A finite cover bounds a nonnegative real integral by the sum of its
covering integrals. -/
theorem uc_integral_le_sum_of_finite_cover
    (f : ParabolicPoint → ℝ) (hf : ∀ z, 0 ≤ f z)
    (S : Set ParabolicPoint) (G : Finset Vec3)
    (T : Vec3 → Set ParabolicPoint)
    (hcover : S ⊆ ⋃ c ∈ G, T c)
    (hSInt : IntegrableOn f S volume)
    (hTInt : ∀ c ∈ G, IntegrableOn f (T c) volume) :
    (∫ z in S, f z) ≤ ∑ c ∈ G, ∫ z in T c, f z := by
  have hnonneg (c : Vec3) (hc : c ∈ G) :
      0 ≤ ∫ z in T c, f z :=
    integral_nonneg_of_ae (Filter.Eventually.of_forall hf)
  have hsum : 0 ≤ ∑ c ∈ G, ∫ z in T c, f z :=
    Finset.sum_nonneg fun c hc => hnonneg c hc
  have hEN : ENNReal.ofReal (∫ z in S, f z) ≤
      ENNReal.ofReal (∑ c ∈ G, ∫ z in T c, f z) := by
    rw [ofReal_integral_eq_lintegral_ofReal hSInt
      (Filter.Eventually.of_forall hf),
      ENNReal.ofReal_sum_of_nonneg (fun c hc => hnonneg c hc)]
    calc
      (∫⁻ z in S, ENNReal.ofReal (f z)) ≤
          ∫⁻ z in ⋃ c ∈ G, T c, ENNReal.ofReal (f z) :=
        lintegral_mono_set hcover
      _ ≤ ∑' c : G, ∫⁻ z in T c.1, ENNReal.ofReal (f z) := by
        convert lintegral_iUnion_le (fun c : G => T c.1) _ using 1
        simp only [iUnion_subtype]
      _ = ∑ c ∈ G, ∫⁻ z in T c, ENNReal.ofReal (f z) := by
        rw [tsum_fintype]
        simpa only [Finset.attach_eq_univ] using
          (Finset.sum_attach G (fun c =>
            ∫⁻ z in T c, ENNReal.ofReal (f z)))
      _ = ∑ c ∈ G, ENNReal.ofReal (∫ z in T c, f z) := by
        apply Finset.sum_congr rfl
        intro c hc
        exact (ofReal_integral_eq_lintegral_ofReal (hTInt c hc)
          (Filter.Eventually.of_forall hf)).symm
  exact (ENNReal.ofReal_le_ofReal_iff hsum).mp hEN

end ESS
