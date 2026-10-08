/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Leray.RegularisedBesselLaplacianStep

/-!
# Even-order Sobolev membership from iterated Laplacians

Repeated use of the second-order Bessel identity recovers complete
integer Sobolev regularity from physical L² Laplacian data.
-/

public section

open MeasureTheory FourierTransform
open scoped ENNReal FourierTransform SchwartzMap Laplacian

noncomputable section

namespace CKN.Leray

open CKN.Foundation.Parabolic

/-- If all iterated distributional Laplacians through order `k` are
represented by L² fields, then the original distribution lies in H²ᵏ. -/
theorem regularised_memSobolev_even_of_iterated_laplacian_L2
    (k : ℕ) (D : 𝓢'(L2Vec3, ComplexVec3))
    (h : ∀ j ≤ k, TemperedDistribution.MemSobolev 0 2
      ((Laplacian.laplacian :
        𝓢'(L2Vec3, ComplexVec3) → 𝓢'(L2Vec3, ComplexVec3))^[j] D)) :
    TemperedDistribution.MemSobolev ((2 * k : ℕ) : ℝ) 2 D := by
  induction k generalizing D with
  | zero =>
      simpa using h 0 (le_refl 0)
  | succ k ih =>
      let L : 𝓢'(L2Vec3, ComplexVec3) → 𝓢'(L2Vec3, ComplexVec3) :=
        Laplacian.laplacian
      have hD : TemperedDistribution.MemSobolev ((2 * k : ℕ) : ℝ) 2 D :=
        ih D (by intro j hj; exact h j (Nat.le_trans hj (Nat.le_succ k)))
      have hΔ : TemperedDistribution.MemSobolev ((2 * k : ℕ) : ℝ) 2
          (Laplacian.laplacian D) := by
        apply ih (Laplacian.laplacian D)
        intro j hj
        have hIter : (L^[j]) (L D) = (L^[j + 1]) D := by
          rw [Function.iterate_succ_apply]
        change TemperedDistribution.MemSobolev 0 2 ((L^[j]) (L D))
        rw [hIter]
        exact h (j + 1) (Nat.succ_le_succ hj)
      have hStep := regularised_memSobolev_add_two_of_laplacian
        ((2 * k : ℕ) : ℝ) D hD hΔ
      convert hStep using 1
      push_cast
      ring

/-- L² representatives for all iterated Laplacians give an exact
complete H²ᵏ lift of the original spatial field. -/
theorem regularised_bessel_even_lift_of_iterated_laplacian_L2
    (k : ℕ) (f : ComplexVectorL2)
    (h : ∀ j ≤ k, ∃ g : ComplexVectorL2,
      ((Laplacian.laplacian :
        𝓢'(L2Vec3, ComplexVec3) → 𝓢'(L2Vec3, ComplexVec3))^[j]
          (f : 𝓢'(L2Vec3, ComplexVec3))) =
        (g : 𝓢'(L2Vec3, ComplexVec3))) :
    ∃ v : BesselPotentialSpace L2Vec3 ComplexVec3 ((2 * k : ℕ) : ℝ) 2,
      regularisedBesselSobolevToL2 ((2 * k : ℕ) : ℝ)
        (by positivity) v = f := by
  have hSob : TemperedDistribution.MemSobolev ((2 * k : ℕ) : ℝ) 2
      (f : 𝓢'(L2Vec3, ComplexVec3)) := by
    apply regularised_memSobolev_even_of_iterated_laplacian_L2 k
    intro j hj
    obtain ⟨g, hg⟩ := h j hj
    exact (TemperedDistribution.memSobolev_zero_iff).2 ⟨g, hg⟩
  let v := hSob.toBesselPotentialSpace
  refine ⟨v, ?_⟩
  have hDistr :
      ((regularisedBesselSobolevToL2 ((2 * k : ℕ) : ℝ)
        (by positivity) v : ComplexVectorL2) :
        𝓢'(L2Vec3, ComplexVec3)) =
          (f : 𝓢'(L2Vec3, ComplexVec3)) := by
    rw [regularisedBesselSobolevToL2_toTemperedDistribution_eq]
    exact hSob.toBesselPotentialSpace_toDistr
  exact (LinearMap.ker_eq_bot.mp
    (MeasureTheory.Lp.ker_toTemperedDistributionCLM_eq_bot
      (F := ComplexVec3) (μ := volume) (p := 2))) hDistr

end CKN.Leray

end
