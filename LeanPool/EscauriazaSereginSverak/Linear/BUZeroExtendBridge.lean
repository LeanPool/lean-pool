/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.BUShortCutoffZero
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.CarlemanSobolevZeroExt

/-!
# Zero extension across the shifted time face

A field already supported in a smaller cylinder agrees pointwise with its
zero extension from that cylinder.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- A product-coordinate integrand that vanishes off a measurable set has
the same unrestricted and restricted integral. -/
theorem bu_setIntegral_eq_integral_of_zero_off
    (V : Set (Vec3 × ℝ))
    (F : Vec3 × ℝ → ℝ)
    (hzero : ∀ q ∉ V, F q = 0) :
    (∫ q in V, F q ∂(volume : Measure (Vec3 × ℝ))) =
      ∫ q, F q ∂(volume : Measure (Vec3 × ℝ)) := by
  have h := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
    (f := F) (μ := (volume : Measure (Vec3 × ℝ)))
    (MeasurableSet.univ : MeasurableSet (Set.univ : Set (Vec3 × ℝ)))
    (Set.subset_univ V) (fun q hq => hzero q (by simpa using hq.2))
  simpa using h.symm

/-- If a field vanishes off a subset of a cylinder, zero extension from
that cylinder leaves its product-coordinate representation unchanged. -/
theorem bu_zeroExtend_eq_of_support_subset
    {E : Type} [Zero E]
    {Ω : Set Vec3} {I : Set ℝ} {K : Set ParabolicPoint}
    (hKsub : K ⊆ spaceTimeSet Ω I)
    {f : ParabolicPoint → E}
    (hfzero : ∀ z ∉ K, f z = 0) (q : Vec3 × ℝ) :
    zeroExtendField (Ω ×ˢ I)
      (fun r : Vec3 × ℝ => f (parabolicHomeomorph.symm r)) q =
        f (parabolicHomeomorph.symm q) := by
  by_cases hq : q ∈ Ω ×ˢ I
  · simp [zeroExtendField, hq]
  · have hz : parabolicHomeomorph.symm q ∉ K := by
      intro hK
      apply hq
      have hU := hKsub hK
      rcases q with ⟨y, s⟩
      exact hU
    have h0 := hfzero _ hz
    change f q = 0 at h0
    simp [zeroExtendField, hq, h0]

end ESS
