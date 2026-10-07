/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Linear.UCMeasureFiniteCover

/-!
# Gaussian control of one geometric time slab

The finite spatial cover turns uniform Gaussian box bounds into a slab
bound with geometric covering multiplicity.
-/

public section


open MeasureTheory Set CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- Uniform bounds on Gaussian boxes control the corresponding local
space-time slab. -/
theorem uc_geometric_slab_integral_le
    (F : Finset Vec3)
    (hF : ∀ y ∈ closure (vec3Ball 0 1),
      ∃ c ∈ F, y ∈ vec3Ball c (1 / 2))
    (x : Vec3) (r : ℝ) (hr : 0 < r) (n : ℕ)
    (f : ParabolicPoint → ℝ) (hf : ∀ z, 0 ≤ f z)
    (A : ℝ) (hA : 0 ≤ A)
    (hSInt : IntegrableOn f
      (spaceTimeSet (vec3Ball x r)
        (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) volume)
    (hBoxInt : ∀ c ∈ vec3Ball x (2 * r), IntegrableOn f
      (spaceTimeSet
        (vec3Ball c (Real.sqrt
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))))
        (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)))) volume)
    (hBox : ∀ c ∈ vec3Ball x (2 * r),
      (∫ z in spaceTimeSet
        (vec3Ball c (Real.sqrt
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))))
        (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
          (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))), f z) ≤ A) :
    (∫ z in spaceTimeSet (vec3Ball x r)
      (Ioo ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2)
        (2 * ((3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2))), f z) ≤
      (F.card : ℝ) ^ (n + 1) * A := by
  let t : ℝ := (3 / 5 : ℝ) * (3 / 4) ^ n * r ^ 2
  let q : ℝ := r / (2 : ℝ) ^ (n + 1)
  have hq : q ≤ Real.sqrt (2 * t) :=
    uc_geometric_cover_radius_le r hr n
  obtain ⟨G, hcard, hnear, hcover⟩ :=
    uc_ball_cover_near_centers F hF x r hr (n + 1)
  let S : Set ParabolicPoint := spaceTimeSet (vec3Ball x r) (Ioo t (2 * t))
  let B (c : Vec3) : Set ParabolicPoint :=
    spaceTimeSet (vec3Ball c (Real.sqrt (2 * t))) (Ioo t (2 * t))
  have hSsub : S ⊆ ⋃ c ∈ G, B c := by
    intro z hz
    obtain ⟨c, hc, hzc⟩ := hcover z.1 hz.1
    refine mem_iUnion₂.mpr ⟨c, hc, ?_⟩
    exact ⟨(vec3Ball_mono hq) hzc, hz.2⟩
  have hbound := uc_integral_le_sum_of_finite_cover
    f hf S G B hSsub hSInt (fun c hc => hBoxInt c (hnear c hc))
  have hsum : (∑ c ∈ G, ∫ z in B c, f z) ≤ G.card * A := by
    calc
      _ ≤ ∑ _c ∈ G, A := Finset.sum_le_sum
        (fun c hc => hBox c (hnear c hc))
      _ = G.card * A := by simp
  have hcardReal : (G.card : ℝ) ≤ (F.card : ℝ) ^ (n + 1) := by
    exact_mod_cast hcard
  have hfinal := hbound.trans hsum
  change (∫ z in S, f z) ≤ (F.card : ℝ) ^ (n + 1) * A
  exact hfinal.trans (mul_le_mul_of_nonneg_right hcardReal hA)

end ESS
