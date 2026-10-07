/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.BlowupPressureSplit
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Vec3Norm
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Topology

/-!
# Geometry of rescaled past cylinders

Every fixed bounded past cylinder lies in the rescaled source domain once the
scale is sufficiently small (`prop:blowup-limit`).
-/

public section


open Set Filter CKN.Foundation.Parabolic

noncomputable section

namespace ESS

/-- The rescaled preimage of the cylinder where local suitability is known. -/
@[expose] def blowupSuitableDomain (x₀ : Vec3) (t₀ r : ℝ) : Set ParabolicPoint :=
  (fun z => parabolicTranslate x₀ t₀ (parabolicScale r z)) ⁻¹'
    (vec3Ball 0 (3 / 4 : ℝ) ×ˢ Ioo (-1) 0)

/-- A spatial and temporal scale bound places a fixed bounded past cylinder
inside the rescaled original domain. -/
theorem blowupCylinder_subset_domain
    (x₀ : Vec3) (t₀ r ρ a : ℝ)
    (hx₀ : vec3EuclideanNorm x₀ ≤ 1 / 2)
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : 0 < r)
    (hspace : r * ρ < 1 / 2)
    (htime : r ^ 2 * (-a) < 3 / 4) :
    vec3Ball 0 ρ ×ˢ Ioo a 0 ⊆ blowupDomain x₀ t₀ r := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  change (x₀ + r • x, t₀ + r ^ 2 * t) ∈ goodPointDomain
  constructor
  · change vec3EuclideanNorm (x₀ + r • x - 0) < 1
    rw [sub_zero]
    have hxnorm : vec3EuclideanNorm x < ρ := by
      simpa only [mem_vec3Ball, sub_zero] using hx
    have hscale : vec3EuclideanNorm (r • x) = r * vec3EuclideanNorm x := by
      rw [vec3EuclideanNorm_smul, abs_of_pos hr]
    have hscaled : r * vec3EuclideanNorm x < r * ρ :=
      mul_lt_mul_of_pos_left hxnorm hr
    have htri := vec3EuclideanNorm_add_le x₀ (r • x)
    rw [hscale] at htri
    linarith only [hx₀, hscaled, htri, hspace]
  · change t₀ + r ^ 2 * t ∈ Ioo (-(1 : ℝ)) 0
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have hlow : r ^ 2 * a < r ^ 2 * t :=
      mul_lt_mul_of_pos_left ht.1 hr2
    have hupp : r ^ 2 * t < 0 := mul_neg_of_pos_of_neg hr2 ht.2
    have htime' : -(3 / 4 : ℝ) < r ^ 2 * a := by
      linarith only [htime]
    exact ⟨by linarith only [ht₀.1, htime', hlow],
      by linarith only [ht₀.2, hupp]⟩

/-- Every fixed bounded past cylinder eventually lies in the source domain
along any positive sequence of scales tending to zero. -/
theorem blowupCylinder_eventually_subset_domain
    (x₀ : Vec3) (t₀ ρ a : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : ∀ k, 0 < r k)
    (hr0 : Tendsto r atTop (nhds 0)) :
    ∀ᶠ k in atTop,
      vec3Ball 0 ρ ×ˢ Ioo a 0 ⊆ blowupDomain x₀ t₀ (r k) := by
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1 / 2 := by
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1 / 2)] at hx₀
    simpa only [Set.mem_ofPred_eq, sub_zero] using hx₀
  have hspaceLim : Tendsto (fun k => r k * ρ) atTop (nhds 0) := by
    simpa only [zero_mul] using hr0.mul_const ρ
  have htimeLim : Tendsto (fun k => (r k) ^ 2 * (-a)) atTop (nhds 0) := by
    simpa using (hr0.pow 2).mul_const (-a)
  have hspace : ∀ᶠ k in atTop, r k * ρ < 1 / 2 :=
    hspaceLim.eventually (eventually_lt_nhds (by norm_num))
  have htime : ∀ᶠ k in atTop, (r k) ^ 2 * (-a) < 3 / 4 :=
    htimeLim.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hspace, htime] with k hsk htk
  exact blowupCylinder_subset_domain x₀ t₀ (r k) ρ a
    hxnorm ht₀ (hr k) hsk htk

/-- The smaller spatial scale bound places a fixed cylinder in the region
where the original solution is suitable. -/
theorem blowupCylinder_subset_suitableDomain
    (x₀ : Vec3) (t₀ r ρ a : ℝ)
    (hx₀ : vec3EuclideanNorm x₀ ≤ 1 / 2)
    (ht₀ : t₀ ∈ Icc (-(1 / 4 : ℝ)) 0)
    (hr : 0 < r)
    (hspace : r * ρ < 1 / 4)
    (htime : r ^ 2 * (-a) < 3 / 4) :
    vec3Ball 0 ρ ×ˢ Ioo a 0 ⊆ blowupSuitableDomain x₀ t₀ r := by
  rintro ⟨x, t⟩ ⟨hx, ht⟩
  change (x₀ + r • x, t₀ + r ^ 2 * t) ∈
    vec3Ball 0 (3 / 4 : ℝ) ×ˢ Ioo (-1) 0
  constructor
  · change vec3EuclideanNorm (x₀ + r • x - 0) < 3 / 4
    rw [sub_zero]
    have hxnorm : vec3EuclideanNorm x < ρ := by
      simpa only [mem_vec3Ball, sub_zero] using hx
    have hscale : vec3EuclideanNorm (r • x) = r * vec3EuclideanNorm x := by
      rw [vec3EuclideanNorm_smul, abs_of_pos hr]
    have hscaled : r * vec3EuclideanNorm x < r * ρ :=
      mul_lt_mul_of_pos_left hxnorm hr
    have htri := vec3EuclideanNorm_add_le x₀ (r • x)
    rw [hscale] at htri
    linarith only [hx₀, hscaled, htri, hspace]
  · change t₀ + r ^ 2 * t ∈ Ioo (-(1 : ℝ)) 0
    have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
    have hlow : r ^ 2 * a < r ^ 2 * t :=
      mul_lt_mul_of_pos_left ht.1 hr2
    have hupp : r ^ 2 * t < 0 := mul_neg_of_pos_of_neg hr2 ht.2
    have htime' : -(3 / 4 : ℝ) < r ^ 2 * a := by
      linarith only [htime]
    exact ⟨by linarith only [ht₀.1, htime', hlow],
      by linarith only [ht₀.2, hupp]⟩

/-- Shrinking balls centered over the closed half-ball eventually lie in the
smaller source ball. -/
theorem blowupSpatialBall_eventually_subset_inner
    (x₀ : Vec3) (S : ℝ) (r : ℕ → ℝ)
    (hx₀ : x₀ ∈ closure (vec3Ball 0 (1 / 2 : ℝ)))
    (hr0 : Tendsto r atTop (nhds 0)) :
    ∀ᶠ k in atTop,
      vec3Ball x₀ (r k*S) ⊆ CKN.euclideanBall 0 (3 / 4 : ℝ) := by
  have hxnorm : vec3EuclideanNorm x₀ ≤ 1/2 := by
    rw [closure_vec3Ball (by norm_num : (0 : ℝ) < 1/2)] at hx₀
    simpa only [Set.mem_ofPred_eq, sub_zero] using hx₀
  have hlim : Tendsto (fun k => r k*S) atTop (nhds 0) := by
    simpa using hr0.mul_const S
  have hsmall : ∀ᶠ k in atTop, r k*S < 1/4 :=
    hlim.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [hsmall] with k hk x hx
  rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball
    (by norm_num : (0 : ℝ) < 3/4)]
  change vec3EuclideanNorm (x - 0) < 3/4
  have hx' : vec3EuclideanNorm (x - x₀) < r k*S := hx
  have htri := vec3EuclideanNorm_add_le (x-x₀) x₀
  have hsum : (x-x₀)+x₀ = x := by abel
  rw [hsum] at htri
  simpa only [sub_zero] using
    (lt_of_le_of_lt htri (by linarith only [hx', hxnorm, hk]))

/-- Every bounded open past box fits inside a larger CKN past cylinder. -/
theorem blowupPastBox_subset_pastCylinder
    (R a : ℝ) (hR : 0 < R) (ha : a < 0) :
    ∃ S : ℝ, 0 < S ∧
      (vec3Ball 0 R ×ˢ Ioo a 0) ⊆ parabolicCylinder 0 0 S := by
  let S := R - a + 2
  have hS : 0 < S := by dsimp [S]; linarith only [hR, ha]
  have hSR : R < S := by dsimp [S]; linarith only [ha]
  have hST : -S^2 < a := by
    have hSbig : -a + 1 < S := by dsimp [S]; linarith only [hR]
    have hb : 0 < -a := by linarith only [ha]
    nlinarith only [sq_nonneg (-a), hSbig, hS, hb]
  refine ⟨S, hS, ?_⟩
  rintro ⟨x,t⟩ ⟨hx,ht⟩
  change x ∈ vec3Ball 0 S ∧ t ∈ Ioc (0 - S^2) 0
  constructor
  · change vec3EuclideanNorm (x-0) < S
    exact lt_trans hx hSR
  · constructor
    · linarith only [hST, ht.1]
    · exact ht.2.le

end ESS
