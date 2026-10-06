/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsTop
public import LeanPool.EscauriazaSereginSverak.Endpoint.GoodPointsRestriction

/-!
# Good-point neighborhoods and gluing

This file proves the lower bound at bad points and the local gluing statement
from lem:good-open-glue.
-/

public section

open Filter MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- A strict good-point energy bound persists at some smaller positive radius.
This is the radius choice used in `lem:good-open-glue`. -/
theorem exists_smaller_radius_preserving_goodPoint_smallness
    {E : ℝ≥0∞} {r ε : ℝ}
    (hr : 0 < r)
    (hsmall : ENNReal.ofReal (r⁻¹ ^ 2) * E < ENNReal.ofReal (ε / 8)) :
    ∃ r' : ℝ, 0 < r' ∧ r' < r ∧
      ENNReal.ofReal (r'⁻¹ ^ 2) * E < ENNReal.ofReal (ε / 8) := by
  let a : ℝ≥0∞ := ENNReal.ofReal (r⁻¹ ^ 2) * E
  have hfinite : a ≠ ⊤ := ne_top_of_lt hsmall
  have hcont : ContinuousAt (fun c : ℝ => ENNReal.ofReal c * a) 1 := by
    have hmul : ContinuousAt (fun v : ℝ≥0∞ => v * a) (ENNReal.ofReal 1) :=
      (ENNReal.continuous_mul_const hfinite).continuousAt
    have hone : ENNReal.ofReal (1 : ℝ) = 1 := by norm_num
    have hcomp := hmul.comp ENNReal.continuous_ofReal.continuousAt
    change ContinuousAt (fun c : ℝ => ENNReal.ofReal c * a) 1
    simpa only [Function.comp_def, hone] using hcomp
  have hnear : ∀ᶠ c : ℝ in 𝓝 1,
      ENNReal.ofReal c * a < ENNReal.ofReal (ε / 8) := by
    have hmem : Set.Iio (ENNReal.ofReal (ε / 8)) ∈ 𝓝 a :=
      isOpen_Iio.mem_nhds hsmall
    have htend : Tendsto (fun c : ℝ => ENNReal.ofReal c * a) (𝓝 1) (𝓝 a) := by
      simpa only [ENNReal.ofReal_one, one_mul] using hcont.tendsto
    exact htend.eventually hmem
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hnear
  let c := 1 + min (δ / 2) 1
  have hcgt : 1 < c := by
    dsimp [c]
    have hminpos : 0 < min (δ / 2) 1 := by positivity
    linarith only [hminpos]
  have hcpos : 0 < c := lt_trans zero_lt_one hcgt
  have hcdist : dist c 1 < δ := by
    rw [Real.dist_eq]
    change |(1 + min (δ / 2) 1) - 1| < δ
    have hmin : min (δ / 2) 1 < δ := by
      calc
        min (δ / 2) 1 ≤ δ / 2 := min_le_left _ _
        _ < δ := by linarith only [hδpos]
    have hval : (1 + min (δ / 2) 1) - 1 = min (δ / 2) 1 := by ring
    rw [hval, abs_of_nonneg (by positivity)]
    exact hmin
  have hcmul : ENNReal.ofReal c * a < ENNReal.ofReal (ε / 8) := hδ hcdist
  let r' := r / Real.sqrt c
  have hsqrtpos : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
  have hsqrtgt : 1 < Real.sqrt c := by
    have hsq : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hcpos.le
    have hnn : 0 ≤ Real.sqrt c := Real.sqrt_nonneg c
    nlinarith only [hcgt, hsq, hnn]
  have hr'pos : 0 < r' := by dsimp [r']; positivity
  have hr'lt : r' < r := by
    dsimp [r']
    exact div_lt_self hr hsqrtgt
  have hscale : r'⁻¹ ^ 2 = c * r⁻¹ ^ 2 := by
    dsimp [r']
    have hsq : (Real.sqrt c) ^ 2 = c := Real.sq_sqrt hcpos.le
    field_simp
    nlinarith only [hsq]
  have hsmall' : ENNReal.ofReal (r'⁻¹ ^ 2) * E < ENNReal.ofReal (ε / 8) := by
    rw [hscale, ENNReal.ofReal_mul (le_of_lt hcpos), mul_assoc]
    simpa only [a] using hcmul
  exact ⟨r', hr'pos, hr'lt, hsmall'⟩

/-- A smaller past cylinder and its closure remain in the closed top domain.
This is the admissibility step used in `lem:good-open-glue`. -/
theorem goodPoint_smaller_radius_admissible
    {z : ParabolicPoint} {R r : ℝ}
    (hz : z ∈ goodPointClosedTopDomain) (hRpos : 0 < R) (hrpos : 0 < r)
    (hrR : r < R)
    (hRdomain : goodPointPastCylinder z.1 z.2 R ⊆ goodPointDomain) :
    goodPointPastCylinder z.1 z.2 r ⊆ goodPointDomain ∧
      closure (parabolicCylinder z.1 z.2 r) ⊆ goodPointClosedTopDomain := by
  have htimeR : Ioo (z.2 - R ^ 2) z.2 ⊆ Ioo (-1) 0 := by
    intro s hs
    have hx : z.1 ∈ vec3Ball z.1 R := by
      simp [vec3Ball, vec3EuclideanNorm_zero, hRpos]
    have hp : (z.1, s) ∈ goodPointPastCylinder z.1 z.2 R := by
      change z.1 ∈ vec3Ball z.1 R ∧ s ∈ Ioo (z.2 - R ^ 2) z.2
      exact ⟨hx, hs⟩
    exact (hRdomain hp).2
  have htimeEnds :=
    (Set.Ioo_subset_Ioo_iff (by nlinarith only [hRpos])).mp htimeR
  have hRspace : vec3Ball z.1 R ⊆ vec3Ball 0 1 := by
    intro y hy
    let s := z.2 - R ^ 2 / 2
    have hs : s ∈ Ioo (z.2 - R ^ 2) z.2 := by
      dsimp [s]
      constructor <;> nlinarith only [hRpos]
    have hp : (y, s) ∈ goodPointPastCylinder z.1 z.2 R := by
      change y ∈ vec3Ball z.1 R ∧ s ∈ Ioo (z.2 - R ^ 2) z.2
      exact ⟨hy, hs⟩
    have hRpair := hRdomain hp
    exact hRpair.1
  have htimeR' : Ioo (z.2 - r ^ 2) z.2 ⊆ Ioo (-1) 0 := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have hlow : z.2 - R ^ 2 ≤ z.2 - r ^ 2 := by
        nlinarith only [hrR, hrpos, hRpos]
      have hlowR : -1 ≤ z.2 - R ^ 2 := htimeEnds.1
      have hlowS : z.2 - R ^ 2 < s := hlow.trans_lt hs.1
      linarith only [hlowR, hlowS]
    · exact hs.2.trans_le hz.2.2
  have hpast : goodPointPastCylinder z.1 z.2 r ⊆ goodPointDomain := by
    intro q hq
    rcases hq with ⟨hqx, hqt⟩
    have hqxR : q.1 ∈ vec3Ball z.1 R := by
      change vec3EuclideanNorm (q.1 - z.1) < r at hqx
      change vec3EuclideanNorm (q.1 - z.1) < R
      exact hqx.trans hrR
    exact ⟨hRspace hqxR, htimeR' hqt⟩
  have hclosed : closure (parabolicCylinder z.1 z.2 r) ⊆
      goodPointClosedTopDomain := by
    have hclosure := closure_parabolicCylinder (x := z.1) (t := z.2) (r := r) hrpos
    intro q hq
    rw [hclosure] at hq
    rcases hq with ⟨hqx, hqt⟩
    rcases hqt with ⟨hqtlo, hqthi⟩
    have hqxR : q.1 ∈ vec3Ball z.1 R := by
      change vec3EuclideanNorm (q.1 - z.1) < R
      exact hqx.trans_lt hrR
    have htlo : -1 < z.2 - r ^ 2 := by
      have hr2R2 : r ^ 2 < R ^ 2 := by nlinarith only [hrR, hrpos, hRpos]
      have hlow : z.2 - R ^ 2 < z.2 - r ^ 2 := by nlinarith only [hr2R2]
      linarith only [htimeEnds.1, hlow]
    exact ⟨hRspace hqxR,
      ⟨htlo.trans_le hqtlo, le_trans hqthi hz.2.2⟩⟩
  exact ⟨hpast, hclosed⟩

end ESS
