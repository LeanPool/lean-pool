/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GlobalInverse
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.GeneratingSymmetry
public import LeanPool.ArnoldKAM.Arnold1963.Geometry.RealCover

/-!
Construct the inverse of a frequency shift from derivative smallness, including a consistent
analytic branch on the target domain.
-/

@[expose] public section
noncomputable section
open Set Function Filter Metric
open scoped NNReal Topology
namespace KamProject.Arnold1963

variable {n : ℕ}

/-- The identity frequency map plus the specified correction. -/
def frequencyShift (a : ComplexSpace n → ComplexSpace n) (x : ComplexSpace n) := x + a x

/-- The thrice-eroded source on which the frequency shift is inverted. -/
def frequencyInverseSource (V : Set (ComplexSpace n)) (β : ℝ≥0) :=
  erosion V (β + β + β)

/-- The five-times-eroded target used to control the frequency inverse. -/
def frequencyInverseTarget (V : Set (ComplexSpace n)) (β : ℝ≥0) :=
  erosion V (β + β + β + β + β)

/-- A set-restricted inverse of the frequency shift on its eroded source. -/
def frequencyInverse (a : ComplexSpace n → ComplexSpace n)
    (V : Set (ComplexSpace n)) (β : ℝ≥0) :=
  invFunOn (frequencyShift a) (frequencyInverseSource V β)

/-- Analyticity, boundedness and contraction data for inverting a small frequency shift. -/
structure FrequencyShiftData (a : ComplexSpace n → ComplexSpace n)
    (V : Set (ComplexSpace n)) (β κ : ℝ≥0) : Prop where
  radius_pos : 0 < β
  contraction : κ < 1
  analytic : AnalyticOnNhd ℂ a V
  bounded : NormBoundOn a V β
  derivative : ∀ x ∈ V, ‖fderiv ℂ a x‖ ≤ κ

namespace FrequencyShiftData
variable {a : ComplexSpace n → ComplexSpace n} {V : Set (ComplexSpace n)} {β κ : ℝ≥0}
  (d : FrequencyShiftData a V β κ)
include d

theorem lipschitz_ball {x : ComplexSpace n} {r : ℝ≥0} (hx : x ∈ erosion V r) :
    LipschitzOnWith κ a (closedBall x r) :=
  (convex_closedBall x (r : ℝ)).lipschitzOnWith_of_nnnorm_fderiv_le
    (fun y hy => (d.analytic y (hx hy)).differentiableAt) (fun y hy => d.derivative y (hx hy))

theorem shift_injOn : InjOn (frequencyShift a) (frequencyInverseSource V β) := by
  apply injOn_add_of_local_lipschitz (r := ((β + β : ℝ≥0) : ℝ))
    (ε := (β : ℝ)) (κ := κ)
  · intro x hx
    exact d.bounded.norm_le (erosion_subset _ _ hx)
  · simp only [NNReal.coe_add]; linarith
  · exact d.contraction
  · intro x hx
    exact d.lipschitz_ball (erosion_antitone_radius V
      (show β + β ≤ β + β + β from le_self_add) hx)

theorem shift_analytic {x : ComplexSpace n} (hx : x ∈ V) :
    AnalyticAt ℂ (frequencyShift a) x := analyticAt_id.add (d.analytic x hx)

theorem shift_derivative {x : ComplexSpace n} (hx : x ∈ V) :
    fderiv ℂ (frequencyShift a) x = ContinuousLinearMap.id ℂ _ + fderiv ℂ a x := by
  exact ((hasFDerivAt_id (𝕜 := ℂ) x).add (d.analytic x hx).differentiableAt.hasFDerivAt).fderiv

theorem inverse_spec {y : ComplexSpace n} (hy : y ∈ frequencyInverseTarget V β) :
    frequencyInverse a V β y ∈ erosion V (β + β + β + β) ∧
      frequencyShift a (frequencyInverse a V β y) = y ∧
      ‖frequencyInverse a V β y - y‖ ≤ β := by
  have hy' : y ∈ erosion V β := erosion_antitone_radius V (by
    exact_mod_cast (show (β : ℝ) ≤ β + β + β + β + β by linarith [β.coe_nonneg])) hy
  have hbound : NormBoundOn a (closedBall y β) β :=
    ⟨β.coe_nonneg, fun x hx => d.bounded.norm_le (hy' hx)⟩
  obtain ⟨x, ⟨hx, he⟩, _⟩ := existsUnique_add_eq_on_closedBall
    hbound (le_refl (β : ℝ)) d.contraction (d.lipschitz_ball hy')
  have hb : x ∈ erosion V (β + β + β + β) := mem_erosion_of_dist_le hy hx
  have hsource : x ∈ frequencyInverseSource V β :=
    erosion_antitone_radius V (show β + β + β ≤ β + β + β + β from le_self_add) hb
  have hi : frequencyInverse a V β y = x := by
    change invFunOn (frequencyShift a) (frequencyInverseSource V β) y = x
    rw [← he]
    exact d.shift_injOn.leftInvOn_invFunOn hsource
  rw [hi]
  exact ⟨hb, he, by simpa only [mem_closedBall, dist_eq_norm] using hx⟩

theorem inverse_analytic_right {y : ComplexSpace n}
    (hy : y ∈ frequencyInverseTarget V β) :
    AnalyticAt ℂ (frequencyInverse a V β) y ∧
      ∀ᶠ z in 𝓝 y, frequencyShift a (frequencyInverse a V β z) = z := by
  have hs := d.inverse_spec hy
  have hx : frequencyInverse a V β y ∈ V := erosion_subset _ _ hs.1
  have hderiv : ‖fderiv ℂ (frequencyShift a) (frequencyInverse a V β y) -
      ContinuousLinearMap.id ℂ _‖ < 1 := by
    rw [d.shift_derivative hx, add_sub_cancel_left]
    exact (d.derivative _ hx).trans_lt d.contraction
  have hh := analytic_invFunOn d.shift_injOn (erosion_mem_nhds d.radius_pos hs.1)
    (d.shift_analytic hx) hderiv
  rw [hs.2.1] at hh
  exact ⟨hh.1, hh.2.2⟩

theorem target_subset_image :
    frequencyInverseTarget V β ⊆ frequencyShift a '' frequencyInverseSource V β := by
  intro y hy
  have hs := d.inverse_spec hy
  exact ⟨_, erosion_antitone_radius V
    (show β + β + β ≤ β + β + β + β from le_self_add) hs.1, hs.2.1⟩

theorem inverse_conj (hV : ConjInvariant V)
    (ha : ∀ x ∈ V, a (conjVec x) = conjVec (a x))
    {y : ComplexSpace n} (hy : y ∈ frequencyInverseTarget V β) :
    frequencyInverse a V β (conjVec y) = conjVec (frequencyInverse a V β y) := by
  have hyc : conjVec y ∈ frequencyInverseTarget V β := star_mem_erosion hV hy
  have hs := d.inverse_spec hy
  have hc := d.inverse_spec hyc
  apply d.shift_injOn (erosion_antitone_radius V
    (show β + β + β ≤ β + β + β + β from le_self_add) hc.1)
    (star_mem_erosion hV (erosion_antitone_radius V
      (show β + β + β ≤ β + β + β + β from le_self_add) hs.1))
  rw [hc.2.1]
  change conjVec y = conjVec (frequencyInverse a V β y) + a (conjVec _)
  rw [ha _ (erosion_subset _ _ hs.1)]
  simpa only [frequencyShift, conjVec_eq_star, star_add] using (congrArg conjVec hs.2.1).symm

theorem inverse_real (hV : ConjInvariant V)
    (ha : ∀ x ∈ V, a (conjVec x) = conjVec (a x)) {y : RealSpace n}
    (hy : complexify y ∈ frequencyInverseTarget V β) :
    complexify (realPart (frequencyInverse a V β (complexify y))) =
      frequencyInverse a V β (complexify y) := by
  apply complexify_realPart_of_conj
  simpa only [conjVec_complexify] using (d.inverse_conj hV ha hy).symm

theorem derivative_bounds {x : ComplexSpace n} (hx : x ∈ V) (v : ComplexSpace n) :
    (1 - (κ : ℝ)) * ‖v‖ ≤ ‖fderiv ℂ (frequencyShift a) x v‖ ∧
      ‖fderiv ℂ (frequencyShift a) x v‖ ≤ (1 + (κ : ℝ)) * ‖v‖ := by
  rw [d.shift_derivative hx]
  change (1 - (κ : ℝ)) * ‖v‖ ≤ ‖v + fderiv ℂ a x v‖ ∧
    ‖v + fderiv ℂ a x v‖ ≤ (1 + (κ : ℝ)) * ‖v‖
  have hd : ‖fderiv ℂ a x v‖ ≤ (κ : ℝ) * ‖v‖ :=
    ((fderiv ℂ a x).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (d.derivative x hx) (norm_nonneg _))
  constructor
  · have hh : ‖v‖ ≤ ‖v + fderiv ℂ a x v‖ + ‖fderiv ℂ a x v‖ := by
      simpa using norm_sub_le (v + fderiv ℂ a x v) (fderiv ℂ a x v)
    linarith
  · have hh := norm_add_le v (fderiv ℂ a x v)
    linarith

end FrequencyShiftData
end KamProject.Arnold1963
