/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.PartV.HeatPDE
public import LeanPool.EscauriazaSereginSverak.PartV.HeatConvolution
public import LeanPool.EscauriazaSereginSverak.PartV.HeatEntropyTime
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Basic

/-!
# Heat Critical Measurable

The smooth-data heat orbit extended to nonpositive times by its initial
value, for use in `lem:pv-heat-critical`.
-/

public section

open MeasureTheory Filter Set
open CKN.Foundation.Heat CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The smooth-data heat orbit extended to nonpositive times by its initial
value, for use in `lem:pv-heat-critical`. -/
@[expose] def heatConvSmoothExt (f : Vec3 → ℝ) (t : ℝ) (x : Vec3) : ℝ :=
  if t ≤ 0 then f x else heatConv t f x

private theorem heatConvExt_continuous_x {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (t : ℝ) :
    Continuous (fun x : Vec3 => heatConvSmoothExt f t x) := by
  by_cases ht : t ≤ 0
  · simpa [heatConvSmoothExt, ht] using hf.continuous
  · have htpos : 0 < t := lt_of_not_ge ht
    simpa [heatConvSmoothExt, ht] using (heatConv_smooth_input hf hfc htpos).continuous

private theorem heatConvExt_continuous_t {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) (x : Vec3) :
    Continuous (fun t : ℝ => heatConvSmoothExt f t x) := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases lt_trichotomy t 0 with htneg | htzero | htpos
  · have hlocal : (fun s : ℝ => heatConvSmoothExt f s x) =ᶠ[nhds t]
        fun _ => f x := by
      filter_upwards [isOpen_Iio.mem_nhds htneg] with s hs
      change s < 0 at hs
      simp [heatConvSmoothExt, le_of_lt hs]
    exact continuousAt_const.congr_of_eventuallyEq hlocal
  · subst t
    have hleft : Tendsto (fun _ : ℝ => f x)
        (nhdsWithin 0 (Iic 0)) (nhds (f x)) := tendsto_const_nhds
    have hright := heatConv_tendsto_self_nhdsWithin_zero_smooth hf hfc x
    have hleftExt : Tendsto (fun s : ℝ => heatConvSmoothExt f s x)
        (nhdsWithin 0 (Iic 0)) (nhds (f x)) := by
      apply (tendsto_congr' ?_).2 hleft
      filter_upwards [self_mem_nhdsWithin] with s hs
      change s ≤ 0 at hs
      simp [heatConvSmoothExt, hs]
    have hrightExt : Tendsto (fun s : ℝ => heatConvSmoothExt f s x)
        (nhdsWithin 0 (Ioi 0)) (nhds (f x)) := by
      apply (tendsto_congr' ?_).2 hright
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : 0 < s := hs
      simp [heatConvSmoothExt, not_le_of_gt hs']
    have hboth := hleftExt.sup hrightExt
    have hunion : Tendsto (fun s : ℝ => heatConvSmoothExt f s x)
        (nhdsWithin 0 (Iic 0 ∪ Ioi 0)) (nhds (f x)) := by
      rw [nhdsWithin_union]
      exact hboth
    have hunion' : Tendsto (fun s : ℝ => heatConvSmoothExt f s x)
        (nhds 0) (nhds (f x)) := by
      simpa only [Iic_union_Ioi, nhdsWithin_univ] using hunion
    change Tendsto (fun s : ℝ => heatConvSmoothExt f s x)
      (nhds 0) (nhds (heatConvSmoothExt f 0 x))
    simpa [heatConvSmoothExt] using hunion'
  · have hconv : ContinuousAt (fun s : ℝ => heatConv s f x) t :=
      (heatConv_hasDerivAt_laplacianIntegral_smooth hf hfc htpos x).continuousAt
    have hlocal : (fun s : ℝ => heatConvSmoothExt f s x) =ᶠ[nhds t]
        fun s => heatConv s f x := by
      filter_upwards [isOpen_Ioi.mem_nhds htpos] with s hs
      have hs' : 0 < s := hs
      simp [heatConvSmoothExt, not_le_of_gt hs']
    exact hconv.congr_of_eventuallyEq hlocal

/-- The extended scalar heat orbit is jointly measurable, as used in
`lem:pv-heat-critical`. -/
theorem heatConvSmoothExt_joint_measurable {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    Measurable (Function.uncurry (fun t : ℝ => heatConvSmoothExt f t)) :=
  measurable_uncurry_of_continuous_of_measurable
    (fun x => heatConvExt_continuous_t hf hfc x)
    (fun t => (heatConvExt_continuous_x hf hfc t).measurable)

/-- The componentwise extended vector heat orbit is jointly measurable in
space and time for smooth compact data in `lem:pv-heat-critical`. -/
@[expose] def heatConvVec3SmoothExt (b : Vec3 → Vec3) (t : ℝ) (x : Vec3) : Vec3 :=
  fun i => heatConvSmoothExt (fun y => b y i) t x

/-- Joint measurability of the extended vector heat orbit in
`lem:pv-heat-critical`. -/
theorem heatConvVec3SmoothExt_joint_measurable {b : Vec3 → Vec3}
    (hb : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i))
    (hbc : ∀ i : Fin 3, HasCompactSupport (fun x => b x i)) :
    Measurable (Function.uncurry (fun t : ℝ => heatConvVec3SmoothExt b t)) := by
  apply measurable_pi_iff.mpr
  intro i
  change Measurable (Function.uncurry (fun t : ℝ =>
    heatConvSmoothExt (fun y => b y i) t))
  exact heatConvSmoothExt_joint_measurable (hb i) (hbc i)













end ESS

end
