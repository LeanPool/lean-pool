/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/
module

public import LeanPool.NairTenenbaum.Arithmetic.Arithmetic
public import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Tactic.Positivity

/-! # Choosing an integer moment order

Rounding `a sqrt(u/log u)` upward preserves the leading normalized cost
`a/2+t/a`. Choosing `a=sqrt(2t)` gives the sharp coefficient `sqrt(2t)`.
-/

@[expose] public section

namespace NairTenenbaum

open Real Filter
open scoped Topology

/-- The real scale used to select the Hooley moment order. -/
noncomputable def momentOrderScale (a u : ℝ) : ℝ := a * Real.sqrt (u / Real.log u)

/-- The integral moment order obtained by rounding the chosen scale. -/
noncomputable def roundedMomentOrder (a u : ℝ) : ℕ := ⌈momentOrderScale a u⌉₊

theorem tendsto_div_log_atTop : Tendsto (fun u : ℝ => u / Real.log u) atTop atTop := by
  have H : Tendsto (fun u : ℝ => Real.log u / u) atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero, ?_⟩
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with u hu
    exact div_pos (Real.log_pos hu) (by linarith)
  have H' : Tendsto (fun u : ℝ => (Real.log u / u)⁻¹) atTop atTop := H.inv_tendsto_nhdsGT_zero
  simpa only [inv_div] using H'

theorem tendsto_momentOrderScale {a : ℝ} (ha : 0 < a) :
    Tendsto (momentOrderScale a) atTop atTop :=
  (Real.tendsto_sqrt_atTop.comp tendsto_div_log_atTop).const_mul_atTop ha

theorem tendsto_roundedMomentOrder {a : ℝ} (ha : 0 < a) :
    Tendsto (roundedMomentOrder a) atTop atTop :=
  tendsto_nat_ceil_atTop.comp (tendsto_momentOrderScale ha)

theorem tendsto_roundedMomentOrder_div_scale {a : ℝ} (ha : 0 < a) :
    Tendsto (fun u => (roundedMomentOrder a u : ℝ) / momentOrderScale a u) atTop (𝓝 1) :=
  tendsto_nat_ceil_div_atTop.comp (tendsto_momentOrderScale ha)

theorem momentOrderScale_pos {a u : ℝ} (ha : 0 < a) (hu : 1 < u) :
    0 < momentOrderScale a u :=
  mul_pos ha (Real.sqrt_pos.mpr (div_pos (by linarith) (Real.log_pos hu)))

theorem momentOrderScale_log_identity {a u : ℝ} (hu : 1 < u) :
    momentOrderScale a u * Real.log u = a * Real.sqrt (u * Real.log u) := by
  have hu₀ : 0 < u := by linarith
  have hl : 0 < Real.log u := Real.log_pos hu
  have hs : Real.sqrt (Real.log u) ≠ 0 := (Real.sqrt_pos.mpr hl).ne'
  unfold momentOrderScale
  rw [Real.sqrt_div hu₀.le, Real.sqrt_mul hu₀.le]
  field_simp
  rw [Real.sq_sqrt hl.le]

theorem momentOrderScale_sqrt_identity {a u : ℝ} (hu : 1 < u) :
    momentOrderScale a u * Real.sqrt (u * Real.log u) = a * u := by
  have hu₀ : 0 < u := by linarith
  have hl : 0 < Real.log u := Real.log_pos hu
  unfold momentOrderScale
  rw [mul_assoc, ← Real.sqrt_mul (div_nonneg hu₀.le hl.le),
    show u / Real.log u * (u * Real.log u) = u ^ 2 by field_simp,
    Real.sqrt_sq hu₀.le]

theorem log_momentOrderScale {a u : ℝ} (ha : 0 < a) (hu : 1 < u) :
    Real.log (momentOrderScale a u) =
      Real.log a + (Real.log u - Real.log (Real.log u)) / 2 := by
  have hl : 0 < Real.log u := Real.log_pos hu
  unfold momentOrderScale
  rw [Real.log_mul ha.ne' (Real.sqrt_pos.mpr (div_pos (by linarith) hl)).ne',
    Real.log_sqrt (div_nonneg (by linarith) hl.le), Real.log_div (by linarith : u ≠ 0) hl.ne']

theorem tendsto_log_roundedMomentOrder_div_log {a : ℝ} (ha : 0 < a) :
    Tendsto (fun u => Real.log (roundedMomentOrder a u) / Real.log u) atTop (𝓝 (1 / 2)) := by
  have Hr := (tendsto_roundedMomentOrder_div_scale ha).log (by norm_num : (1 : ℝ) ≠ 0)
  have Hz : Tendsto (fun u => Real.log ((roundedMomentOrder a u : ℝ) / momentOrderScale a u) /
      Real.log u) atTop (𝓝 0) := Hr.div_atTop Real.tendsto_log_atTop
  have Ha : Tendsto (fun u : ℝ => Real.log a / Real.log u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have Hl : Tendsto (fun u : ℝ => Real.log (Real.log u) / Real.log u) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp Real.tendsto_log_atTop
  have H := Hz.add (Ha.add (((tendsto_const_nhds (x := (1 : ℝ))).sub Hl).div_const 2))
  have H' : Tendsto (fun u : ℝ =>
      Real.log ((roundedMomentOrder a u : ℝ) / momentOrderScale a u) / Real.log u +
      (Real.log a / Real.log u + (1 - Real.log (Real.log u) / Real.log u) / 2))
      atTop (𝓝 (1 / 2)) := by simpa using H
  apply H'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), (tendsto_roundedMomentOrder ha).eventually_ge_atTop
      1] with u hu hq
  have hs := momentOrderScale_pos ha hu
  have hq' : (0 : ℝ) < roundedMomentOrder a u := by exact_mod_cast hq
  rw [Real.log_div hq'.ne' hs.ne', log_momentOrderScale ha hu]
  have hl := Real.log_pos hu
  field_simp
  ring

theorem tendsto_momentOrderCost {a K t : ℝ} (ha : 0 < a) (hK : 0 < K) :
    Tendsto (fun u =>
      ((roundedMomentOrder a u : ℝ) * Real.log (K * roundedMomentOrder a u) +
        t * u / roundedMomentOrder a u) / Real.sqrt (u * Real.log u))
      atTop (𝓝 (a / 2 + t / a)) := by
  have Hq := tendsto_roundedMomentOrder_div_scale ha
  have HK : Tendsto (fun u : ℝ => Real.log K / Real.log u) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  have Hl := HK.add (tendsto_log_roundedMomentOrder_div_log ha)
  have H := ((Hq.mul_const a).mul Hl).add (((tendsto_const_nhds (x := t)).div Hq (by
    norm_num)).div_const a)
  have H' : Tendsto (fun u : ℝ =>
      (((roundedMomentOrder a u : ℝ) / momentOrderScale a u) * a) *
        (Real.log K / Real.log u + Real.log (roundedMomentOrder a u) / Real.log u) +
      (t / ((roundedMomentOrder a u : ℝ) / momentOrderScale a u)) / a)
      atTop (𝓝 (a / 2 + t / a)) := by
    convert H using 1
    simp only [one_mul, zero_add, div_one, mul_one_div]
  apply H'.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), (tendsto_roundedMomentOrder ha).eventually_ge_atTop
      1] with u hu hq
  have hs := momentOrderScale_pos ha hu
  have hq' : (0 : ℝ) < roundedMomentOrder a u := by exact_mod_cast hq
  have hl := Real.log_pos hu
  have hu₀ : 0 < u := by linarith
  have hw : 0 < Real.sqrt (u * Real.log u) := Real.sqrt_pos.mpr (mul_pos hu₀ hl)
  have HS := momentOrderScale_log_identity (a := a) hu
  have HT := momentOrderScale_sqrt_identity (a := a) hu
  have Hleft :
      (((roundedMomentOrder a u : ℝ) / momentOrderScale a u) * a) *
        (Real.log K / Real.log u + Real.log (roundedMomentOrder a u) / Real.log u) =
      ((roundedMomentOrder a u : ℝ) * (Real.log K + Real.log (roundedMomentOrder a u))) /
        Real.sqrt (u * Real.log u) := by
    field_simp
    rw [mul_comm (Real.log u) u]
    linear_combination -(Real.log K + Real.log (roundedMomentOrder a u)) * HS
  have Hright : (t / ((roundedMomentOrder a u : ℝ) / momentOrderScale a u)) / a =
      t * u / ((roundedMomentOrder a u : ℝ) * Real.sqrt (u * Real.log u)) := by
    field_simp
    linear_combination t * HT
  rw [Hleft, Hright, Real.log_mul hK.ne' hq'.ne']
  ring

theorem eventually_exists_momentOrderCost_le {K t η : ℝ} (hK : 0 < K) (ht : 0 < t)
    (hη : Real.sqrt (2 * t) < η) (N : ℕ) :
    ∀ᶠ u : ℝ in atTop, ∃ q : ℕ, N ≤ q ∧
      (q : ℝ) * Real.log (K * q) + t * u / q ≤ η * Real.sqrt (u * Real.log u) := by
  have ha : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by positivity)
  have heq : Real.sqrt (2 * t) / 2 + t / Real.sqrt (2 * t) = Real.sqrt (2 * t) := by
    have hs := Real.sq_sqrt (by positivity : 0 ≤ 2 * t)
    field_simp
    nlinarith
  have H := (tendsto_momentOrderCost (t := t) ha hK).eventually_lt_const
    (heq.trans_lt hη)
  filter_upwards [H, eventually_gt_atTop (1 : ℝ),
    (tendsto_roundedMomentOrder ha).eventually_ge_atTop N] with u hu hu₁ hq
  refine ⟨roundedMomentOrder (Real.sqrt (2 * t)) u, hq, ?_⟩
  have hw : 0 < Real.sqrt (u * Real.log u) :=
    Real.sqrt_pos.mpr (mul_pos (by linarith) (Real.log_pos hu₁))
  exact ((div_lt_iff₀ hw).mp hu).le

end NairTenenbaum
