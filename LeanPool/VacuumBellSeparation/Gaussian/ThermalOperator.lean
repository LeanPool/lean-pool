/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.ThermalScalar
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
public import Mathlib.Analysis.SpecialFunctions.Artanh
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.InnerProductSpace.StarOrder
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-!
# Thermal comparison: infimum statements and operator form (Lemma 4.3)

Source: the manuscript (Section 4.2 and Lemma 4.3,
"Thermal comparison"). The scalar inequality `c_τ ≤ 𝔮_τ(u)` is proved in `ThermalScalar.lean`.
This file proves:

* the infimum statements of Lemma 4.3 (the constants `c_τ` are the infima of the scalar
  ratios): `𝔮_τ(u) → (1 - τ)/τ` as `u → 0⁺`, `𝔮_τ(u) → 2^{1-2τ}` as `u → ∞`, and `c_τ` is the
  greatest lower bound of `{𝔮_τ(u) : u > 0}` (`isGLB_thermalRatio`, `sInf_thermalRatio`);
* the scalar function `h_τ(x) = x coth(τ artanh x) - 1` on `[0, 1]` (`thermalIncrement`, with
  the continuous extension `(1 - τ)/τ` at `0` and the value `0` at `1`), its continuity
  (`continuousOn_thermalIncrement`) and the bound `h_τ(x) ≥ c_τ (1 - x²)^τ`
  (`thermalIncrement_ge`);
* the operator form: for a positive contraction `d` in a unital C⋆-algebra (e.g. `H →L[ℂ] H`),
  `H_τ(I) = h_τ(d) ≥ c_τ R^{2τ}` with `R = (1 - d²)^{1/2}`, all defined by the continuous
  functional calculus (`thermal_comparison`, `thermal_comparison_clm`).
-/

@[expose] public section

namespace VacuumBellSeparation

open Filter Topology

/-! ### Limits of the ratio and the infimum statements -/

/-- `sinh (a u) / u → a` as `u → 0⁺`. -/
theorem tendsto_sinh_mul_div_nhdsGT (a : ℝ) :
    Tendsto (fun u : ℝ => Real.sinh (a * u) / u) (𝓝[>] 0) (𝓝 a) := by
  have h1 : HasDerivAt (fun u : ℝ => a * u) (a * 1) 0 :=
    (hasDerivAt_id' (x := (0 : ℝ))).const_mul a
  have h2 : HasDerivAt (fun u : ℝ => Real.sinh (a * u)) (Real.cosh (a * 0) * (a * 1)) 0 :=
    h1.sinh
  rw [mul_zero, Real.cosh_zero, mul_one, one_mul] at h2
  refine h2.tendsto_slope_zero_right.congr fun t => ?_
  change t⁻¹ • (Real.sinh (a * (0 + t)) - Real.sinh (a * 0)) = Real.sinh (a * t) / t
  rw [zero_add, mul_zero, Real.sinh_zero, sub_zero, smul_eq_mul, div_eq_inv_mul]

/-- The ratio `𝔮_τ(u)` tends to `(1 - τ)/τ` as `u → 0⁺`. -/
theorem tendsto_thermalRatio_nhdsGT {τ : ℝ} (hτ0 : 0 < τ) :
    Tendsto (thermalRatio τ) (𝓝[>] 0) (𝓝 ((1 - τ) / τ)) := by
  have h1 := (tendsto_sinh_mul_div_nhdsGT (1 - τ)).div (tendsto_sinh_mul_div_nhdsGT τ) hτ0.ne'
  have hc : Tendsto Real.cosh (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h := (Real.continuous_cosh.tendsto (0 : ℝ)).mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    rwa [Real.cosh_zero] at h
  have h2 := hc.rpow_const (p := 2 * τ - 1) (Or.inl one_ne_zero)
  rw [Real.one_rpow] at h2
  have h3 := h1.mul h2
  rw [mul_one] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hu0 : u ≠ 0 := (Set.mem_Ioi.mp hu).ne'
  simp only [Pi.div_apply, thermalRatio]
  rw [div_div_div_cancel_right₀ hu0]

/-- Exponential form of the ratio, used for the limit at infinity:
`𝔮_τ(u) = (1 - e^{-2(1-τ)u}) / (1 - e^{-2τu}) · ((1 + e^{-2u})/2)^{2τ-1}` for `τ, u > 0`. -/
theorem thermalRatio_eq_exp {τ u : ℝ} (hτ0 : 0 < τ) (hu : 0 < u) :
    thermalRatio τ u = (1 - Real.exp (-2 * ((1 - τ) * u))) / (1 - Real.exp (-2 * (τ * u)))
      * ((1 + Real.exp (-2 * u)) / 2) ^ (2 * τ - 1) := by
  have hsinh : ∀ x : ℝ, Real.sinh x = Real.exp x * (1 - Real.exp (-2 * x)) / 2 := by
    intro x
    have e : Real.exp x * Real.exp (-2 * x) = Real.exp (-x) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [Real.sinh_eq, mul_sub, mul_one, e]
  have hcosh : Real.cosh u = Real.exp u * ((1 + Real.exp (-2 * u)) / 2) := by
    have e : Real.exp u * Real.exp (-2 * u) = Real.exp (-u) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [Real.cosh_eq, ← e]; ring
  have hy : (0 : ℝ) ≤ (1 + Real.exp (-2 * u)) / 2 := by positivity
  have hpow : Real.cosh u ^ (2 * τ - 1)
      = Real.exp (u * (2 * τ - 1)) * ((1 + Real.exp (-2 * u)) / 2) ^ (2 * τ - 1) := by
    rw [hcosh, Real.mul_rpow (Real.exp_pos u).le hy, ← Real.exp_mul]
  have hB : 1 - Real.exp (-2 * (τ * u)) ≠ 0 := by
    have hτu : 0 < τ * u := mul_pos hτ0 hu
    have : Real.exp (-2 * (τ * u)) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    exact (sub_pos.mpr this).ne'
  have e2 : Real.exp (τ * u) = Real.exp ((1 - τ) * u) * Real.exp (u * (2 * τ - 1)) := by
    rw [← Real.exp_add]; congr 1; ring
  have hE1 : Real.exp ((1 - τ) * u) ≠ 0 := (Real.exp_pos _).ne'
  have hE3 : Real.exp (u * (2 * τ - 1)) ≠ 0 := (Real.exp_pos _).ne'
  unfold thermalRatio
  rw [hsinh ((1 - τ) * u), hsinh (τ * u), hpow, e2]
  field_simp

/-- The ratio `𝔮_τ(u)` tends to `2^{1-2τ}` as `u → ∞`. -/
theorem tendsto_thermalRatio_atTop {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    Tendsto (thermalRatio τ) atTop (𝓝 ((2 : ℝ) ^ (1 - 2 * τ))) := by
  have hE : ∀ c : ℝ, 0 < c → Tendsto (fun u : ℝ => Real.exp (-2 * (c * u))) atTop (𝓝 0) := by
    intro c hc
    have h1 : Tendsto (fun u : ℝ => 2 * (c * u)) atTop atTop :=
      (tendsto_id.const_mul_atTop hc).const_mul_atTop two_pos
    refine (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).congr fun u => ?_
    change Real.exp (-(2 * (c * u))) = Real.exp (-2 * (c * u))
    rw [neg_mul]
  have hA := hE (1 - τ) (by linarith)
  have hB := hE τ hτ0
  have hC : Tendsto (fun u : ℝ => Real.exp (-2 * u)) atTop (𝓝 0) := by
    refine (hE 1 one_pos).congr fun u => ?_
    rw [one_mul]
  have h1 : Tendsto
      (fun u : ℝ => (1 - Real.exp (-2 * ((1 - τ) * u))) / (1 - Real.exp (-2 * (τ * u))))
      atTop (𝓝 ((1 - 0) / (1 - 0))) :=
    (tendsto_const_nhds.sub hA).div (tendsto_const_nhds.sub hB) (by norm_num)
  have h2 : Tendsto (fun u : ℝ => ((1 + Real.exp (-2 * u)) / 2) ^ (2 * τ - 1)) atTop
      (𝓝 (((1 + 0) / 2) ^ (2 * τ - 1))) :=
    ((tendsto_const_nhds.add hC).div_const 2).rpow_const (Or.inl (by norm_num))
  have hval : (1 - 0 : ℝ) / (1 - 0) * ((1 + 0) / 2) ^ (2 * τ - 1) = (2 : ℝ) ^ (1 - 2 * τ) := by
    rw [sub_zero, div_one, one_mul, add_zero, one_div, Real.inv_rpow (by norm_num : (0 : ℝ) ≤ 2),
      ← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), neg_sub]
  have h3 := h1.mul h2
  rw [hval] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with u hu
  exact (thermalRatio_eq_exp hτ0 hu).symm

/-- `c_τ = (1 - τ)/τ` for `1/2 ≤ τ` (at `τ = 1/2` both formulas give `1`). -/
theorem thermalConst_of_half_le {τ : ℝ} (hτ : 1 / 2 ≤ τ) : thermalConst τ = (1 - τ) / τ := by
  unfold thermalConst
  split_ifs with h
  · have h' : τ = 1 / 2 := le_antisymm h hτ
    subst h'
    norm_num
  · rfl

/-- For `0 < τ ≤ 1/2` the constant `c_τ = 2^{1-2τ}` is the limit of `𝔮_τ(u)` as `u → ∞`. -/
theorem tendsto_thermalRatio_atTop_thermalConst {τ : ℝ} (hτ0 : 0 < τ) (hτ : τ ≤ 1 / 2) :
    Tendsto (thermalRatio τ) atTop (𝓝 (thermalConst τ)) := by
  rw [thermalConst, ite_eq_left hτ]
  exact tendsto_thermalRatio_atTop hτ0 (by linarith)

/-- For `1/2 ≤ τ < 1` the constant `c_τ = (1 - τ)/τ` is the limit of `𝔮_τ(u)` as `u → 0⁺`. -/
theorem tendsto_thermalRatio_nhdsGT_thermalConst {τ : ℝ} (hτ : 1 / 2 ≤ τ) :
    Tendsto (thermalRatio τ) (𝓝[>] 0) (𝓝 (thermalConst τ)) := by
  rw [thermalConst_of_half_le hτ]
  exact tendsto_thermalRatio_nhdsGT (by linarith)

/-- Lemma 4.3, the infimum statement (the constants `c_τ` are the infima of the scalar ratios):
for `0 < τ < 1`, `c_τ` is the greatest lower bound of `{𝔮_τ(u) : u > 0}`. -/
theorem isGLB_thermalRatio {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    IsGLB (thermalRatio τ '' Set.Ioi 0) (thermalConst τ) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    exact thermalConst_le_thermalRatio hτ0 hτ1 hu
  · have hb' : ∀ u : ℝ, 0 < u → b ≤ thermalRatio τ u := fun u hu =>
      hb (Set.mem_image_of_mem (thermalRatio τ) hu)
    by_cases hτ : τ ≤ 1 / 2
    · refine ge_of_tendsto (tendsto_thermalRatio_atTop_thermalConst hτ0 hτ) ?_
      filter_upwards [eventually_gt_atTop 0] with u hu using hb' u hu
    · refine ge_of_tendsto (tendsto_thermalRatio_nhdsGT_thermalConst (by linarith)) ?_
      filter_upwards [self_mem_nhdsWithin] with u hu using hb' u hu

/-- Lemma 4.3, infimum form: `c_τ = inf_{u > 0} 𝔮_τ(u)` for `0 < τ < 1`. -/
theorem sInf_thermalRatio {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    sInf (thermalRatio τ '' Set.Ioi 0) = thermalConst τ :=
  (isGLB_thermalRatio hτ0 hτ1).csInf_eq (Set.nonempty_Ioi.image _)

/-- `c_τ ≤ (1 - τ)/τ`, the limit of `𝔮_τ` at `0⁺` (this is the value of `h_τ` at `0`). -/
theorem thermalConst_le_one_sub_div {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) :
    thermalConst τ ≤ (1 - τ) / τ := by
  refine ge_of_tendsto (tendsto_thermalRatio_nhdsGT hτ0) ?_
  filter_upwards [self_mem_nhdsWithin] with u hu using thermalConst_le_thermalRatio hτ0 hτ1 hu

/-! ### The scalar function `h_τ` on `[0, 1]` -/

/-- The thermal increment `h_τ(x) = x coth(τ artanh x) - 1` of Section 4.2 (so that
`H_τ(I) = h_τ(d)` by the functional calculus), extended continuously to `[0, 1]`: it takes the
value `(1 - τ)/τ` at `x = 0` and `0` at `x = 1` (`continuousOn_thermalIncrement`). Here
`coth y = cosh y / sinh y`. Values outside `[0, 1]` are never used. -/
noncomputable def thermalIncrement (τ x : ℝ) : ℝ :=
  if x = 0 then (1 - τ) / τ
  else if x = 1 then 0
  else x * (Real.cosh (τ * Real.artanh x) / Real.sinh (τ * Real.artanh x)) - 1

/-- `h_τ(0) = (1 - τ)/τ`. -/
theorem thermalIncrement_zero (τ : ℝ) : thermalIncrement τ 0 = (1 - τ) / τ := by
  rw [thermalIncrement, ite_eq_left rfl]

/-- `h_τ(1) = 0`. -/
theorem thermalIncrement_one (τ : ℝ) : thermalIncrement τ 1 = 0 := by
  rw [thermalIncrement, ite_eq_right one_ne_zero, ite_eq_left rfl]

/-- For `0 < x < 1`, `h_τ(x) = x coth(τ artanh x) - 1`. -/
theorem thermalIncrement_of_mem_Ioo {τ x : ℝ} (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    thermalIncrement τ x
      = x * (Real.cosh (τ * Real.artanh x) / Real.sinh (τ * Real.artanh x)) - 1 := by
  rw [thermalIncrement, ite_eq_right hx.1.ne', ite_eq_right hx.2.ne]

/-- At `x = tanh u` with `u > 0`: `h_τ(tanh u) = tanh u · coth(τu) - 1`, the right side of
`thermal_increment_ge`. -/
theorem thermalIncrement_tanh {τ u : ℝ} (hu : 0 < u) :
    thermalIncrement τ (Real.tanh u)
      = Real.tanh u * (Real.cosh (τ * u) / Real.sinh (τ * u)) - 1 := by
  have h0 : 0 < Real.tanh u := by
    rw [Real.tanh_eq_sinh_div_cosh]
    exact div_pos (Real.sinh_pos_iff.mpr hu) (Real.cosh_pos u)
  rw [thermalIncrement_of_mem_Ioo ⟨h0, Real.tanh_lt_one u⟩, Real.artanh_tanh]

/-- Lemma 4.3 on the closed interval: `h_τ(x) ≥ c_τ (1 - x²)^τ` for `0 < τ < 1` and
`x ∈ [0, 1]` (interior: `thermal_increment_ge` with `x = tanh u`; endpoints directly). -/
theorem thermalIncrement_ge {τ x : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    thermalConst τ * (1 - x ^ 2) ^ τ ≤ thermalIncrement τ x := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases hx0.eq_or_lt with rfl | hx0
  · have h0 : thermalConst τ * (1 - (0 : ℝ) ^ 2) ^ τ = thermalConst τ := by
      rw [zero_pow two_ne_zero, sub_zero, Real.one_rpow, mul_one]
    rw [h0, thermalIncrement_zero]
    exact thermalConst_le_one_sub_div hτ0 hτ1
  rcases hx1.lt_or_eq with hx1 | rfl
  · have hu : 0 < Real.artanh x := Real.artanh_pos ⟨hx0, hx1⟩
    have hx : Real.tanh (Real.artanh x) = x := Real.tanh_artanh ⟨by linarith, hx1⟩
    rw [← hx, thermalIncrement_tanh hu]
    exact thermal_increment_ge hτ0 hτ1 hu
  · have h1 : thermalConst τ * (1 - (1 : ℝ) ^ 2) ^ τ = 0 := by
      rw [one_pow, sub_self, Real.zero_rpow hτ0.ne', mul_zero]
    exact (h1.trans (thermalIncrement_one τ).symm).le

/-- `c_τ > 0` for `0 < τ < 1`. -/
theorem thermalConst_pos {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) : 0 < thermalConst τ := by
  unfold thermalConst
  split_ifs
  · exact Real.rpow_pos_of_pos two_pos _
  · exact div_pos (by linarith) hτ0

/-- `h_τ ≥ 0` on `[0, 1]` for `0 < τ < 1` (a consequence of `thermalIncrement_ge`). -/
theorem thermalIncrement_nonneg {τ x : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hx : x ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ thermalIncrement τ x := by
  have h : 0 ≤ 1 - x ^ 2 := by
    obtain ⟨hx0, hx1⟩ := hx
    nlinarith
  exact (mul_nonneg (thermalConst_pos hτ0 hτ1).le (Real.rpow_nonneg h τ)).trans
    (thermalIncrement_ge hτ0 hτ1 hx)

/-! ### Continuity of `h_τ` on `[0, 1]` -/

/-- With `x = tanh u`: `coth(τu) = ((1 + x)^τ + (1 - x)^τ) / ((1 + x)^τ - (1 - x)^τ)`. -/
theorem coth_mul_eq_rpow (τ u : ℝ) :
    Real.cosh (τ * u) / Real.sinh (τ * u)
      = ((1 + Real.tanh u) ^ τ + (1 - Real.tanh u) ^ τ)
        / ((1 + Real.tanh u) ^ τ - (1 - Real.tanh u) ^ τ) := by
  have hc := Real.cosh_pos u
  have h1 : (1 + Real.tanh u) ^ τ = Real.exp (τ * u) * Real.cosh u ^ (-τ) := by
    have e : 1 + Real.tanh u = Real.exp u / Real.cosh u := by
      rw [Real.tanh_eq_sinh_div_cosh, eq_div_iff hc.ne', add_mul, one_mul,
        div_mul_cancel₀ _ hc.ne', Real.cosh_add_sinh]
    rw [e, Real.div_rpow (Real.exp_pos u).le hc.le, ← Real.exp_mul, Real.rpow_neg hc.le,
      div_eq_mul_inv, mul_comm u τ]
  have h2 : (1 - Real.tanh u) ^ τ = Real.exp (-(τ * u)) * Real.cosh u ^ (-τ) := by
    have e : 1 - Real.tanh u = Real.exp (-u) / Real.cosh u := by
      rw [Real.tanh_eq_sinh_div_cosh, eq_div_iff hc.ne', sub_mul, one_mul,
        div_mul_cancel₀ _ hc.ne', Real.cosh_sub_sinh]
    rw [e, Real.div_rpow (Real.exp_pos _).le hc.le, ← Real.exp_mul, Real.rpow_neg hc.le,
      div_eq_mul_inv, neg_mul, mul_comm u τ]
  rw [h1, h2, ← add_mul, ← sub_mul,
    mul_div_mul_right _ _ (Real.rpow_pos_of_pos hc (-τ)).ne',
    Real.cosh_eq (τ * u), Real.sinh_eq (τ * u),
    div_div_div_cancel_right₀ (two_ne_zero : (2 : ℝ) ≠ 0)]

/-- Closed form of `h_τ` on `(0, 1]`:
`h_τ(x) = x ((1 + x)^τ + (1 - x)^τ) / ((1 + x)^τ - (1 - x)^τ) - 1`. -/
theorem thermalIncrement_eq_of_pos {τ x : ℝ} (hτ0 : 0 < τ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    thermalIncrement τ x
      = x * (((1 + x) ^ τ + (1 - x) ^ τ) / ((1 + x) ^ τ - (1 - x) ^ τ)) - 1 := by
  rcases hx1.lt_or_eq with hx1 | rfl
  · have hx : Real.tanh (Real.artanh x) = x := Real.tanh_artanh ⟨by linarith, hx1⟩
    rw [thermalIncrement_of_mem_Ioo ⟨hx0, hx1⟩, coth_mul_eq_rpow, hx]
  · rw [thermalIncrement_one, sub_self, Real.zero_rpow hτ0.ne', add_zero, sub_zero,
      div_self (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 1 + 1) τ).ne', mul_one, sub_self]

/-- `D_τ(x) = (1 + x)^τ - (1 - x)^τ`, the denominator of the closed form of `h_τ`; its
difference quotient `dslope D_τ 0` is continuous, with value `2τ` at `0`. -/
noncomputable def thermalDiff (τ x : ℝ) : ℝ := (1 + x) ^ τ - (1 - x) ^ τ

/-- `D_τ(0) = 0`. -/
theorem thermalDiff_zero (τ : ℝ) : thermalDiff τ 0 = 0 := by
  rw [thermalDiff, add_zero, sub_zero, sub_self]

/-- `D_τ'(0) = 2τ`. -/
theorem hasDerivAt_thermalDiff (τ : ℝ) : HasDerivAt (thermalDiff τ) (2 * τ) 0 := by
  have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 0 := (hasDerivAt_id' (x := (0 : ℝ))).const_add 1
  have h2 : HasDerivAt (fun x : ℝ => 1 - x) (-1) 0 :=
    (hasDerivAt_id' (x := (0 : ℝ))).const_sub 1
  have h3 := h1.rpow_const (p := τ) (Or.inl (by norm_num))
  have h4 := h2.rpow_const (p := τ) (Or.inl (by norm_num))
  have h5 : HasDerivAt (thermalDiff τ)
      (1 * τ * (1 + 0 : ℝ) ^ (τ - 1) - -1 * τ * (1 - 0 : ℝ) ^ (τ - 1)) 0 := h3.sub h4
  have e : (1 * τ * (1 + 0 : ℝ) ^ (τ - 1) - -1 * τ * (1 - 0 : ℝ) ^ (τ - 1)) = 2 * τ := by
    rw [add_zero, sub_zero, Real.one_rpow]; ring
  rwa [e] at h5

/-- `D_τ` is continuous for `τ ≥ 0`. -/
theorem continuous_thermalDiff {τ : ℝ} (hτ : 0 ≤ τ) : Continuous (thermalDiff τ) := by
  have h1 : Continuous (fun x : ℝ => (1 + x) ^ τ) :=
    (continuous_const.add continuous_id).rpow_const fun _ => Or.inr hτ
  have h2 : Continuous (fun x : ℝ => (1 - x) ^ τ) :=
    (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hτ
  exact h1.sub h2

/-- `D_τ(x) > 0` for `0 < x ≤ 1` and `τ > 0`. -/
theorem thermalDiff_pos {τ x : ℝ} (hτ0 : 0 < τ) (hx0 : 0 < x) (hx1 : x ≤ 1) :
    0 < thermalDiff τ x := by
  have h := Real.rpow_lt_rpow (by linarith : (0 : ℝ) ≤ 1 - x) (by linarith : 1 - x < 1 + x) hτ0
  rw [thermalDiff]
  exact sub_pos.mpr h

/-- The difference quotient `dslope D_τ 0` is continuous for `τ ≥ 0`. -/
theorem continuous_dslope_thermalDiff {τ : ℝ} (hτ : 0 ≤ τ) :
    Continuous (dslope (thermalDiff τ) 0) := by
  rw [← continuousOn_univ]
  exact (continuousOn_dslope Filter.univ_mem).mpr
    ⟨(continuous_thermalDiff hτ).continuousOn, (hasDerivAt_thermalDiff τ).differentiableAt⟩

/-- `dslope D_τ 0 0 = 2τ`. -/
theorem dslope_thermalDiff_zero (τ : ℝ) : dslope (thermalDiff τ) 0 0 = 2 * τ := by
  rw [dslope_same, (hasDerivAt_thermalDiff τ).deriv]

/-- `dslope D_τ 0 x = D_τ(x)/x` for `x ≠ 0`. -/
theorem dslope_thermalDiff_of_ne {τ x : ℝ} (hx : x ≠ 0) :
    dslope (thermalDiff τ) 0 x = thermalDiff τ x / x := by
  rw [dslope_of_ne _ hx, slope_def_field, thermalDiff_zero, sub_zero, sub_zero]

/-- On `[0, 1]`, `h_τ(x) = ((1 + x)^τ + (1 - x)^τ) / dslope D_τ 0 x - 1`: a quotient of
continuous functions with nonvanishing denominator. -/
theorem thermalIncrement_eq_dslope {τ x : ℝ} (hτ0 : 0 < τ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    thermalIncrement τ x = ((1 + x) ^ τ + (1 - x) ^ τ) / dslope (thermalDiff τ) 0 x - 1 := by
  obtain ⟨hx0, hx1⟩ := hx
  rcases hx0.eq_or_lt with rfl | hx0
  · have hτ : τ ≠ 0 := hτ0.ne'
    rw [dslope_thermalDiff_zero, thermalIncrement_zero, add_zero, sub_zero, Real.one_rpow]
    rw [div_sub_one (mul_ne_zero two_ne_zero hτ), div_eq_div_iff hτ (mul_ne_zero two_ne_zero hτ)]
    ring
  · rw [dslope_thermalDiff_of_ne hx0.ne', thermalIncrement_eq_of_pos hτ0 hx0 hx1, thermalDiff,
      div_div_eq_mul_div, mul_comm _ x, mul_div_assoc]

/-- `h_τ` is continuous on `[0, 1]` for `τ > 0`. -/
theorem continuousOn_thermalIncrement {τ : ℝ} (hτ0 : 0 < τ) :
    ContinuousOn (thermalIncrement τ) (Set.Icc 0 1) := by
  have hN : Continuous (fun x : ℝ => (1 + x) ^ τ + (1 - x) ^ τ) := by
    have h1 : Continuous (fun x : ℝ => (1 + x) ^ τ) :=
      (continuous_const.add continuous_id).rpow_const fun _ => Or.inr hτ0.le
    have h2 : Continuous (fun x : ℝ => (1 - x) ^ τ) :=
      (continuous_const.sub continuous_id).rpow_const fun _ => Or.inr hτ0.le
    exact h1.add h2
  have hne : ∀ x ∈ Set.Icc (0 : ℝ) 1, dslope (thermalDiff τ) 0 x ≠ 0 := by
    rintro x ⟨hx0, hx1⟩
    rcases hx0.eq_or_lt with rfl | hx0
    · rw [dslope_thermalDiff_zero]
      exact (mul_pos two_pos hτ0).ne'
    · rw [dslope_thermalDiff_of_ne hx0.ne']
      exact (div_pos (thermalDiff_pos hτ0 hx0 hx1) hx0).ne'
  have hG : ContinuousOn
      (fun x : ℝ => ((1 + x) ^ τ + (1 - x) ^ τ) / dslope (thermalDiff τ) 0 x - 1)
      (Set.Icc 0 1) :=
    (hN.continuousOn.div (continuous_dslope_thermalDiff hτ0.le).continuousOn hne).sub
      continuousOn_const
  exact hG.congr fun x hx => thermalIncrement_eq_dslope hτ0 hx

/-! ### Operator form (Lemma 4.3 for a positive contraction `d`) -/

section Operator

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- Lemma 4.3, functional-calculus form: if the spectrum of `a` lies in `[0, 1]`, then
`c_τ · cfc (x ↦ (1 - x²)^τ) a ≤ cfc h_τ a` (real continuous functional calculus). The left
factor is `R^{2τ}` for `R = (1 - a²)^{1/2}` (see `thermal_comparison`). The meaningful case is
`IsSelfAdjoint a`: otherwise both sides are `0` by the convention of `cfc`; `thermal_comparison`
assumes `0 ≤ d ≤ 1`, which includes self-adjointness. -/
theorem thermalConst_smul_cfc_le_cfc_thermalIncrement {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    {a : A} (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) :
    thermalConst τ • cfc (fun x : ℝ => (1 - x ^ 2) ^ τ) a ≤ cfc (thermalIncrement τ) a := by
  have hR : Continuous (fun x : ℝ => (1 - x ^ 2) ^ τ) :=
    (continuous_const.sub (continuous_pow 2)).rpow_const fun _ => Or.inr hτ0.le
  rw [← cfc_const_mul (thermalConst τ) (fun x : ℝ => (1 - x ^ 2) ^ τ) a hR.continuousOn]
  exact cfc_mono (fun x hx => thermalIncrement_ge hτ0 hτ1 (hspec hx))
    (continuous_const.mul hR).continuousOn ((continuousOn_thermalIncrement hτ0).mono hspec)

omit [PartialOrder A] [StarOrderedRing A] in
/-- `cfc (x ↦ 1 - x²) a = 1 - a²` for self-adjoint `a`. -/
theorem cfc_one_sub_sq {a : A} (ha : IsSelfAdjoint a) :
    cfc (fun x : ℝ => 1 - x ^ 2) a = 1 - a ^ 2 := by
  rw [cfc_sub (fun _ : ℝ => (1 : ℝ)) (fun x : ℝ => x ^ 2) a, cfc_const_one ℝ a ha,
    cfc_pow_id (R := ℝ) a 2 ha]

/-- `1 - a² ≥ 0` for self-adjoint `a` with `x² ≤ 1` on its spectrum. -/
theorem one_sub_sq_nonneg {a : A} (ha : IsSelfAdjoint a)
    (hspec : ∀ x ∈ spectrum ℝ a, x ^ 2 ≤ 1) : (0 : A) ≤ 1 - a ^ 2 := by
  rw [← cfc_one_sub_sq ha]
  exact cfc_nonneg fun x hx => sub_nonneg.mpr (hspec x hx)

/-- The real power `(1 - a²)^τ` of the positive element `1 - a²` (`CFC.rpow`) equals
`cfc (x ↦ (1 - x²)^τ) a`, for self-adjoint `a` with `x² ≤ 1` on its spectrum and `τ ≥ 0`. -/
theorem one_sub_sq_rpow_eq_cfc {τ : ℝ} (hτ : 0 ≤ τ) {a : A} (ha : IsSelfAdjoint a)
    (hspec : ∀ x ∈ spectrum ℝ a, x ^ 2 ≤ 1) :
    (1 - a ^ 2) ^ τ = cfc (fun x : ℝ => (1 - x ^ 2) ^ τ) a := by
  have hf : Continuous (fun x : ℝ => 1 - x ^ 2) := continuous_const.sub (continuous_pow 2)
  rw [CFC.rpow_eq_cfc_real (one_sub_sq_nonneg ha hspec), ← cfc_one_sub_sq ha,
    ← cfc_comp' (fun y : ℝ => y ^ τ) (fun x : ℝ => 1 - x ^ 2) a
      (Real.continuous_rpow_const hτ).continuousOn hf.continuousOn ha]

/-- `cfc (x ↦ (1 - x²)^τ) a = (cfc (x ↦ √(1 - x²)) a)^{2τ}` (`CFC.rpow`), for self-adjoint `a`
with `x² ≤ 1` on its spectrum and `τ ≥ 0`: the left side of the functional-calculus form is
`R^{2τ}` for `R = cfc (x ↦ √(1 - x²)) a`. -/
theorem cfc_one_sub_sq_rpow_eq_cfc_sqrt_rpow {τ : ℝ} (hτ : 0 ≤ τ) {a : A} (ha : IsSelfAdjoint a)
    (hspec : ∀ x ∈ spectrum ℝ a, x ^ 2 ≤ 1) :
    cfc (fun x : ℝ => (1 - x ^ 2) ^ τ) a
      = (cfc (fun x : ℝ => Real.sqrt (1 - x ^ 2)) a) ^ (2 * τ) := by
  have hs : Continuous (fun x : ℝ => Real.sqrt (1 - x ^ 2)) :=
    (continuous_const.sub (continuous_pow 2)).sqrt
  have h0 : (0 : A) ≤ cfc (fun x : ℝ => Real.sqrt (1 - x ^ 2)) a :=
    cfc_nonneg fun x _ => Real.sqrt_nonneg _
  rw [CFC.rpow_eq_cfc_real h0,
    ← cfc_comp' (fun y : ℝ => y ^ (2 * τ)) (fun x : ℝ => Real.sqrt (1 - x ^ 2)) a
      (Real.continuous_rpow_const (by linarith)).continuousOn hs.continuousOn ha]
  refine cfc_congr fun x hx => ?_
  have h1 : 0 ≤ 1 - x ^ 2 := sub_nonneg.mpr (hspec x hx)
  change (1 - x ^ 2) ^ τ = Real.sqrt (1 - x ^ 2) ^ (2 * τ)
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul h1]
  congr 1
  ring

/-- `R^{2τ} = (1 - a²)^τ` for `R = (1 - a²)^{1/2}` (`CFC.sqrt`), if `1 - a² ≥ 0` and `τ ≥ 0`. -/
theorem sqrt_one_sub_sq_rpow {τ : ℝ} (hτ : 0 ≤ τ) {a : A} (h0 : (0 : A) ≤ 1 - a ^ 2) :
    CFC.sqrt (1 - a ^ 2) ^ (2 * τ) = (1 - a ^ 2) ^ τ := by
  rw [CFC.sqrt_eq_rpow, CFC.rpow_rpow_of_exponent_nonneg (1 - a ^ 2) (1 / 2) (2 * τ)
    (by norm_num) (by linarith) h0]
  congr 1
  ring

/-- **Lemma 4.3 (thermal comparison), operator form.** Let `d` be a positive contraction
(`0 ≤ d ≤ 1`) in a unital C⋆-algebra, `R = (1 - d²)^{1/2}` (`CFC.sqrt`) and
`H_τ(I) = h_τ(d) = d coth(τ artanh d) - 1` (continuous functional calculus with the
continuous extension `thermalIncrement`). Then `H_τ(I) ≥ c_τ R^{2τ}` for `0 < τ < 1`, where
`R^{2τ}` is the real power (`CFC.rpow`) of the positive element `R`. -/
theorem thermal_comparison {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {d : A} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) :
    thermalConst τ • CFC.sqrt (1 - d ^ 2) ^ (2 * τ) ≤ cfc (thermalIncrement τ) d := by
  have hsa : IsSelfAdjoint d := IsSelfAdjoint.of_nonneg hd0
  have hspec : spectrum ℝ d ⊆ Set.Icc 0 1 := fun x hx =>
    ⟨spectrum_nonneg_of_nonneg hd0 hx, (CFC.le_one_iff (R := ℝ) d hsa).mp hd1 x hx⟩
  have hsq : ∀ x ∈ spectrum ℝ d, x ^ 2 ≤ 1 := fun x hx => by
    obtain ⟨h0, h1⟩ := hspec hx
    nlinarith
  rw [sqrt_one_sub_sq_rpow hτ0.le (one_sub_sq_nonneg hsa hsq),
    one_sub_sq_rpow_eq_cfc hτ0.le hsa hsq]
  exact thermalConst_smul_cfc_le_cfc_thermalIncrement hτ0 hτ1 hspec

/-- Lemma 4.3, operator form, with the contraction hypothesis stated as `‖d‖ ≤ 1`. -/
theorem thermal_comparison_of_norm_le_one {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {d : A}
    (hd0 : 0 ≤ d) (hd1 : ‖d‖ ≤ 1) :
    thermalConst τ • CFC.sqrt (1 - d ^ 2) ^ (2 * τ) ≤ cfc (thermalIncrement τ) d :=
  thermal_comparison hτ0 hτ1 hd0 ((CStarAlgebra.norm_le_one_iff_of_nonneg d hd0).mp hd1)

/-- `H_τ(I) = h_τ(d) ≥ 0`: the functional calculus of `h_τ` gives a positive element when the
spectrum of `d` lies in `[0, 1]` and `0 < τ < 1` (for non-self-adjoint `a` the left side is `0`
by the
convention of `cfc`, so the meaningful case is `IsSelfAdjoint a`). -/
theorem cfc_thermalIncrement_nonneg {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {a : A}
    (hspec : spectrum ℝ a ⊆ Set.Icc 0 1) : 0 ≤ cfc (thermalIncrement τ) a :=
  cfc_nonneg fun _ hx => thermalIncrement_nonneg hτ0 hτ1 (hspec hx)

end Operator

/-- Lemma 4.3, operator form, for bounded operators on a complex Hilbert space
(`0 ≤ d ≤ 1` in the Loewner order). -/
theorem thermal_comparison_clm {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {τ : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1) {d : H →L[ℂ] H} (hd0 : 0 ≤ d)
    (hd1 : d ≤ 1) :
    thermalConst τ • CFC.sqrt (1 - d ^ 2) ^ (2 * τ) ≤ cfc (thermalIncrement τ) d :=
  thermal_comparison hτ0 hτ1 hd0 hd1

end VacuumBellSeparation
