/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.Cutfast.Distances
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Entropy dissipation and the Bregman form of the relative entropy
-/

@[expose] public section

open MeasureTheory Filter Topology Metric Real
open scoped ENNReal InnerProductSpace BoundedContinuousFunction MatrixOrder

namespace Cutfast

/-- The entropy dissipation identity `d/dt Hₘ(v(t) | v_∞) = -Iₘ(v(t) | v_∞)` along the solution
(the Fisher information is finite). -/
theorem relEntropy_hasDerivAt' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (h2 : (d : ℝ) / (d + 2) < m) (x₀ : E d) {t : ℝ} (ht : 0 < t) :
    fisherInfo m (solution d m x₀ t) ≠ ⊤ ∧
    HasDerivAt (fun s => relEntropy m (solution d m x₀ s) (equilibrium d m))
      (-(fisherInfo m (solution d m x₀ t)).toReal) t := by
  have h : Admissible d m := ⟨hd, hm0, hm1, hmd⟩
  rw [fisherInfo_solution h h2 x₀ ht]
  refine ⟨ENNReal.ofReal_ne_top, ?_⟩
  set A := alpha d m with hAdef
  set M := eqSecondMoment d m
  have hA : 0 < A := alpha_pos h
  have hM := (eqSecondMoment_pos h h2).le
  have hκ : (d : ℝ) * (1 - m) = 2 - 1 / A := by
    rw [hAdef, alpha, one_div_one_div]; ring
  have hκ0 : (d : ℝ) * (1 - m) ≠ 0 := by
    have : (0 : ℝ) < d := by exact_mod_cast hd
    exact mul_ne_zero this.ne' (sub_ne_zero.2 (Ne.symm hm1))
  set κ := (d : ℝ) * (1 - m)
  set w := 1 - exp (-t / A) with hw
  have hw0 : 0 < w := Barenblatt.one_sub_exp_pos h ht
  have hat : scaleFactor d m t = w ^ A := rfl
  have ha0 : 0 < w ^ A := rpow_pos_of_pos hw0 A
  -- derivatives of the pieces
  have hdw : HasDerivAt (fun s => 1 - exp (-s / A)) (-(exp (-t / A) * (-1 / A))) t :=
    ((hasDerivAt_neg t).div_const A).exp.const_sub 1
  have hda := hdw.rpow_const (p := A) (Or.inl hw0.ne')
  have hdak := hda.rpow_const (p := κ) (Or.inl ha0.ne')
  have hda2 := hda.pow 2
  have hde := (((hasDerivAt_neg t).exp).pow 2).mul_const (‖x₀‖ ^ 2) |>.div_const 2
  have hF := ((((hdak.const_sub 1).div_const κ).sub ((hda2.const_sub 1).div_const 2)).const_mul
    M).add hde
  have hev : (fun s => relEntropy m (solution d m x₀ s) (equilibrium d m)) =ᶠ[𝓝 t]
      fun s => M * ((1 - ((1 - exp (-s / A)) ^ A) ^ κ) / κ -
        (1 - ((1 - exp (-s / A)) ^ A) ^ 2) / 2) + (exp (-s)) ^ 2 * ‖x₀‖ ^ 2 / 2 := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    rw [relEntropy_solution h h2 x₀ hs, entropyProfile]
    rfl
  refine (hF.congr_of_eventuallyEq hev).congr_deriv ?_
  have hnn : 0 ≤ (w ^ A) ^ 2 * (1 - (w ^ A) ^ (-1 / A)) ^ 2 * M + exp (-t) ^ 2 * ‖x₀‖ ^ 2 := by
    positivity
  rw [hat, ENNReal.toReal_ofReal hnn]
  have h1 : (w ^ A) ^ (κ - 1) = w ^ A / w := by
    rw [← rpow_mul hw0.le, hκ, show A * (2 - 1 / A - 1) = A - 1 by field_simp; ring,
      rpow_sub_one hw0.ne']
  have h2' : (w ^ A) ^ (-1 / A) = w⁻¹ := by
    rw [← rpow_mul hw0.le, show A * (-1 / A) = -1 by field_simp, rpow_neg_one]
  have h3 : w ^ (A - 1) = w ^ A / w := rpow_sub_one hw0.ne' A
  have hu : exp (-t / A) = 1 - w := by rw [hw]; ring
  rw [← hw, h1, h2', h3, hu]
  field_simp
  ring

namespace Entropy

/-- Pointwise nonnegativity of the Bregman integrand of `x ↦ xᵐ/(m-1)` (Bernoulli). -/
theorem bregman_nonneg {m y z : ℝ} (hm0 : 0 < m) (hm1 : m ≠ 1) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hyz : z = 0 → y = 0) : 0 ≤ (y ^ m - z ^ m - m * z ^ (m - 1) * (y - z)) / (m - 1) := by
  rcases hz.eq_or_lt with hz0 | hz0
  · subst hz0; rw [hyz rfl]; simp
  have hs : -1 ≤ y / z - 1 := by have := div_nonneg hy hz0.le; linarith
  have hzm : 0 < z ^ m := rpow_pos_of_pos hz0 m
  have key : z ^ m * (1 + (y / z - 1)) ^ m = y ^ m := by
    rw [add_sub_cancel, div_rpow hy hz0.le, mul_div_cancel₀ _ hzm.ne']
  have key2 : z ^ m * (1 + m * (y / z - 1)) = z ^ m + m * z ^ (m - 1) * (y - z) := by
    rw [rpow_sub_one hz0.ne']
    field_simp
  rcases lt_or_gt_of_ne hm1 with h | h
  · have hb := rpow_one_add_le_one_add_mul_self hs hm0.le h.le
    have := mul_le_mul_of_nonneg_left hb hzm.le
    rw [key, key2] at this
    exact div_nonneg_of_nonpos (by linarith) (by linarith)
  · have hb := one_add_mul_self_le_rpow_one_add hs h.le
    have := mul_le_mul_of_nonneg_left hb hzm.le
    rw [key, key2] at this
    exact div_nonneg (by linarith) (by linarith)

variable {d : ℕ} {m : ℝ}

/-- On the support of `v_∞`, `v_∞^{m-1} = C + (1-m)/(2m)|x|²`; this gives the pointwise identity
`m v_∞^{m-1} (f - v_∞) = m C (f - v_∞) + (1-m)/2 |x|² (f - v_∞)` (both sides vanish off the
support, where `f = 0`). -/
theorem equilibrium_rpow_mul (h : Admissible d m) {f : E d → ℝ}
    (hsupp : 1 < m → ∀ x, equilibrium d m x = 0 → f x = 0) (x : E d) :
    m * equilibrium d m x ^ (m - 1) * (f x - equilibrium d m x) =
      m * equilibriumConst d m * (f x - equilibrium d m x) +
        (1 - m) / 2 * ‖x‖ ^ 2 * (f x - equilibrium d m x) := by
  have hm1 : m - 1 ≠ 0 := sub_ne_zero.2 h.2.2.1
  have hm0 := h.2.1
  have he := equilibrium_eq h x
  set q := equilibriumConst d m + (1 - m) / (2 * m) * ‖x‖ ^ 2 with hq
  rcases lt_or_ge 0 q with hq0 | hq0
  · rw [max_eq_left hq0.le] at he
    rw [he, ← rpow_mul hq0.le, one_div_mul_cancel hm1, rpow_one, hq]
    field_simp
  · rw [max_eq_right hq0, zero_rpow (one_div_ne_zero hm1)] at he
    rcases lt_or_gt_of_ne h.2.2.1 with hm | hm
    · exact absurd he (equilibrium_pos h hm x).ne'
    · rw [hsupp hm x he, he]; ring

end Entropy

/-- The finite-second-moment case of the Bregman form of the relative entropy,
equation (1.14) of arXiv:2503.11770v2. The equilibrium `v_∞` has finite second moment
when `m > d/(d+2)`. The probability density `f` has finite second moment and integrable
`fᵐ`, and it vanishes wherever `v_∞` vanishes when `m > 1`. Then
`Hₘ(f | v_∞) = 1/(m-1) ∫ (fᵐ - v_∞ᵐ - m v_∞^{m-1} (f - v_∞))` and `Hₘ(f | v_∞) ≥ 0`. -/
theorem relEntropy_eq_bregman' {d : ℕ} {m : ℝ} (hd : 1 ≤ d) (hm0 : 0 < m) (hm1 : m ≠ 1)
    (hmd : ((d : ℝ) - 2) / d < m) (h2 : (d : ℝ) / (d + 2) < m) (f : E d → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf : Integrable f) (hf1 : ∫ x, f x = 1)
    (hfm : Integrable fun x => f x ^ m) (hf2 : Integrable fun x => ‖x‖ ^ 2 * f x)
    (hsupp : 1 < m → ∀ x, equilibrium d m x = 0 → f x = 0) :
    Integrable (relEntropyDensity m f (equilibrium d m)) ∧
    relEntropy m f (equilibrium d m) =
      ∫ x, (f x ^ m - equilibrium d m x ^ m -
        m * equilibrium d m x ^ (m - 1) * (f x - equilibrium d m x)) / (m - 1) ∧
    0 ≤ relEntropy m f (equilibrium d m) := by
  have h : Admissible d m := ⟨hd, hm0, hm1, hmd⟩
  set v := equilibrium d m
  have hv := integrable_equilibrium h
  have hint : Integrable (relEntropyDensity m f v) := by
    have e : relEntropyDensity m f v = fun x =>
        (f x ^ m - v x ^ m - (1 - m) / 2 * (‖x‖ ^ 2 * f x) +
          (1 - m) / 2 * (‖x‖ ^ 2 * v x)) / (m - 1) := by
      funext x; simp only [relEntropyDensity]; ring
    rw [e]
    exact ((((hfm.sub (integrable_equilibrium_rpow h h2)).sub (hf2.const_mul _)).add
      ((integrable_sq_mul_equilibrium h h2).const_mul _)).div_const _)
  have hbreg : (fun x => (f x ^ m - v x ^ m - m * v x ^ (m - 1) * (f x - v x)) / (m - 1)) =
      fun x => relEntropyDensity m f v x - m * equilibriumConst d m / (m - 1) * (f x - v x) := by
    funext x
    rw [Entropy.equilibrium_rpow_mul h hsupp x, relEntropyDensity]
    have : m - 1 ≠ 0 := sub_ne_zero.2 hm1
    field_simp
    ring
  have heq : relEntropy m f v =
      ∫ x, (f x ^ m - v x ^ m - m * v x ^ (m - 1) * (f x - v x)) / (m - 1) := by
    have hi : Integrable fun x => m * equilibriumConst d m / (m - 1) * (f x - v x) :=
      (hf.sub hv).const_mul _
    rw [hbreg, integral_sub hint hi, integral_const_mul,
      integral_sub hf hv, hf1, integral_equilibrium h, sub_self, mul_zero, sub_zero, relEntropy]
  refine ⟨hint, heq, ?_⟩
  rw [heq]
  refine integral_nonneg fun x => Entropy.bregman_nonneg hm0 hm1 (hf0 x)
    (equilibrium_nonneg h x) fun hx => ?_
  rcases lt_or_gt_of_ne hm1 with hm | hm
  · exact absurd hx (equilibrium_pos h hm x).ne'
  · exact hsupp hm x hx

namespace Entropy

/-- `x ↦ (xᵐ - 1)/(m - 1)` is strictly convex on `[0,∞)` for `m > 0`, `m ≠ 1`. -/
theorem tsallis_strictConvexOn {m : ℝ} (hm0 : 0 < m) (hm1 : m ≠ 1) :
    StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => (x ^ m - 1) / (m - 1)) := by
  refine ⟨convex_Ici 0, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  rcases lt_or_gt_of_ne hm1 with h | h
  · have hc := (strictConcaveOn_rpow hm0 h).2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at hc
    have hn : m - 1 < 0 := by linarith
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have hi : (m - 1)⁻¹ < 0 := inv_lt_zero.2 hn
    nlinarith
  · have hc := (strictConvexOn_rpow h).2 hx hy hxy ha hb hab
    simp only [smul_eq_mul] at hc
    have hn : 0 < m - 1 := by linarith
    rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv]
    have hi : 0 < (m - 1)⁻¹ := inv_pos.2 hn
    nlinarith

/-- The correct form of the limit `m → 1`: `(xᵐ - x)/(m - 1) → x log x`. -/
theorem tsallis_tendsto {x : ℝ} (hx : 0 < x) :
    Tendsto (fun m : ℝ => (x ^ m - x) / (m - 1)) (𝓝[≠] 1) (𝓝 (x * log x)) := by
  have := hasDerivAt_iff_tendsto_slope.1 (hasStrictDerivAt_const_rpow hx 1).hasDerivAt
  rw [rpow_one] at this
  refine this.congr fun m => ?_
  rw [slope_def_field, rpow_one]

/-- The limit claimed in `tsallis_strictConvexOn_tendsto_log'` fails at `x = 2`:
`(2ᵐ - 1)/(m - 1)` does not tend to `log 2` as `m → 1` (its numerator tends to `1 ≠ 0`). -/
theorem tsallis_not_tendsto :
    ¬ Tendsto (fun m : ℝ => ((2 : ℝ) ^ m - 1) / (m - 1)) (𝓝[≠] 1) (𝓝 (log 2)) := by
  intro h
  have h2 : Tendsto (fun m : ℝ => (m - 1) * (((2 : ℝ) ^ m - 1) / (m - 1))) (𝓝[≠] 1) (𝓝 (0 * log 2))
    := by
    refine Tendsto.mul ?_ h
    have : Tendsto (fun m : ℝ => m - 1) (𝓝 1) (𝓝 (1 - 1)) := (continuous_id.sub
      continuous_const).tendsto 1
    rw [sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have h3 : Tendsto (fun m : ℝ => (2 : ℝ) ^ m - 1) (𝓝[≠] 1) (𝓝 ((2 : ℝ) ^ (1 : ℝ) - 1)) :=
    ((continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).sub continuous_const).tendsto 1
      |>.mono_left nhdsWithin_le_nhds
  have h4 : Tendsto (fun m : ℝ => (m - 1) * (((2 : ℝ) ^ m - 1) / (m - 1))) (𝓝[≠] 1)
      (𝓝 ((2 : ℝ) ^ (1 : ℝ) - 1)) := by
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with m hm
    have : m - 1 ≠ 0 := sub_ne_zero.2 hm
    field_simp
  have := tendsto_nhds_unique h2 h4
  norm_num at this

end Entropy

/-- The Tsallis profile is strictly convex on `[0,∞)` for `m > 0`, `m ≠ 1`.
For positive `x`, the centered quotient `(xᵐ - x)/(m - 1)` tends to `x * log x`
as `m → 1` (Section 1.3). -/
theorem tsallis_strictConvexOn_tendsto_log' {m : ℝ} (hm0 : 0 < m) (hm1 : m ≠ 1) :
    StrictConvexOn ℝ (Set.Ici 0) (fun x : ℝ => (x ^ m - 1) / (m - 1)) ∧
    ∀ x : ℝ, 0 < x → Tendsto (fun m : ℝ => (x ^ m - x) / (m - 1)) (𝓝[≠] 1) (𝓝 (x * log x)) := by
  exact ⟨Entropy.tsallis_strictConvexOn hm0 hm1, fun x hx => Entropy.tsallis_tendsto hx⟩

/-- The entropy dissipation identity `d/dt Hₘ(v(t) | v_∞) = -Iₘ(v(t) | v_∞)` along the solution
(the Fisher information is finite). -/
alias relEntropy_hasDerivAt := relEntropy_hasDerivAt'

/-- The finite-second-moment case of the Bregman form of the relative entropy,
equation (1.14) of arXiv:2503.11770v2. The equilibrium `v_∞` has finite second moment
when `m > d/(d+2)`. The probability density `f` has finite second moment and integrable
`fᵐ`, and it vanishes wherever `v_∞` vanishes when `m > 1`. Then
`Hₘ(f | v_∞) = 1/(m-1) ∫ (fᵐ - v_∞ᵐ - m v_∞^{m-1} (f - v_∞))` and `Hₘ(f | v_∞) ≥ 0`. -/
alias relEntropy_eq_bregman := relEntropy_eq_bregman'

/-- `x ↦ (xᵐ - 1)/(m - 1)` is strictly convex on `[0,∞)` for `m > 0`, `m ≠ 1`, and, up to the
affine term `(x - 1)/(m - 1)` (whose integral vanishes between probability densities), it gives
the classical entropy as `m → 1`: `(xᵐ - x)/(m - 1) → x log x` (Section 1.3). -/
alias tsallis_strictConvexOn_tendsto_log := tsallis_strictConvexOn_tendsto_log'

end Cutfast
