/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# IntrinsicScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The intrinsic length scale, the effective diffusivity, and the scale arithmetic

The superdiffusive displacement bounds are stated in terms of the length scale

`R(t) = ((ν t)^{2-γ} + c⋆ γ^{-1} t²)^{1/(2(2-γ))}`

associated with a time `t`, and are proved at a scale `3^m` above it.  The
comparison that carries the proof from the time variable to the scale variable
is between `R(t)²` and `σ_m t`, where `σ_m` is the effective diffusivity at
scale `3^m`.  This file proves that comparison.

The deterministic profile of the effective diffusivity is

`ν_eff(r) = (ν² + c⋆ γ^{-1} r^{2γ})^{1/2}`,

and the argument has two halves.  The first is exact and needs no smallness at
all: whenever `R(t) ≤ r`,

`|R(t)² - ν_eff(r) t| ≤ γ r²`.

Two elementary facts drive it.  The defining identity of `R(t)`, multiplied by
`R(t)^{2γ}`, gives the exact gap

`R(t)⁴ - (ν_eff(R(t)) t)² = R(t)^{2γ} (ν t)^{2-γ} - (ν t)²`,

and that gap is between `0` and `γ R(t)⁴` because `ν t ≤ R(t)²` and because
`u^γ - 1 ≤ γ u²` for every `u ≥ 1`.  The same inequality `u^γ - 1 ≤ γ u²`,
applied to `u = r / R(t)`, is what lets the scale `r` be arbitrarily far above
`R(t)` at the cost of the factor `r²` on the right.

The second half replaces `ν_eff(3^m)` by the effective diffusivity `σ_m` of
the renormalization theorem, which is within a relative error
`C γ^{1/2} |log γ|` of the profile.  Since `γ ≤ γ^{1/2} |log γ|` throughout the
admissible range of `γ`, the two halves combine into

`|R(t)² - σ_m t| ≤ (1 + 2C) γ^{1/2} |log γ| 3^{2m}`,

which is the displayed comparison, with the constant made explicit.

## Main definitions

* `intrinsicScale` — the length scale `R(t)`.
* `effectiveDiffusivity` — the profile `ν_eff(r)`.

## Main results

* `mul_le_intrinsicScale_sq` — `ν t ≤ R(t)²`.
* `abs_intrinsicScale_sq_sub_effectiveDiffusivity_mul_le` — the exact half,
  `|R(t)² - ν_eff(r) t| ≤ γ r²` for every `r ≥ R(t)`.
* `effectiveDiffusivity_mul_le_sq` — `ν_eff(r) t ≤ r²`, the same statement read
  as a comparison of the time `t` with the time scale of `r`.
* `abs_intrinsicScale_sq_sub_mul_le` — the displayed comparison with the
  effective diffusivity of the renormalization theorem in place of the profile.
* `effectiveDiffusivity_three_zpow` — the profile at a triadic scale, in the
  form in which the renormalization theorem states it.

## References

* ABK26, the superdiffusive displacement bounds of Section 5.4.
-/

namespace Algsuperdiff.Section5.Support

noncomputable section

variable {nu cstar gamma t : ℝ}

/-! ## 1. The two length-scale profiles -/

/-- **The intrinsic length scale** associated with a time `t`,
`R(t) = ((ν t)^{2-γ} + c⋆ γ^{-1} t²)^{1/(2(2-γ))}`. -/
def intrinsicScale (nu cstar gamma t : ℝ) : ℝ :=
  ((nu * t) ^ (2 - gamma) + cstar * gamma⁻¹ * t ^ (2 : ℕ)) ^ (2 * (2 - gamma))⁻¹

/-- **The effective diffusivity profile** at a length scale `r`,
`ν_eff(r) = (ν² + c⋆ γ^{-1} r^{2γ})^{1/2}`. -/
def effectiveDiffusivity (nu cstar gamma r : ℝ) : ℝ :=
  Real.sqrt (nu ^ (2 : ℕ) + cstar * gamma⁻¹ * r ^ (2 * gamma))

/-- The profile at a triadic scale, written with the exponent in the form used
by the renormalization theorem. -/
theorem effectiveDiffusivity_three_zpow (nu cstar gamma : ℝ) (m : ℤ) :
    effectiveDiffusivity nu cstar gamma ((3 : ℝ) ^ m) =
      Real.sqrt (nu ^ (2 : ℕ) + cstar * gamma⁻¹ * (3 : ℝ) ^ (2 * gamma * (m : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  rw [effectiveDiffusivity, ← Real.rpow_intCast (3 : ℝ) m, ← Real.rpow_mul h3.le]
  ring_nf

private theorem base_pos (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma) (ht : 0 < t) :
    0 < (nu * t) ^ (2 - gamma) + cstar * gamma⁻¹ * t ^ (2 : ℕ) := by
  have h1 : 0 < (nu * t) ^ (2 - gamma) := Real.rpow_pos_of_pos (by positivity) _
  have h2 : 0 < cstar * gamma⁻¹ * t ^ (2 : ℕ) := by positivity
  linarith only [h1, h2]

/-- The intrinsic scale is positive. -/
theorem intrinsicScale_pos (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (ht : 0 < t) : 0 < intrinsicScale nu cstar gamma t :=
  Real.rpow_pos_of_pos (base_pos hnu hcstar hgamma ht) _

/-- The effective diffusivity profile is nonnegative. -/
theorem effectiveDiffusivity_nonneg (nu cstar gamma r : ℝ) :
    0 ≤ effectiveDiffusivity nu cstar gamma r := Real.sqrt_nonneg _

/-- **The defining identity of the intrinsic scale**, read on its square:
`(R(t)²)^{2-γ} = (ν t)^{2-γ} + c⋆ γ^{-1} t²`. -/
theorem intrinsicScale_sq_rpow (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (hgamma2 : gamma < 2) (ht : 0 < t) :
    (intrinsicScale nu cstar gamma t ^ (2 : ℕ)) ^ (2 - gamma) =
      (nu * t) ^ (2 - gamma) + cstar * gamma⁻¹ * t ^ (2 : ℕ) := by
  have hB := base_pos hnu hcstar hgamma ht
  have hg : (0 : ℝ) < 2 - gamma := by linarith only [hgamma2]
  have hgne : (2 : ℝ) * (2 - gamma) ≠ 0 := by positivity
  rw [intrinsicScale, ← Real.rpow_natCast (((nu * t) ^ (2 - gamma) +
      cstar * gamma⁻¹ * t ^ (2 : ℕ)) ^ (2 * (2 - gamma))⁻¹) 2,
    ← Real.rpow_mul hB.le, ← Real.rpow_mul hB.le,
    show (2 * (2 - gamma))⁻¹ * ((2 : ℕ) : ℝ) * (2 - gamma) = 1 by
      push_cast
      field_simp]
  exact Real.rpow_one _

/-! ## 2. The elementary inequality behind both halves -/

/-- For `u ≥ 1` and `γ ∈ (0,1]`, `u^γ - 1 ≤ γ u²`.  This is the only place the
exponent `γ` is used quantitatively, and it is what makes both the comparison at
`R(t)` itself and the passage to a scale `r` above it cost exactly one factor
of `γ`. -/
private theorem rpow_sub_one_le_mul_sq {u : ℝ} (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hu : 1 ≤ u) : u ^ gamma - 1 ≤ gamma * u ^ (2 : ℕ) := by
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hlog : 0 ≤ Real.log u := Real.log_nonneg hu
  have hue : u ^ gamma = Real.exp (gamma * Real.log u) := by
    rw [Real.rpow_def_of_pos hu0, mul_comm]
  have hkey : Real.exp (gamma * Real.log u) - 1 ≤
      gamma * Real.log u * Real.exp (gamma * Real.log u) := by
    set y : ℝ := gamma * Real.log u with hy
    have h1 : -y + 1 ≤ Real.exp (-y) := Real.add_one_le_exp (-y)
    have hpos : (0 : ℝ) < Real.exp y := Real.exp_pos y
    have h2 : (1 - y) * Real.exp y ≤ Real.exp (-y) * Real.exp y :=
      mul_le_mul_of_nonneg_right (by linarith only [h1]) hpos.le
    have h3 : Real.exp (-y) * Real.exp y = 1 := by
      rw [← Real.exp_add]
      simp
    have h4 : (1 - y) * Real.exp y = Real.exp y - y * Real.exp y := by ring
    rw [h3, h4] at h2
    linarith only [h2]
  have hugle : u ^ gamma ≤ u := by
    calc u ^ gamma ≤ u ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hu hgamma1
      _ = u := Real.rpow_one u
  have hlogu : Real.log u ≤ u :=
    le_trans (Real.log_le_sub_one_of_pos hu0) (by linarith only)
  calc u ^ gamma - 1 = Real.exp (gamma * Real.log u) - 1 := by rw [hue]
    _ ≤ gamma * Real.log u * Real.exp (gamma * Real.log u) := hkey
    _ = gamma * Real.log u * u ^ gamma := by rw [hue]
    _ ≤ gamma * u * u :=
        mul_le_mul (mul_le_mul_of_nonneg_left hlogu hgamma.le) hugle
          (Real.rpow_nonneg hu0.le gamma) (by positivity)
    _ = gamma * u ^ (2 : ℕ) := by ring

/-- The two-sided estimate of the gap `Q^γ x^{2-γ} - x²` for `0 < x ≤ Q`. -/
private theorem rpow_gap_le {x Q : ℝ} (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1)
    (hx : 0 < x) (hxQ : x ≤ Q) :
    x ^ (2 : ℕ) ≤ Q ^ gamma * x ^ (2 - gamma) ∧
      Q ^ gamma * x ^ (2 - gamma) - x ^ (2 : ℕ) ≤ gamma * Q ^ (2 : ℕ) := by
  have hQ : 0 < Q := lt_of_lt_of_le hx hxQ
  have hu : 1 ≤ Q / x := (one_le_div hx).mpr hxQ
  have hx2 : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hxg : x ^ (2 - gamma) = x ^ (2 : ℕ) / x ^ gamma := by
    rw [Real.rpow_sub hx, hx2]
  have hkey : Q ^ gamma * x ^ (2 - gamma) = x ^ (2 : ℕ) * (Q / x) ^ gamma := by
    rw [Real.div_rpow hQ.le hx.le, hxg]
    ring
  have hone : (1 : ℝ) ≤ (Q / x) ^ gamma := by
    calc (1 : ℝ) = (1 : ℝ) ^ gamma := (Real.one_rpow gamma).symm
      _ ≤ (Q / x) ^ gamma := Real.rpow_le_rpow (by norm_num) hu hgamma.le
  refine ⟨?_, ?_⟩
  · rw [hkey]
    nth_rewrite 1 [← mul_one (x ^ (2 : ℕ))]
    exact mul_le_mul_of_nonneg_left hone (by positivity)
  · have hb := rpow_sub_one_le_mul_sq hgamma hgamma1 hu
    have hsplit : x ^ (2 : ℕ) * (Q / x) ^ gamma - x ^ (2 : ℕ) =
        x ^ (2 : ℕ) * ((Q / x) ^ gamma - 1) := by ring
    rw [hkey, hsplit]
    calc x ^ (2 : ℕ) * ((Q / x) ^ gamma - 1)
        ≤ x ^ (2 : ℕ) * (gamma * (Q / x) ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = gamma * Q ^ (2 : ℕ) := by
          field_simp

/-! ## 3. The comparison at the intrinsic scale itself -/

/-- `ν t ≤ R(t)²`: the intrinsic scale is above the diffusive scale. -/
theorem mul_le_intrinsicScale_sq (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (hgamma2 : gamma < 2) (ht : 0 < t) :
    nu * t ≤ intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by
  have hg : (0 : ℝ) < 2 - gamma := by linarith only [hgamma2]
  have hRpos := intrinsicScale_pos hnu hcstar hgamma ht
  have hQpos : 0 < intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by positivity
  have hQrpow := intrinsicScale_sq_rpow hnu hcstar hgamma hgamma2 ht
  have h2 : (0 : ℝ) ≤ cstar * gamma⁻¹ * t ^ (2 : ℕ) := by positivity
  have hle : (nu * t) ^ (2 - gamma) ≤
      (intrinsicScale nu cstar gamma t ^ (2 : ℕ)) ^ (2 - gamma) := by
    rw [hQrpow]
    linarith only [h2]
  exact (Real.rpow_le_rpow_iff (by positivity) hQpos.le hg).mp hle

/-- **The exact gap at the intrinsic scale.**  The square of the intrinsic scale
exceeds the diffusive displacement `ν_eff(R(t)) t` by the amount
`R(t)^{2γ}(ν t)^{2-γ} - (ν t)²`. -/
private theorem intrinsic_gap_eq (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (hgamma2 : gamma < 2) (ht : 0 < t) :
    (intrinsicScale nu cstar gamma t ^ (2 : ℕ)) ^ (2 : ℕ)
        - (effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t) * t) ^ (2 : ℕ)
      = (intrinsicScale nu cstar gamma t ^ (2 : ℕ)) ^ gamma * (nu * t) ^ (2 - gamma)
        - (nu * t) ^ (2 : ℕ) := by
  have hRpos := intrinsicScale_pos hnu hcstar hgamma ht
  set R : ℝ := intrinsicScale nu cstar gamma t with hR
  set Q : ℝ := R ^ (2 : ℕ) with hQdef
  have hQpos : 0 < Q := by rw [hQdef]; positivity
  have hQrpow : Q ^ (2 - gamma) = (nu * t) ^ (2 - gamma) + cstar * gamma⁻¹ * t ^ (2 : ℕ) :=
    intrinsicScale_sq_rpow hnu hcstar hgamma hgamma2 ht
  have hRQ : R ^ (2 * gamma) = Q ^ gamma := by
    rw [hQdef, ← Real.rpow_natCast R 2, ← Real.rpow_mul hRpos.le]
    norm_num
  have hE2 : (effectiveDiffusivity nu cstar gamma R * t) ^ (2 : ℕ)
      = (nu ^ (2 : ℕ) + cstar * gamma⁻¹ * Q ^ gamma) * t ^ (2 : ℕ) := by
    rw [mul_pow, effectiveDiffusivity, hRQ, Real.sq_sqrt (by positivity)]
  have hQ2 : Q ^ (2 : ℕ) = Q ^ gamma * Q ^ (2 - gamma) := by
    rw [← Real.rpow_add hQpos, show gamma + (2 - gamma) = ((2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast]
  rw [hQ2, hQrpow, hE2]
  ring

/-- The diffusive displacement at the intrinsic scale never exceeds the square of
that scale. -/
private theorem effectiveDiffusivity_intrinsic_mul_le (hnu : 0 < nu) (hcstar : 0 < cstar)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) (ht : 0 < t) :
    effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t) * t ≤
      intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by
  have hgamma2 : gamma < 2 := by linarith only [hgamma1]
  have hRpos := intrinsicScale_pos hnu hcstar hgamma ht
  have hQpos : 0 < intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by positivity
  have hx : 0 < nu * t := by positivity
  have hxQ := mul_le_intrinsicScale_sq hnu hcstar hgamma hgamma2 ht
  have hgap := intrinsic_gap_eq hnu hcstar hgamma hgamma2 ht
  have hlow := (rpow_gap_le hgamma hgamma1 hx hxQ).1
  have hsq : (effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t) * t)
      ^ (2 : ℕ) ≤ (intrinsicScale nu cstar gamma t ^ (2 : ℕ)) ^ (2 : ℕ) := by
    linarith only [hgap, hlow]
  exact le_of_pow_le_pow_left₀ two_ne_zero hQpos.le hsq

/-- The diffusive displacement at the intrinsic scale is within a relative `γ` of
the square of that scale. -/
private theorem intrinsic_sub_effectiveDiffusivity_mul_le (hnu : 0 < nu) (hcstar : 0 < cstar)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) (ht : 0 < t) :
    intrinsicScale nu cstar gamma t ^ (2 : ℕ)
        - effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t) * t ≤
      gamma * intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by
  have hgamma2 : gamma < 2 := by linarith only [hgamma1]
  have hRpos := intrinsicScale_pos hnu hcstar hgamma ht
  have hQpos : 0 < intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by positivity
  have hx : 0 < nu * t := by positivity
  have hxQ := mul_le_intrinsicScale_sq hnu hcstar hgamma hgamma2 ht
  have hgap := intrinsic_gap_eq hnu hcstar hgamma hgamma2 ht
  have hup := (rpow_gap_le hgamma hgamma1 hx hxQ).2
  have hEnn : 0 ≤ effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t) * t := by
    have := effectiveDiffusivity_nonneg nu cstar gamma (intrinsicScale nu cstar gamma t)
    positivity
  -- `(E t)² ≥ (1-γ) Q²`, hence `E t ≥ (1-γ) Q` and the claim.
  have hsq : ((1 - gamma) * intrinsicScale nu cstar gamma t ^ (2 : ℕ)) ^ (2 : ℕ) ≤
      (effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t) * t) ^ (2 : ℕ) := by
    have hfac : ((1 - gamma) * intrinsicScale nu cstar gamma t ^ (2 : ℕ)) ^ (2 : ℕ) =
        (1 - gamma) ^ (2 : ℕ) * (intrinsicScale nu cstar gamma t ^ (2 : ℕ)) ^ (2 : ℕ) := by
      ring
    have hsmall : (1 - gamma) ^ (2 : ℕ) ≤ 1 - gamma := by nlinarith only [hgamma, hgamma1]
    have hQ2 : 0 ≤ (intrinsicScale nu cstar gamma t ^ (2 : ℕ)) ^ (2 : ℕ) := by positivity
    nlinarith only [hgap, hup, hfac, hsmall, hQ2]
  have hle : (1 - gamma) * intrinsicScale nu cstar gamma t ^ (2 : ℕ) ≤
      effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t) * t :=
    le_of_pow_le_pow_left₀ two_ne_zero hEnn hsq
  linarith only [hle]

/-! ## 4. The comparison at a scale above the intrinsic scale -/

private theorem effectiveDiffusivity_mono {r s : ℝ} (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (hr : 0 < r) (hrs : r ≤ s) :
    effectiveDiffusivity nu cstar gamma r ≤ effectiveDiffusivity nu cstar gamma s := by
  refine Real.sqrt_le_sqrt ?_
  have := Real.rpow_le_rpow hr.le hrs (by positivity : (0 : ℝ) ≤ 2 * gamma)
  have hc : (0 : ℝ) ≤ cstar * gamma⁻¹ := by positivity
  nlinarith only [this, hc]

private theorem effectiveDiffusivity_le_ratio_rpow_mul {r s : ℝ}
    (hgamma : 0 < gamma) (hr : 0 < r) (hrs : r ≤ s) :
    effectiveDiffusivity nu cstar gamma s ≤
      (s / r) ^ gamma * effectiveDiffusivity nu cstar gamma r := by
  have hs : 0 < s := lt_of_lt_of_le hr hrs
  have hu : 1 ≤ s / r := (one_le_div hr).mpr hrs
  have hsqrt : Real.sqrt ((s / r) ^ (2 * gamma)) = (s / r) ^ gamma := by
    rw [show (2 : ℝ) * gamma = gamma * 2 by ring, Real.rpow_mul (by positivity),
      show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      Real.sqrt_sq (by positivity)]
  have hprod : (s / r) ^ (2 * gamma) * r ^ (2 * gamma) = s ^ (2 * gamma) := by
    rw [← Real.mul_rpow (by positivity) hr.le, div_mul_cancel₀ _ hr.ne']
  have hone : (1 : ℝ) ≤ (s / r) ^ (2 * gamma) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (2 * gamma) := (Real.one_rpow _).symm
      _ ≤ (s / r) ^ (2 * gamma) := Real.rpow_le_rpow (by norm_num) hu (by positivity)
  have hnu2 : (0 : ℝ) ≤ nu ^ (2 : ℕ) := by positivity
  have hstep : nu ^ (2 : ℕ) + cstar * gamma⁻¹ * s ^ (2 * gamma) ≤
      (s / r) ^ (2 * gamma) * (nu ^ (2 : ℕ) + cstar * gamma⁻¹ * r ^ (2 * gamma)) := by
    have hexp : (s / r) ^ (2 * gamma) * (nu ^ (2 : ℕ) + cstar * gamma⁻¹ * r ^ (2 * gamma)) =
        (s / r) ^ (2 * gamma) * nu ^ (2 : ℕ) + cstar * gamma⁻¹ * s ^ (2 * gamma) := by
      rw [mul_add]
      congr 1
      rw [← hprod]
      ring
    rw [hexp]
    nlinarith only [hone, hnu2]
  calc effectiveDiffusivity nu cstar gamma s
      ≤ Real.sqrt ((s / r) ^ (2 * gamma) * (nu ^ (2 : ℕ) + cstar * gamma⁻¹ * r ^ (2 * gamma))) :=
        Real.sqrt_le_sqrt hstep
    _ = (s / r) ^ gamma * effectiveDiffusivity nu cstar gamma r := by
        rw [Real.sqrt_mul (by positivity), hsqrt, effectiveDiffusivity]

/-- **The scale arithmetic, exact half.**  At every length scale `r` above the
intrinsic scale, the square of the intrinsic scale and the displacement
`ν_eff(r) t` differ by at most `γ r²`. -/
theorem abs_intrinsicScale_sq_sub_effectiveDiffusivity_mul_le (hnu : 0 < nu) (hcstar : 0 < cstar)
    (hgamma : 0 < gamma) (hgamma1 : gamma ≤ 1) (ht : 0 < t) {r : ℝ}
    (hr : intrinsicScale nu cstar gamma t ≤ r) :
    |intrinsicScale nu cstar gamma t ^ (2 : ℕ) - effectiveDiffusivity nu cstar gamma r * t| ≤
      gamma * r ^ (2 : ℕ) := by
  have hRpos := intrinsicScale_pos hnu hcstar hgamma ht
  have hrpos : 0 < r := lt_of_lt_of_le hRpos hr
  have hQpos : 0 < intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by positivity
  have hQr : intrinsicScale nu cstar gamma t ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := by
    exact pow_le_pow_left₀ hRpos.le hr 2
  have hmono := effectiveDiffusivity_mono (nu := nu) hcstar hgamma hRpos hr
  have hratio := effectiveDiffusivity_le_ratio_rpow_mul (nu := nu) (cstar := cstar) hgamma hRpos hr
  have hEint := effectiveDiffusivity_intrinsic_mul_le hnu hcstar hgamma hgamma1 ht
  have hEgap := intrinsic_sub_effectiveDiffusivity_mul_le hnu hcstar hgamma hgamma1 ht
  rw [abs_le]
  refine ⟨?_, ?_⟩
  · -- `ν_eff(r) t - R(t)² ≤ γ r²`
    have hu : 1 ≤ r / intrinsicScale nu cstar gamma t := (one_le_div hRpos).mpr hr
    have hb := rpow_sub_one_le_mul_sq hgamma hgamma1 hu
    have hup : effectiveDiffusivity nu cstar gamma r * t ≤
        (r / intrinsicScale nu cstar gamma t) ^ gamma *
          intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by
      calc effectiveDiffusivity nu cstar gamma r * t
          ≤ ((r / intrinsicScale nu cstar gamma t) ^ gamma *
              effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t)) * t :=
            mul_le_mul_of_nonneg_right hratio ht.le
        _ = (r / intrinsicScale nu cstar gamma t) ^ gamma *
              (effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t) * t) := by
            ring
        _ ≤ (r / intrinsicScale nu cstar gamma t) ^ gamma *
              intrinsicScale nu cstar gamma t ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_left hEint (by positivity)
    have hexp : intrinsicScale nu cstar gamma t ^ (2 : ℕ) *
        (gamma * (r / intrinsicScale nu cstar gamma t) ^ (2 : ℕ)) = gamma * r ^ (2 : ℕ) := by
      field_simp
    nlinarith only [hup, hb, hQpos, hexp]
  · -- `R(t)² - ν_eff(r) t ≤ γ r²`
    have hstep : intrinsicScale nu cstar gamma t ^ (2 : ℕ) -
        effectiveDiffusivity nu cstar gamma r * t ≤
          gamma * intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by
      have : effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t) * t ≤
          effectiveDiffusivity nu cstar gamma r * t :=
        mul_le_mul_of_nonneg_right hmono ht.le
      linarith only [hEgap, this]
    have hmul : gamma * intrinsicScale nu cstar gamma t ^ (2 : ℕ) ≤ gamma * r ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hQr hgamma.le
    linarith only [hstep, hmul]

/-- **The displacement never exceeds the square of the scale.**  At every length
scale `r` above the intrinsic scale, `ν_eff(r) t ≤ r²`. -/
theorem effectiveDiffusivity_mul_le_sq (hnu : 0 < nu) (hcstar : 0 < cstar) (hgamma : 0 < gamma)
    (hgamma1 : gamma ≤ 1) (ht : 0 < t) {r : ℝ} (hr : intrinsicScale nu cstar gamma t ≤ r) :
    effectiveDiffusivity nu cstar gamma r * t ≤ r ^ (2 : ℕ) := by
  have hRpos := intrinsicScale_pos hnu hcstar hgamma ht
  have hrpos : 0 < r := lt_of_lt_of_le hRpos hr
  have hQpos : 0 < intrinsicScale nu cstar gamma t ^ (2 : ℕ) := by positivity
  have hu : 1 ≤ r / intrinsicScale nu cstar gamma t := (one_le_div hRpos).mpr hr
  have hratio := effectiveDiffusivity_le_ratio_rpow_mul (nu := nu) (cstar := cstar) hgamma hRpos hr
  have hEint := effectiveDiffusivity_intrinsic_mul_le hnu hcstar hgamma hgamma1 ht
  have hpow : (r / intrinsicScale nu cstar gamma t) ^ gamma ≤
      (r / intrinsicScale nu cstar gamma t) ^ (2 : ℕ) := by
    calc (r / intrinsicScale nu cstar gamma t) ^ gamma
        ≤ (r / intrinsicScale nu cstar gamma t) ^ (2 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hu (by linarith only [hgamma1])
      _ = (r / intrinsicScale nu cstar gamma t) ^ (2 : ℕ) := by
          rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hfinal : (r / intrinsicScale nu cstar gamma t) ^ (2 : ℕ) *
      intrinsicScale nu cstar gamma t ^ (2 : ℕ) = r ^ (2 : ℕ) := by
    field_simp
  calc effectiveDiffusivity nu cstar gamma r * t
      ≤ ((r / intrinsicScale nu cstar gamma t) ^ gamma *
          effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t)) * t :=
        mul_le_mul_of_nonneg_right hratio ht.le
    _ = (r / intrinsicScale nu cstar gamma t) ^ gamma *
          (effectiveDiffusivity nu cstar gamma (intrinsicScale nu cstar gamma t) * t) := by ring
    _ ≤ (r / intrinsicScale nu cstar gamma t) ^ gamma *
          intrinsicScale nu cstar gamma t ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_left hEint (by positivity)
    _ ≤ (r / intrinsicScale nu cstar gamma t) ^ (2 : ℕ) *
          intrinsicScale nu cstar gamma t ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right hpow hQpos.le
    _ = r ^ (2 : ℕ) := hfinal

/-! ## 5. The comparison with the effective diffusivity of the renormalization -/

/-- On the admissible range of the coupling, `1 ≤ |log γ|`. -/
theorem one_le_abs_log (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4) :
    1 ≤ |Real.log gamma| := by
  have hlog4 : (1 : ℝ) < Real.log 4 := by
    have h := Real.exp_one_lt_d9
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log 4 := Real.log_lt_log (Real.exp_pos 1) (by linarith only [h])
  have hlq : Real.log gamma ≤ Real.log (4 : ℝ)⁻¹ :=
    Real.log_le_log hgamma (by linarith only [hgamma4])
  have hlq2 : Real.log gamma ≤ -Real.log 4 := by
    rw [← Real.log_inv 4]
    exact hlq
  have hneg : Real.log gamma < 0 := by linarith only [hlq2, hlog4]
  rw [abs_of_neg hneg]
  linarith only [hlq2, hlog4]

/-- On the admissible range of the coupling, `1 ≤ |log γ|^{1/2}`. -/
theorem one_le_sqrt_abs_log (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4) :
    1 ≤ Real.sqrt |Real.log gamma| := by
  have h := one_le_abs_log hgamma hgamma4
  calc (1 : ℝ) = Real.sqrt 1 := (Real.sqrt_one).symm
    _ ≤ Real.sqrt |Real.log gamma| := Real.sqrt_le_sqrt h

/-- On the admissible range of the coupling, `γ ≤ γ^{1/2} |log γ|`. -/
private theorem le_sqrt_mul_abs_log (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4) :
    gamma ≤ Real.sqrt gamma * |Real.log gamma| := by
  have hge : (1 : ℝ) ≤ |Real.log gamma| := one_le_abs_log hgamma hgamma4
  have hsqrt : Real.sqrt gamma ≤ 1 / 2 := by
    have : Real.sqrt gamma ≤ Real.sqrt (1 / 4) := Real.sqrt_le_sqrt hgamma4
    rwa [show (1 / 4 : ℝ) = (1 / 2) ^ (2 : ℕ) by norm_num,
      Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 2)] at this
  have hmul : Real.sqrt gamma * Real.sqrt gamma = gamma := Real.mul_self_sqrt hgamma.le
  have hsg : 0 ≤ Real.sqrt gamma := Real.sqrt_nonneg gamma
  nlinarith only [hmul, hge, hsqrt, hsg]

/-- **The scale arithmetic.**  Let `σ` be an effective diffusivity within the
relative error `C γ^{1/2} |log γ|` of the profile at a length scale `r` above the
intrinsic scale.  Then the square of the intrinsic scale and the displacement
`σ t` differ by at most `(1 + 2C) γ^{1/2} |log γ| r²`.

The relative error of the renormalization theorem is exactly the hypothesis
`hprofile`, and the smallness hypothesis `hsmall` is the statement that the
relative error is at most one half, so that `σ` and the profile are comparable.
The `γ` produced by the exact half is absorbed into the displayed factor by
`γ ≤ γ^{1/2} |log γ|`. -/
theorem abs_intrinsicScale_sq_sub_mul_le (hnu : 0 < nu) (hcstar : 0 < cstar)
    (hgamma : 0 < gamma) (hgamma4 : gamma ≤ 1 / 4) (ht : 0 < t) {r : ℝ}
    (hr : intrinsicScale nu cstar gamma t ≤ r) {sigmaBar C : ℝ} (hsigma : 0 < sigmaBar)
    (hC : 0 ≤ C) (hsmall : C * Real.sqrt gamma * |Real.log gamma| ≤ 1 / 2)
    (hprofile : |sigmaBar - effectiveDiffusivity nu cstar gamma r| ≤
      C * Real.sqrt gamma * |Real.log gamma| * sigmaBar) :
    |intrinsicScale nu cstar gamma t ^ (2 : ℕ) - sigmaBar * t| ≤
      (1 + 2 * C) * Real.sqrt gamma * |Real.log gamma| * r ^ (2 : ℕ) := by
  have hgamma1 : gamma ≤ 1 := by linarith only [hgamma4]
  have hRpos := intrinsicScale_pos hnu hcstar hgamma ht
  have hrpos : 0 < r := lt_of_lt_of_le hRpos hr
  have hprof := abs_intrinsicScale_sq_sub_effectiveDiffusivity_mul_le hnu hcstar hgamma hgamma1 ht
    hr
  have hEle := effectiveDiffusivity_mul_le_sq hnu hcstar hgamma hgamma1 ht hr
  have hEnn := effectiveDiffusivity_nonneg nu cstar gamma r
  set eps : ℝ := C * Real.sqrt gamma * |Real.log gamma| with heps
  have hepsnn : 0 ≤ eps := by
    rw [heps]
    positivity
  rw [abs_le] at hprofile
  -- `σ ≤ 2 ν_eff(r)`
  have hcomp : sigmaBar ≤ 2 * effectiveDiffusivity nu cstar gamma r := by
    nlinarith only [hprofile.2, hsmall, hsigma, hepsnn]
  have hgap : |sigmaBar * t - effectiveDiffusivity nu cstar gamma r * t| ≤
      2 * eps * r ^ (2 : ℕ) := by
    have habs1 : |sigmaBar - effectiveDiffusivity nu cstar gamma r| ≤ eps * sigmaBar := by
      rw [abs_le]
      exact hprofile
    have hprod : |sigmaBar * t - effectiveDiffusivity nu cstar gamma r * t| =
        |sigmaBar - effectiveDiffusivity nu cstar gamma r| * t := by
      rw [← abs_of_pos ht, ← abs_mul, abs_of_pos ht, sub_mul]
    have hstep1 : |sigmaBar - effectiveDiffusivity nu cstar gamma r| * t ≤ eps * sigmaBar * t := by
      have := mul_le_mul_of_nonneg_right habs1 ht.le
      linarith only [this]
    have hst : sigmaBar * t ≤ 2 * (effectiveDiffusivity nu cstar gamma r * t) := by
      have := mul_le_mul_of_nonneg_right hcomp ht.le
      linarith only [this]
    have hstep2 : eps * (sigmaBar * t) ≤ eps * (2 * (effectiveDiffusivity nu cstar gamma r * t)) :=
      mul_le_mul_of_nonneg_left hst hepsnn
    have hstep3 : (2 * eps) * (effectiveDiffusivity nu cstar gamma r * t) ≤
        (2 * eps) * r ^ (2 : ℕ) :=
      mul_le_mul_of_nonneg_left hEle (by linarith only [hepsnn])
    rw [hprod]
    linarith only [hstep1, hstep2, hstep3]
  have hgle := le_sqrt_mul_abs_log hgamma hgamma4
  have hr2 : (0 : ℝ) ≤ r ^ (2 : ℕ) := by positivity
  calc |intrinsicScale nu cstar gamma t ^ (2 : ℕ) - sigmaBar * t|
      ≤ |intrinsicScale nu cstar gamma t ^ (2 : ℕ) - effectiveDiffusivity nu cstar gamma r * t| +
          |effectiveDiffusivity nu cstar gamma r * t - sigmaBar * t| := by
        exact abs_sub_le _ _ _
    _ = |intrinsicScale nu cstar gamma t ^ (2 : ℕ) -
          effectiveDiffusivity nu cstar gamma r * t| +
          |sigmaBar * t - effectiveDiffusivity nu cstar gamma r * t| := by
        rw [abs_sub_comm (effectiveDiffusivity nu cstar gamma r * t) (sigmaBar * t)]
    _ ≤ gamma * r ^ (2 : ℕ) + 2 * eps * r ^ (2 : ℕ) := add_le_add hprof hgap
    _ ≤ (1 + 2 * C) * Real.sqrt gamma * |Real.log gamma| * r ^ (2 : ℕ) := by
        rw [heps]
        nlinarith only [hgle, hr2, hC]

end

end Algsuperdiff.Section5.Support
