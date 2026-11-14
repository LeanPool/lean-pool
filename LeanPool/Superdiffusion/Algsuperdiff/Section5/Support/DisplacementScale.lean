/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.Carrier

/-!
# DisplacementScale

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The displacement scale `S_m` and its moments

The tail bound on the displacement is stated at a random scale

`S_m = δ^{-1/(1-γ)} 3^{Y_m(ε)}`,

where `Y_m(ε)` is the `ℕ`-valued scale of the chains-of-good-cubes estimate and
`δ ∈ (0, 1]` is the separation parameter of the argument.  The scale is a
genuine positive real at every sample: `Y` is `ℕ`-valued, so `3^{Y}` is a
natural power of three and no fallback value is involved.

The moment bound is one integration of the tail of `Y`.  If

`P[Y ≥ N] ≤ exp(-a 3^N)` for `N ≥ 1`,

then, for every exponent `p` with `2 p log 3 ≤ a`,

`E[S_m^p] ≤ (δ^{-1/(1-γ)} (1 - e^{-a/2})^{-1})^p`,

so `E[S_m^p]^{1/p}` is bounded by a constant.  The two steps are: the summand
`3^{pN} exp(-a 3^N)` is at most `exp(-aN/2)` because `3^N ≥ N`, and the
resulting geometric series is summed.  The admissible exponents are exactly
those below `a / (2 log 3)`: with the rate `a = c ε² γ^{-1} |log γ|^{-6}` of the
chains estimate this is `(c ε² / (2 log 3)) γ^{-1} |log γ|^{-6}`, the shape the
source uses.

The constants of the bound are uniform over the model: `ε` is bounded below by
`C γ^{1/2} |log γ|^{7/2}`, which makes the rate at least `c C² |log γ|`, and
`γ ≤ 1/4` makes `δ^{-1/(1-γ)}` at most `δ^{-4/3}`.

The admissible exponents are nonempty only when the rate exceeds `2 log 3`, and
at the bottom `ε = C γ^{1/2}|log γ|^{7/2}` of the accuracy range the rate is
`c C² |log γ|`, whose size is governed by constants that nothing here pins.  The
way out is the top of the range: at `ε = 1/4` the rate is
`(c/16) γ^{-1}|log γ|^{-6}`, which is large for small `γ`.  The last section
makes that quantitative, with an explicit threshold `γ_1(c, C)` below which
`ε = 1/4` is an admissible accuracy and the exponent `p = 1` is admissible with
it.

## Main definitions

* `displacementScale delta gamma N` — the value `δ^{-1/(1-γ)} 3^N` of `S_m` at
  `Y = N`.

## References

* ABK26, the displacement tail bound of Section 5.3.
-/

namespace Algsuperdiff.Section5.Support

open Algsuperdiff.Section3
open MeasureTheory
open scoped ENNReal

noncomputable section

/-! ## 1. The scale -/

/-- **The displacement scale** `S_m = δ^{-1/(1-γ)} 3^{Y_m(ε)}`, as a function of
the value `N` of `Y_m(ε)`. -/
def displacementScale (delta gamma : ℝ) (N : ℕ) : ℝ :=
  delta ^ (-(1 - gamma)⁻¹) * (3 : ℝ) ^ N

/-- The scale is a genuine positive real, at every value of `Y`. -/
theorem displacementScale_pos {delta : ℝ} (hdelta : 0 < delta) (gamma : ℝ) (N : ℕ) :
    0 < displacementScale delta gamma N :=
  mul_pos (Real.rpow_pos_of_pos hdelta _) (by positivity)

/-- The scale is a measurable function of the sample whenever `Y` is. -/
theorem measurable_displacementScale {Omega : Type*} [MeasurableSpace Omega]
    {Y : Omega → ℕ} (hY : Measurable Y) (delta gamma : ℝ) :
    Measurable fun omega => displacementScale delta gamma (Y omega) :=
  (measurable_from_top (f := fun N : ℕ => displacementScale delta gamma N)).comp hY

/-! ## 2. The integration of the tail -/

section Tail

variable {Omega : Type*} [MeasurableSpace Omega]

/-- The law of an `ℕ`-valued variable reads an integral as a sum over its
values. -/
private theorem lintegral_comp_natValued (mu : Measure Omega) {Y : Omega → ℕ}
    (hY : Measurable Y) (g : ℕ → ℝ≥0∞) :
    ∫⁻ omega, g (Y omega) ∂mu = ∑' N : ℕ, g N * mu (Y ⁻¹' {N}) := by
  rw [← lintegral_map measurable_from_top hY, lintegral_countable']
  exact tsum_congr fun N => by rw [Measure.map_apply hY (measurableSet_singleton N)]

private theorem natCast_le_three_pow (N : ℕ) : (N : ℝ) ≤ (3 : ℝ) ^ N := by
  have h : N < 3 ^ N := Nat.lt_pow_self (by norm_num)
  exact_mod_cast h.le

/-- The `N`-th summand of the integrated tail, at an exponent below
`a / (2 log 3)`, is at most the `N`-th term of a geometric series of ratio
`e^{-a/2}`. -/
private theorem three_pow_rpow_mul_exp_le {a p : ℝ} (ha : 0 < a)
    (hpa : 2 * (p * Real.log 3) ≤ a) (N : ℕ) :
    ((3 : ℝ) ^ N) ^ p * Real.exp (-(a * (3 : ℝ) ^ N)) ≤ Real.exp (-(a / 2)) ^ N := by
  have hrpow : ((3 : ℝ) ^ N) ^ p = Real.exp (p * (N * Real.log 3)) := by
    rw [← Real.rpow_natCast (3 : ℝ) N, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 3),
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
    ring_nf
  have hgeom : Real.exp (-(a / 2)) ^ N = Real.exp (-(a / 2) * N) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [hrpow, hgeom, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hN : (N : ℝ) ≤ (3 : ℝ) ^ N := natCast_le_three_pow N
  have h1 : p * (N * Real.log 3) ≤ a / 2 * N := by
    have hlog : p * Real.log 3 ≤ a / 2 := by linarith only [hpa]
    have hrw : p * (N * Real.log 3) = p * Real.log 3 * N := by ring
    rw [hrw]
    exact mul_le_mul_of_nonneg_right hlog (Nat.cast_nonneg N)
  have h2 : a * (N : ℝ) ≤ a * (3 : ℝ) ^ N := mul_le_mul_of_nonneg_left hN ha.le
  linarith only [h1, h2]

/-- **The integration of the tail.**  An `ℕ`-valued variable whose tail decays
like `exp(-a 3^N)` from `N = 1` on has `E[3^{pY}] ≤ (1 - e^{-a/2})^{-1}` at every
exponent `p` with `2 p log 3 ≤ a`. -/
theorem lintegral_ofReal_three_pow_rpow_le_of_tail (mu : Measure Omega)
    [IsProbabilityMeasure mu] {Y : Omega → ℕ} (hY : Measurable Y) {a p : ℝ} (ha : 0 < a)
    (hpa : 2 * (p * Real.log 3) ≤ a)
    (htail : ∀ N : ℕ, 1 ≤ N → mu {omega | N ≤ Y omega} ≤
      ENNReal.ofReal (Real.exp (-(a * (3 : ℝ) ^ N)))) :
    (∫⁻ omega, ENNReal.ofReal ((3 : ℝ) ^ (Y omega)) ^ p ∂mu) ≤
      ENNReal.ofReal (1 - Real.exp (-(a / 2)))⁻¹ := by
  have hexp : Real.exp (-(a / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith only [ha]
  have hpos : (0 : ℝ) < 1 - Real.exp (-(a / 2)) := by linarith only [hexp]
  rw [lintegral_comp_natValued mu hY fun N => ENNReal.ofReal ((3 : ℝ) ^ N) ^ p]
  have hterm : ∀ N : ℕ, ENNReal.ofReal ((3 : ℝ) ^ N) ^ p * mu (Y ⁻¹' {N}) ≤
      ENNReal.ofReal (Real.exp (-(a / 2))) ^ N := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simpa using prob_le_one (μ := mu) (s := Y ⁻¹' {0})
    · have hsub : Y ⁻¹' {N} ⊆ {omega | N ≤ Y omega} := by
        intro omega homega
        simp only [Set.mem_preimage, Set.mem_singleton_iff] at homega
        simp only [Set.mem_ofPred_eq, homega, le_refl]
      calc ENNReal.ofReal ((3 : ℝ) ^ N) ^ p * mu (Y ⁻¹' {N})
          ≤ ENNReal.ofReal ((3 : ℝ) ^ N) ^ p *
              ENNReal.ofReal (Real.exp (-(a * (3 : ℝ) ^ N))) := by
            gcongr
            exact (measure_mono hsub).trans (htail N hN)
        _ = ENNReal.ofReal (((3 : ℝ) ^ N) ^ p * Real.exp (-(a * (3 : ℝ) ^ N))) := by
            rw [ENNReal.ofReal_rpow_of_pos (by positivity),
              ← ENNReal.ofReal_mul (by positivity)]
        _ ≤ ENNReal.ofReal (Real.exp (-(a / 2)) ^ N) :=
            ENNReal.ofReal_le_ofReal (three_pow_rpow_mul_exp_le ha hpa N)
        _ = ENNReal.ofReal (Real.exp (-(a / 2))) ^ N :=
            ENNReal.ofReal_pow (Real.exp_pos _).le N
  calc (∑' N : ℕ, ENNReal.ofReal ((3 : ℝ) ^ N) ^ p * mu (Y ⁻¹' {N}))
      ≤ ∑' N : ℕ, ENNReal.ofReal (Real.exp (-(a / 2))) ^ N := ENNReal.tsum_le_tsum hterm
    _ = (1 - ENNReal.ofReal (Real.exp (-(a / 2))))⁻¹ := ENNReal.tsum_geometric _
    _ = ENNReal.ofReal (1 - Real.exp (-(a / 2)))⁻¹ := by
        rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.ofReal_sub _ (Real.exp_pos _).le,
          ENNReal.ofReal_one]

/-- **The moment bound for the displacement scale at an arbitrary rate.** -/
theorem lintegral_ofReal_displacementScale_rpow_le (mu : Measure Omega)
    [IsProbabilityMeasure mu] {Y : Omega → ℕ} (hY : Measurable Y)
    {delta gamma a p : ℝ} (hdelta : 0 < delta) (ha : 0 < a) (hp : 1 ≤ p)
    (hpa : 2 * (p * Real.log 3) ≤ a)
    (htail : ∀ N : ℕ, 1 ≤ N → mu {omega | N ≤ Y omega} ≤
      ENNReal.ofReal (Real.exp (-(a * (3 : ℝ) ^ N)))) :
    (∫⁻ omega, ENNReal.ofReal (displacementScale delta gamma (Y omega)) ^ p ∂mu) ≤
      ENNReal.ofReal (delta ^ (-(1 - gamma)⁻¹) * (1 - Real.exp (-(a / 2)))⁻¹) ^ p := by
  have hexp : Real.exp (-(a / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith only [ha]
  have hpos : (0 : ℝ) < 1 - Real.exp (-(a / 2)) := by linarith only [hexp]
  have hB : (1 : ℝ) ≤ (1 - Real.exp (-(a / 2)))⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hpos]
    have := (Real.exp_pos (-(a / 2))).le
    linarith only [this]
  set D : ℝ := delta ^ (-(1 - gamma)⁻¹) with hD
  set B : ℝ := (1 - Real.exp (-(a / 2)))⁻¹ with hBdef
  have hDpos : 0 < D := Real.rpow_pos_of_pos hdelta _
  have hp0 : (0 : ℝ) ≤ p := le_trans zero_le_one hp
  have hsplit : ∀ omega : Omega,
      ENNReal.ofReal (displacementScale delta gamma (Y omega)) ^ p =
        ENNReal.ofReal D ^ p * ENNReal.ofReal ((3 : ℝ) ^ (Y omega)) ^ p := by
    intro omega
    rw [displacementScale, ← hD, ENNReal.ofReal_mul hDpos.le,
      ENNReal.mul_rpow_of_nonneg _ _ hp0]
  have hne : ENNReal.ofReal D ^ p ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_nonneg hp0 ENNReal.ofReal_ne_top
  calc (∫⁻ omega, ENNReal.ofReal (displacementScale delta gamma (Y omega)) ^ p ∂mu)
      = ∫⁻ omega, ENNReal.ofReal D ^ p * ENNReal.ofReal ((3 : ℝ) ^ (Y omega)) ^ p ∂mu :=
        lintegral_congr hsplit
    _ = ENNReal.ofReal D ^ p * ∫⁻ omega, ENNReal.ofReal ((3 : ℝ) ^ (Y omega)) ^ p ∂mu :=
        lintegral_const_mul' _ _ hne
    _ ≤ ENNReal.ofReal D ^ p * ENNReal.ofReal B := by
        gcongr
        exact lintegral_ofReal_three_pow_rpow_le_of_tail mu hY ha hpa htail
    _ ≤ ENNReal.ofReal D ^ p * ENNReal.ofReal B ^ p := by
        gcongr
        calc ENNReal.ofReal B = ENNReal.ofReal B ^ (1 : ℝ) := (ENNReal.rpow_one _).symm
          _ ≤ ENNReal.ofReal B ^ p :=
              ENNReal.rpow_le_rpow_of_exponent_le (ENNReal.one_le_ofReal.mpr hB) hp
    _ = ENNReal.ofReal (D * B) ^ p := by
        rw [ENNReal.ofReal_mul hDpos.le, ENNReal.mul_rpow_of_nonneg _ _ hp0]

end Tail

end

end Algsuperdiff.Section5.Support
