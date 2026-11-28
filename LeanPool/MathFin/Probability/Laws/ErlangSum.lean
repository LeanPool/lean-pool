/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Distributions.Exponential
public import Mathlib.Probability.Independence.Basic

/-!
# Sums of iid exponentials are Erlang: the Gamma convolution identity

Mathlib has the Gamma and exponential distributions (`gammaMeasure`,
`expMeasure = gammaMeasure 1`) but **no convolution identity** for them: there
is no lemma computing `gammaMeasure a r ∗ expMeasure r`, and consequently no
proof that the sum of `n` iid `Exp(r)` waiting times is `Erlang(n, r)`
(Saporito, Appendix B.2).

This file proves both, from the densities up.

The analytic heart is the convolution of densities. For `a > 0` the
exponential factors merge into a constant —
`exp (−r·x) · exp (−r·(z−x)) = exp (−r·z)` — so the Beta-type integral
degenerates to the elementary `∫_0^z x^(a−1) dx = z^a / a`, and
`Γ(a+1) = a·Γ(a)` turns the constant into exactly the `Gamma (a+1, r)`
normalisation. No Beta function, no special-function machinery: the identity
holds for every real `a > 0` by completing the constant.

## Main results

* `ErlangSum.gammaMeasure_conv_expMeasure` —
  `gammaMeasure a r ∗ expMeasure r = gammaMeasure (a+1) r` for `a, r > 0`.
* `ErlangSum.map_sum_iidExp` — for iid `Exp(r)` variables indexed by a
  nonempty finset `s`, the law of `∑ i ∈ s, X i` is `gammaMeasure s.card r`.
* `sum_iidExp_law_gammaMeasure` — the textbook form: the sum of all `n ≥ 1`
  coordinates has law `Erlang(n, r) = gammaMeasure n r`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Appendix B.2, p. 178

## Tags

Erlang distribution, Gamma convolution, exponential waiting times, Poisson process arrival time,
sum of exponentials, MSC 60E05, MSC 60G55
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace ErlangSum

variable {a r : ℝ}

/-! ### The density-level convolution identity -/

/-- Pointwise (away from `x = 0`): the product of the `Gamma(a,r)` density at
`x` and the `Exp(r)` density at `z − x` collapses, after the exponentials
merge, to a constant multiple of `x^(a−1)` supported on `(0, z]`. -/
lemma gammaPDF_mul_exponentialPDF_sub_of_ne_zero (ha : 0 < a) (hr : 0 < r) {z x : ℝ} (hx : x ≠ 0) :
    gammaPDF a r x * exponentialPDF r (z - x)
      = ENNReal.ofReal ((Set.Ioc 0 z).indicator
          (fun t ↦ r ^ (a + 1) / Gamma a * Real.exp (-(r * z)) * t ^ (a - 1)) x) := by
  rcases lt_or_gt_of_ne hx with hx_neg | hx_pos
  · rw [gammaPDF_of_neg hx_neg,
      Set.indicator_of_notMem
        (show x ∉ Set.Ioc 0 z from fun h ↦ absurd h.1 (not_lt.mpr hx_neg.le)),
      ENNReal.ofReal_zero, zero_mul]
  · by_cases hxz : x ≤ z
    · have hzx : (0 : ℝ) ≤ z - x := by linarith
      rw [gammaPDF_of_nonneg hx_pos.le, exponentialPDF_eq, ite_eq_left hzx,
        ← ENNReal.ofReal_mul (by positivity),
        Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hx_pos, hxz⟩)]
      congr 1
      have hexp : Real.exp (-(r * x)) * Real.exp (-(r * (z - x)))
          = Real.exp (-(r * z)) := by
        rw [← Real.exp_add]; ring_nf
      calc r ^ a / Gamma a * x ^ (a - 1) * Real.exp (-(r * x))
            * (r * Real.exp (-(r * (z - x))))
          = r ^ a * r / Gamma a * x ^ (a - 1)
            * (Real.exp (-(r * x)) * Real.exp (-(r * (z - x)))) := by ring
        _ = r ^ (a + 1) / Gamma a * Real.exp (-(r * z)) * x ^ (a - 1) := by
            rw [hexp, Real.rpow_add_one hr.ne']; ring
    · rw [exponentialPDF_of_neg (by linarith), mul_zero,
        Set.indicator_of_notMem (show x ∉ Set.Ioc 0 z from fun h ↦ absurd h.2 hxz),
        ENNReal.ofReal_zero]

/-- The elementary Beta-degenerate integral: `∫_{(0,z]} x^(a−1) dx = z^a / a`. -/
lemma setIntegral_rpow_sub_one_Ioc (ha : 0 < a) {z : ℝ} (hz : 0 ≤ z) :
    ∫ x in Set.Ioc 0 z, x ^ (a - 1) = z ^ a / a := by
  rw [← intervalIntegral.integral_of_le hz,
    integral_rpow (Or.inl (by linarith)),
    show a - 1 + 1 = a from by ring,
    Real.zero_rpow ha.ne', sub_zero]

/-- **Density convolution identity.** For `a, r > 0` and every `z`,
`∫ gammaPDF a r x · exponentialPDF r (z−x) dx = gammaPDF (a+1) r z`. -/
lemma lintegral_gammaPDF_mul_exponentialPDF
    (ha : 0 < a) (hr : 0 < r) (z : ℝ) :
    ∫⁻ x, gammaPDF a r x * exponentialPDF r (z - x) = gammaPDF (a + 1) r z := by
  rcases lt_or_ge z 0 with hz | hz
  · -- `z < 0`: integrand vanishes identically, and so does the target density
    rw [gammaPDF_of_neg hz, show (fun x ↦ gammaPDF a r x * exponentialPDF r (z - x))
        = fun _ ↦ 0 from funext fun x ↦ ?_, lintegral_zero]
    rcases lt_or_ge x 0 with hx | hx
    · rw [gammaPDF_of_neg hx, zero_mul]
    · rw [exponentialPDF_of_neg (by linarith), mul_zero]
  · -- `0 ≤ z`: reduce to the elementary integral on `(0, z]`
    have h0 : ∀ᵐ x : ℝ, x ≠ (0 : ℝ) := by
      refine ae_iff.mpr ?_
      simp
    set c : ℝ := r ^ (a + 1) / Gamma a * Real.exp (-(r * z)) with hc_def
    have h_int : IntegrableOn (fun x : ℝ ↦ c * x ^ (a - 1)) (Set.Ioc 0 z) volume := by
      refine Integrable.const_mul ?_ c
      exact (intervalIntegral.intervalIntegrable_rpow' (by linarith)).1
    calc ∫⁻ x, gammaPDF a r x * exponentialPDF r (z - x)
        = ∫⁻ x, ENNReal.ofReal
            ((Set.Ioc 0 z).indicator (fun t ↦ c * t ^ (a - 1)) x) := by
          refine lintegral_congr_ae ?_
          filter_upwards [h0] with x hx
          exact gammaPDF_mul_exponentialPDF_sub_of_ne_zero ha hr hx
      _ = ∫⁻ x, (Set.Ioc 0 z).indicator
            (fun t ↦ ENNReal.ofReal (c * t ^ (a - 1))) x := by
          refine lintegral_congr fun x ↦ ?_
          by_cases hx : x ∈ Set.Ioc 0 z
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
              ENNReal.ofReal_zero]
      _ = ∫⁻ x in Set.Ioc 0 z, ENNReal.ofReal (c * x ^ (a - 1)) :=
          lintegral_indicator measurableSet_Ioc _
      _ = ENNReal.ofReal (∫ x in Set.Ioc 0 z, c * x ^ (a - 1)) := by
          rw [← ofReal_integral_eq_lintegral_ofReal h_int]
          refine Filter.Eventually.mono (ae_restrict_mem measurableSet_Ioc)
            fun x hx ↦ ?_
          have : (0 : ℝ) ≤ x ^ (a - 1) := Real.rpow_nonneg hx.1.le _
          positivity
      _ = ENNReal.ofReal (c * (z ^ a / a)) := by
          rw [integral_const_mul, setIntegral_rpow_sub_one_Ioc ha hz]
      _ = gammaPDF (a + 1) r z := by
          rw [gammaPDF_of_nonneg hz]
          congr 1
          rw [hc_def, Real.Gamma_add_one ha.ne', show a + 1 - 1 = a from by ring]
          field_simp

/-! ### The measure-level convolution identity -/

/-- **Gamma–exponential convolution**: for `a, r > 0`,
`gammaMeasure a r ∗ expMeasure r = gammaMeasure (a + 1) r`.

This identity (and any Gamma convolution) is absent from Mathlib; it is the
measure-level packaging of `lintegral_gammaPDF_mul_exponentialPDF` via
Tonelli and translation invariance of Lebesgue measure. -/
theorem gammaMeasure_conv_expMeasure (ha : 0 < a) (hr : 0 < r) :
    gammaMeasure a r ∗ expMeasure r = gammaMeasure (a + 1) r := by
  have hg : Measurable (gammaPDF a r) := (measurable_gammaPDFReal a r).ennreal_ofReal
  have he : Measurable (exponentialPDF r) :=
    (measurable_exponentialPDFReal r).ennreal_ofReal
  ext s hs
  have h_ind : Measurable (s.indicator (1 : ℝ → ℝ≥0∞)) :=
    measurable_const.indicator hs
  -- expand the convolution as an iterated integral over the densities
  rw [show expMeasure r = volume.withDensity (exponentialPDF r) from rfl,
    show gammaMeasure a r = volume.withDensity (gammaPDF a r) from rfl] at *
  rw [← lintegral_indicator_one hs, Measure.lintegral_conv h_ind]
  -- unfold the inner withDensity and translate `y ↦ w − x`
  have step_inner : ∀ x : ℝ,
      ∫⁻ y, s.indicator 1 (x + y) ∂(volume.withDensity (exponentialPDF r))
        = ∫⁻ w, exponentialPDF r (w - x) * s.indicator 1 w := by
    intro x
    rw [lintegral_withDensity_eq_lintegral_mul _ he
      (show Measurable fun y : ℝ ↦ s.indicator 1 (x + y) from
        h_ind.comp (measurable_const_add x))]
    rw [← lintegral_add_right_eq_self
      (fun w ↦ exponentialPDF r (w - x) * s.indicator 1 w) x]
    refine lintegral_congr fun y ↦ ?_
    simp only [Pi.mul_apply]
    rw [add_sub_cancel_right, add_comm x y]
  simp_rw [step_inner]
  -- unfold the outer withDensity
  have h_inner_meas : Measurable fun x : ℝ ↦
      ∫⁻ w, exponentialPDF r (w - x) * s.indicator 1 w := by
    refine Measurable.lintegral_prod_right' (f := fun p : ℝ × ℝ ↦
      exponentialPDF r (p.2 - p.1) * s.indicator 1 p.2) ?_
    exact (he.comp (measurable_snd.sub measurable_fst)).mul (h_ind.comp measurable_snd)
  rw [lintegral_withDensity_eq_lintegral_mul _ hg h_inner_meas]
  -- push the density inside, Tonelli-swap, evaluate via the heart identity
  have h_uncurry : Measurable fun p : ℝ × ℝ ↦
      gammaPDF a r p.1 * (exponentialPDF r (p.2 - p.1) * s.indicator 1 p.2) :=
    (hg.comp measurable_fst).mul
      ((he.comp (measurable_snd.sub measurable_fst)).mul (h_ind.comp measurable_snd))
  calc ∫⁻ x, (gammaPDF a r * fun x ↦
        ∫⁻ w, exponentialPDF r (w - x) * s.indicator 1 w) x
      = ∫⁻ x, ∫⁻ w, gammaPDF a r x * (exponentialPDF r (w - x) * s.indicator 1 w) := by
        refine lintegral_congr fun x ↦ ?_
        simp only [Pi.mul_apply]
        exact (lintegral_const_mul _ (show Measurable fun w : ℝ ↦
          exponentialPDF r (w - x) * s.indicator 1 w from
            (he.comp (measurable_sub_const x)).mul h_ind)).symm
    _ = ∫⁻ w, ∫⁻ x, gammaPDF a r x * (exponentialPDF r (w - x) * s.indicator 1 w) :=
        lintegral_lintegral_swap h_uncurry.aemeasurable
    _ = ∫⁻ w, gammaPDF (a + 1) r w * s.indicator 1 w := by
        refine lintegral_congr fun w ↦ ?_
        rw [show (fun x ↦ gammaPDF a r x * (exponentialPDF r (w - x) * s.indicator 1 w))
            = fun x ↦ gammaPDF a r x * exponentialPDF r (w - x) * s.indicator 1 w from
          funext fun x ↦ by ring]
        rw [lintegral_mul_const _ (show Measurable fun x : ℝ ↦
            gammaPDF a r x * exponentialPDF r (w - x) from
          hg.mul (he.comp (measurable_const_sub w))),
          lintegral_gammaPDF_mul_exponentialPDF ha hr w]
    _ = ∫⁻ w in s, gammaPDF (a + 1) r w := by
        rw [← lintegral_indicator hs]
        refine lintegral_congr fun w ↦ ?_
        by_cases hw : w ∈ s
        · simp [Set.indicator_of_mem hw]
        · simp [Set.indicator_of_notMem hw]
    _ = gammaMeasure (a + 1) r s := (withDensity_apply _ hs).symm

/-! ### Sums of iid exponentials -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- **Erlang from iid exponentials, finset form.** If the `X i` are iid
`Exp(r)` and `s` is a nonempty finset (over any index type — `Fin n` for the
textbook statement, `ℕ` for the arrival times of a Poisson process), the law
of `∑ i ∈ s, X i` is `gammaMeasure s.card r`. Induction on `s`: the base case
is `expMeasure = gammaMeasure 1` (definitional), the step is
`gammaMeasure_conv_expMeasure` via `IndepFun.map_add_eq_map_conv_map`. -/
theorem map_sum_iidExp [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    {ι : Type*} {X : ι → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, Measure.map (X i) μ = expMeasure r)
    (hindep : iIndepFun X μ)
    (s : Finset ι) (hs : s.Nonempty) :
    Measure.map (∑ i ∈ s, X i) μ = gammaMeasure s.card r := by
  induction s using Finset.cons_induction with
  | empty => exact absurd hs (by simp)
  | cons i t hi ih =>
    rcases t.eq_empty_or_nonempty with rfl | ht
    · simpa [expMeasure] using hlaw i
    · have hsum_meas : Measurable (∑ j ∈ t, X j) := by
        rw [show (∑ j ∈ t, X j) = fun a ↦ ∑ j ∈ t, X j a from
          funext fun a ↦ Finset.sum_apply a t X]
        exact t.measurable_sum fun j _ ↦ hmeas j
      have hindep' : IndepFun (∑ j ∈ t, X j) (X i) μ :=
        hindep.indepFun_finsetSum_of_notMem hmeas hi
      rw [Finset.sum_cons,
        show X i + ∑ j ∈ t, X j = (∑ j ∈ t, X j) + X i from add_comm _ _,
        hindep'.map_add_eq_map_conv_map hsum_meas (hmeas i),
        ih ht, hlaw i,
        gammaMeasure_conv_expMeasure (by exact_mod_cast ht.card_pos) hr]
      congr 1
      rw [Finset.card_cons]
      push_cast
      ring

/-- **Erlang law for a sum of iid exponentials** (Saporito, Appendix B.2). The `n`-th
arrival time of a `Poisson(r)` process — the sum of `n ≥ 1` iid `Exp(r)`
interarrival times — has the `Erlang(n, r) = gammaMeasure n r` law. Proved
from the densities up via the Gamma convolution identity; no part of the
conclusion is assumed. -/
theorem sum_iidExp_law_gammaMeasure [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r)
    {n : ℕ} (hn : n ≠ 0) {X : Fin n → Ω → ℝ} (hmeas : ∀ i, Measurable (X i))
    (hlaw : ∀ i, Measure.map (X i) μ = expMeasure r)
    (hindep : iIndepFun X μ) :
    Measure.map (fun ω ↦ ∑ i, X i ω) μ = gammaMeasure n r := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
  have h := map_sum_iidExp hr hmeas hlaw hindep Finset.univ Finset.univ_nonempty
  rw [show (fun ω ↦ ∑ i, X i ω) = ∑ i, X i from
    funext fun ω ↦ (Finset.sum_apply ω Finset.univ X).symm]
  simpa [Finset.card_univ] using h

end ErlangSum

end MathFin
