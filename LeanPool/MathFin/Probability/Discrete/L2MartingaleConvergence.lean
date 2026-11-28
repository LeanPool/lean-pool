/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Discrete.MartingaleDominator
public import TauCeti.MeasureTheory.Function.UniformIntegrable
public import Mathlib.Probability.Martingale.Convergence

/-!
# L²-bounded discrete martingales converge in L²

Mathlib's martingale convergence theory gives, for an L¹-bounded
submartingale, almost-everywhere convergence to `ℱ.limitProcess f μ`
(`Submartingale.ae_tendsto_limitProcess`), membership of the limit in `Lᵖ`
under an `Lᵖ` bound (`Submartingale.memLp_limitProcess`), and **L¹**-norm
convergence under uniform integrability
(`Submartingale.tendsto_eLpNorm_one_limitProcess`). It does **not** contain
the classical L² statement: an L²-bounded martingale converges in L²-norm.

This file obtains uniform integrability from a square-integrable envelope.
Its finite-time bound is Tau Ceti's Doob inequality
`MeasureTheory.Martingale.eLpNorm_partialSups_norm_le`, used at `p = 2`.

1. the running maxima `ω ↦ max_{k ≤ n} ‖f k ω‖` are uniformly L²-bounded by
   `2R` (Doob at `p = 2`);
2. by monotone convergence the all-time envelope `ω ↦ ⨆ n ‖f n ω‖` is
   square-integrable, and it dominates every `f n` — steps 1–2 are the `p = 2`
   case of `MeasureTheory.LpDominator`, shared with
   `LpContinuousMartingaleConvergence`;
3. a single L² dominator makes the family uniformly integrable in L²
   (`MemLp.uniformIntegrable_of_eNorm_le` in Tau Ceti);
4. Vitali (`tendsto_Lp_finite_of_tendsto_ae`) upgrades the a.e. convergence
   to L²-norm convergence.

## Main results

* `martingale_ae_tendsto_and_eLpNorm_two_tendsto` — for a martingale `f`
  with `eLpNorm (f n) 2 μ ≤ R` for all `n`: a.e. convergence to
  `ℱ.limitProcess f μ` **and** `eLpNorm (f n − ℱ.limitProcess f μ) 2 μ → 0`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 2.5.1

## Tags

martingale convergence, L²-bounded martingale, Doob maximal inequality, uniform integrability,
Vitali theorem, MSC 60G42, MSC 60F15
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

/-- **L² martingale convergence** (Saporito, Theorem 2.5.1, L² form). A
martingale bounded in L² converges to `ℱ.limitProcess f μ` almost everywhere
**and** in L²-norm. The a.e. half is Mathlib's upcrossing-based convergence;
an L² envelope from Tau Ceti's Doob bound dominates every `f n`
(`MeasureTheory.LpDominator`). The envelope gives uniform integrability in L²,
and Vitali's convergence theorem gives L² convergence. -/
theorem martingale_ae_tendsto_and_eLpNorm_two_tendsto
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]
    {ℱ : Filtration ℕ m0} {f : ℕ → Ω → ℝ} {R : ℝ≥0}
    (hf : Martingale f ℱ μ) (hbdd : ∀ n, eLpNorm (f n) 2 μ ≤ R) :
    (∀ᵐ ω ∂μ, Filter.Tendsto (fun n ↦ f n ω) Filter.atTop
      (nhds (ℱ.limitProcess f μ ω))) ∧
    Filter.Tendsto (fun n ↦ eLpNorm (f n - ℱ.limitProcess f μ) 2 μ)
      Filter.atTop (nhds 0) := by
  have hmeas (n : ℕ) : AEStronglyMeasurable (f n) μ :=
    ((hf.stronglyMeasurable n).mono (ℱ.le n)).aestronglyMeasurable
  -- L¹ bound from the L² bound on a finite measure
  have hbdd1 : ∃ R₁ : ℝ≥0, ∀ n, eLpNorm (f n) 1 μ ≤ (R₁ : ℝ≥0∞) := by
    set c : ℝ≥0∞ := μ Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal)
      with hc_def
    have hc_ne : c ≠ ∞ := by
      rw [hc_def]
      exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ _)).ne
    refine ⟨((R : ℝ≥0∞) * c).toNNReal, fun n ↦ ?_⟩
    have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ) (p := 1) (q := 2)
      one_le_two (hmeas n)
    rw [ENNReal.coe_toNNReal (by finiteness)]
    exact h.trans (mul_le_mul_left (hbdd n) _)
  obtain ⟨R₁, hR₁⟩ := hbdd1
  have h_ae := hf.submartingale.ae_tendsto_limitProcess ((iSup_le hR₁).trans_lt ENNReal.coe_lt_top)
  -- Doob's L² maximal inequality: the envelope `⨆ n ‖f n‖` is in L² and dominates every `f n`
  have hb (n : ℕ) : eLpNorm (f n) (ENNReal.ofReal 2) μ ≤ ENNReal.ofReal R := by
    simpa using hbdd n
  have hdom : MemLp (LpDominator.dominator f) 2 μ := by
    simpa using LpDominator.dominator_memLp one_lt_two hf hb
  exact ⟨h_ae, tendsto_Lp_finite_of_tendsto_ae one_le_two ENNReal.ofNat_ne_top hmeas
    (hf.submartingale.memLp_limitProcess ((iSup_le hbdd).trans_lt ENNReal.coe_lt_top))
    (hdom.uniformIntegrable_of_eNorm_le one_le_two ENNReal.ofNat_ne_top hmeas
      (fun n ↦ (LpDominator.norm_le_dominator one_lt_two hf hb n).mono fun _ h ↦ by
        simpa only [← ofReal_norm, Real.norm_eq_abs] using
          ENNReal.ofReal_le_ofReal (h.trans (le_abs_self _)))).unifIntegrable h_ae⟩

end MathFin
