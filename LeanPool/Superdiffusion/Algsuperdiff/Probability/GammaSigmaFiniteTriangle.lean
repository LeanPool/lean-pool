/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import LeanPool.HighContrastHomogenization.Support.Probability.IndependentSums.GammaSigma.Operations

/-!
# GammaSigmaFiniteTriangle

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Measurability-free finite triangle inequality for `O_{Γ_σ}`

ABK26, Lemma `l.Gamma.sigma.triangle`
(`e.Gamma.sigma.triangle`), in the **finite** case.

## What this adds over CoarseGraining

CoarseGraining already proves a finite generalized triangle inequality,
`Homogenization.IndependentSums.isBigO_finset_sum_of_isBigO_gammaSigma`, but it
carries two hypotheses that are painful downstream:

* `Measurable (X i)` for every summand, and
* `0 < a i` (strict) for every scale.

The requirement is **unnecessary**. The finite triangle has a direct union-bound
proof: the tail event of the sum is *contained* in a finite union of the
summands' tail events, and `MeasureTheory.measureReal_biUnion_finset_le` holds
for completely arbitrary sets. This module gives that proof. No measurability
hypothesis appears anywhere below, and scales are only assumed nonnegative.

## The constant

For an `N`-term sum the scale produced here is `(1 + log N)^{1/σ} · ∑ a_i`.
This is both sharper and more explicit than CoarseGraining's
`gammaTriangleConst σ` (which is `σ`-dependent and enormous).  The mechanism:
splitting the budget as `a_i · (λ t)` with `λ = (1 + log N)^{1/σ}` makes each
of the `N` summand tails at most `exp(-(1 + log N) t^σ)`, and `N · exp(-(1 +
log N) t^σ) ≤ exp(-t^σ)` exactly because `t^σ ≥ 1`.

## Main results

* `Algsuperdiff.Probability.isBigO_gammaSigma_finset_sum_of_nonneg_scales`
* `Algsuperdiff.Probability.isBigO_gammaSigma_add2'`

## References

* ABK26, Lemma `l.Gamma.sigma.triangle`.
-/

namespace Algsuperdiff.Probability

open MeasureTheory
open HCPolySupport.IndependentSums
open scoped BigOperators

section Triangle

variable {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The exponential bookkeeping behind the sharp constant: if `0 ≤ L` and
`1 ≤ u`, then `exp L · exp (-((1 + L) * u)) ≤ exp (-u)`. -/
private theorem exp_card_mul_le (L u : ℝ) (hL : 0 ≤ L) (hu : 1 ≤ u) :
    Real.exp L * Real.exp (-((1 + L) * u)) ≤ Real.exp (-u) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have hprod : 0 ≤ L * (u - 1) := mul_nonneg hL (by linarith only [hu])
  linarith only [hprod]

/-- **Measurability-free finite generalized triangle inequality** for the
stretched-exponential class `Γ_σ` (`l.Gamma.sigma.triangle`, finite case).

If `X i = O_{Γ_σ}(a i)` for each `i` in a nonempty finite index set `s`, with
nonnegative scales `a i`, then

`∑_{i ∈ s} X i = O_{Γ_σ}( (1 + log #s)^{1/σ} · ∑_{i ∈ s} a i )`.

Unlike CoarseGraining's `isBigO_finset_sum_of_isBigO_gammaSigma`, **no
measurability of the summands is required** — the proof is a pure union bound,
and `measureReal_biUnion_finset_le` needs no measurable sets. -/
theorem isBigO_gammaSigma_finset_sum_of_nonneg_scales
    (s : Finset ι) {X : ι → Ω → ℝ} {a : ι → ℝ} {σ : ℝ}
    (hσ : 0 < σ) (hs : s.Nonempty) (ha : ∀ i ∈ s, 0 ≤ a i)
    (hX : ∀ i ∈ s, IsBigO μ (gammaSigma σ) (X i) (a i)) :
    IsBigO μ (gammaSigma σ) (fun ω => ∑ i ∈ s, X i ω)
      ((1 + Real.log (s.card : ℝ)) ^ σ⁻¹ * ∑ i ∈ s, a i) := by
  -- Basic facts about the cardinality and the amplification factor `lam`.
  have hcard_pos : 0 < (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  have hcard_one : (1 : ℝ) ≤ (s.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hs
  set L : ℝ := Real.log (s.card : ℝ) with hLdef
  have hL0 : 0 ≤ L := Real.log_nonneg hcard_one
  have h1L : (1 : ℝ) ≤ 1 + L := by linarith only [hL0]
  set lam : ℝ := (1 + L) ^ σ⁻¹ with hlamdef
  have hlam1 : (1 : ℝ) ≤ lam := Real.one_le_rpow h1L (by positivity)
  have hlam0 : (0 : ℝ) ≤ lam := le_trans zero_le_one hlam1
  have hlam_pow : lam ^ σ = 1 + L := by
    rw [hlamdef, ← Real.rpow_mul (by linarith only [hL0]), inv_mul_cancel₀ hσ.ne',
      Real.rpow_one]
  -- Nonnegativity of the total scale.  (This records the only role of `ha`: the
  -- union-bound argument below never needs the sign of the scales.)
  have _hsum_nonneg : 0 ≤ ∑ i ∈ s, a i := Finset.sum_nonneg ha
  rw [isBigO_gammaSigma_iff]
  intro t ht
  have ht0 : (0 : ℝ) ≤ t := le_trans zero_le_one ht
  have hlamt : (1 : ℝ) ≤ lam * t := by
    calc (1 : ℝ) = 1 * 1 := by norm_num
      _ ≤ lam * t := mul_le_mul hlam1 ht zero_le_one hlam0
  -- Step A: set inclusion into a finite union of summand tail events.
  have hsub :
      absTailEvent (fun ω => ∑ i ∈ s, X i ω) ((lam * ∑ i ∈ s, a i) * t) ⊆
        ⋃ i ∈ s, absTailEvent (X i) (a i * (lam * t)) := by
    intro ω hω
    by_contra hcon
    have hall : ∀ i ∈ s, |X i ω| ≤ a i * (lam * t) := by
      intro i hi
      by_contra hlt
      exact hcon (Set.mem_biUnion hi (mem_absTailEvent.mpr (not_le.mp hlt)))
    have hbound : |∑ i ∈ s, X i ω| ≤ (∑ i ∈ s, a i) * (lam * t) := by
      calc |∑ i ∈ s, X i ω| ≤ ∑ i ∈ s, |X i ω| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ s, a i * (lam * t) := Finset.sum_le_sum hall
        _ = (∑ i ∈ s, a i) * (lam * t) := by rw [← Finset.sum_mul]
    have hstrict : (lam * ∑ i ∈ s, a i) * t < |∑ i ∈ s, X i ω| := mem_absTailEvent.mp hω
    have heq : (∑ i ∈ s, a i) * (lam * t) = (lam * ∑ i ∈ s, a i) * t := by ring
    rw [heq] at hbound
    exact absurd hstrict (not_lt.mpr hbound)
  -- Step B: union bound (no measurability needed).
  have hstepB :
      μ.real (absTailEvent (fun ω => ∑ i ∈ s, X i ω) ((lam * ∑ i ∈ s, a i) * t)) ≤
        ∑ i ∈ s, μ.real (absTailEvent (X i) (a i * (lam * t))) :=
    le_trans (measureReal_mono hsub (measure_ne_top μ _))
      (measureReal_biUnion_finset_le (μ := μ) s _)
  -- Step C: each summand tail, at the amplified level `lam * t`.
  have hstepC : ∀ i ∈ s,
      μ.real (absTailEvent (X i) (a i * (lam * t))) ≤ Real.exp (-((lam * t) ^ σ)) :=
    fun i hi => (isBigO_gammaSigma_iff.mp (hX i hi)) hlamt
  have hsum_le :
      ∑ i ∈ s, μ.real (absTailEvent (X i) (a i * (lam * t))) ≤
        (s.card : ℝ) * Real.exp (-((lam * t) ^ σ)) := by
    calc ∑ i ∈ s, μ.real (absTailEvent (X i) (a i * (lam * t)))
        ≤ ∑ _i ∈ s, Real.exp (-((lam * t) ^ σ)) := Finset.sum_le_sum hstepC
      _ = (s.card : ℝ) * Real.exp (-((lam * t) ^ σ)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Step D: the arithmetic that eats the cardinality factor.
  have hpow_split : (lam * t) ^ σ = (1 + L) * t ^ σ := by
    rw [Real.mul_rpow hlam0 ht0, hlam_pow]
  have htpow_one : (1 : ℝ) ≤ t ^ σ := Real.one_le_rpow ht hσ.le
  have hcard_exp : (s.card : ℝ) = Real.exp L := (Real.exp_log hcard_pos).symm
  have hfinal : (s.card : ℝ) * Real.exp (-((lam * t) ^ σ)) ≤ Real.exp (-(t ^ σ)) := by
    rw [hcard_exp, hpow_split]
    exact exp_card_mul_le L (t ^ σ) hL0 htpow_one
  exact le_trans hstepB (le_trans hsum_le hfinal)

/-- Two-term measurability-free `Γ_σ` triangle inequality, constant
`(1 + log 2)^{1/σ}`. -/
theorem isBigO_gammaSigma_add2' {X Y : Ω → ℝ} {a b σ : ℝ}
    (hσ : 0 < σ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hX : IsBigO μ (gammaSigma σ) X a) (hY : IsBigO μ (gammaSigma σ) Y b) :
    IsBigO μ (gammaSigma σ) (fun ω => X ω + Y ω)
      ((1 + Real.log 2) ^ σ⁻¹ * (a + b)) := by
  have h := isBigO_gammaSigma_finset_sum_of_nonneg_scales (μ := μ)
    (s := (Finset.univ : Finset (Fin 2))) (X := ![X, Y]) (a := ![a, b]) (σ := σ)
    hσ Finset.univ_nonempty
    (by intro i _; fin_cases i <;> simpa using ‹_›)
    (by intro i _; fin_cases i <;> simpa using ‹_›)
  simpa [Fin.sum_univ_two] using h

/-- Three-term measurability-free `Γ_σ` triangle inequality, constant
`(1 + Real.log 3) ^ σ⁻¹`. -/
theorem isBigO_gammaSigma_add3 {X Y Z : Ω → ℝ} {a b c σ : ℝ}
    (hσ : 0 < σ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hX : IsBigO μ (gammaSigma σ) X a) (hY : IsBigO μ (gammaSigma σ) Y b)
    (hZ : IsBigO μ (gammaSigma σ) Z c) :
    IsBigO μ (gammaSigma σ) (fun ω => X ω + Y ω + Z ω)
      ((1 + Real.log 3) ^ σ⁻¹ * (a + b + c)) := by
  have h := isBigO_gammaSigma_finset_sum_of_nonneg_scales (μ := μ)
    (s := (Finset.univ : Finset (Fin 3))) (X := ![X, Y, Z]) (a := ![a, b, c]) (σ := σ)
    hσ Finset.univ_nonempty
    (by intro i _; fin_cases i <;> simpa using ‹_›)
    (by intro i _; fin_cases i <;> simpa using ‹_›)
  simpa [Fin.sum_univ_three, add_assoc] using h

end Triangle

end Algsuperdiff.Probability
