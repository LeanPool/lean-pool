/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Models.Binomial.PathMeasure
public import LeanPool.MathFin.Probability.Martingales.EquivMeasure

/-!
# Discrete Girsanov: measure change in the binomial tree

The continuous-time Girsanov theorem has a transparent discrete-time
counterpart in the binomial model. The one-flip algebra comes first; the same weights, multiplied
over the first `n` flips, are the Radon–Nikodym density between the two coin-flip measures.

Given physical up-probability `p` and risk-neutral up-probability `q`, the
**Radon-Nikodym derivative** `dQ/dP` takes only two values:

  `Z_up = q / p`,    `Z_down = (1 − q) / (1 − p)`.

The key invariant: `E^P[Z] = 1` (the change of measure preserves total mass).
Plugging in:

  `p · (q/p) + (1 − p) · ((1 − q)/(1 − p)) = q + (1 − q) = 1`.

This is the *cleanest possible* instance of Girsanov: a finite, two-point
measure change with explicit RN derivative.

## Why this matters

Every continuous-time risk-neutral pricing argument is `E^Q[X] = E^P[Z · X]`
for the appropriate `Z = dQ/dP`. In the binomial model the same identity
holds with `Z` as above, and the risk-neutral pricing formula

  `V_0 = e^{−r} · E^Q[V_T] = e^{−r} · E^P[Z · V_T]`

is just two-state algebra. We make this discrete Girsanov-machinery explicit.

## Main definitions

* `binomialRN`: the one-flip Radon–Nikodym derivative `dQ/dP`, equal to `q / p` on an up-flip and
  `(1 − q) / (1 − p)` on a down-flip.
* `binomialDensity`: the density process `Z_n(ω) = ∏_{i<n} binomialRN p q (ωᵢ)`.

## Main results

* `weight_mul_binomialRN`: the one-flip identity `P(b) · Z(b) = Q(b)` that everything below
  multiplies or sums.
* `binomialRN_expectation_one`: for `p ≠ 0, 1`, `E^P[Z] = 1` (RN normalisation).
* `binomial_riskNeutral_via_RN`: for `p ≠ 0, 1`, the discrete pricing identity
  `E^Q[V_T] = E^P[Z · V_T] = p · Z_up · V_u + (1 − p) · Z_down · V_d`.
* `map_flips_coinFlipMeasure_eq_withDensity`: **the change of measure on `n` flips.** For
  `0 < p < 1` and `q ≤ 1`, the law
  of the first `n` flips under `Bernoulli(q)` is the law under `Bernoulli(p)` with density
  `∏ᵢ Z(xᵢ)`; `coinFlipMeasure_apply_eq_lintegral` states it on `ℱₙ`, and
  `integral_comp_flips_eq` as `E^Q[F] = E^P[Z_n · F]`.
* `coinFlipMeasure_trim_equiv`: for `0 < p, q < 1` the two coin-flip laws are equivalent on every
  `ℱₙ`.
* `martingale_binomialDensity`: for `0 < p < 1`, the density process `Z_n = ∏_{i<n} Z(ωᵢ)` is a
  `P`-martingale.

## References

* [S. E. Shreve, *Stochastic Calculus for Finance I: The Binomial Asset Pricing Model*][ShreveSCFI],
  Ch 1

## Tags

discrete Girsanov, change of measure, Radon–Nikodym derivative, risk-neutral measure,
density process, binomial model, MSC 91G20, MSC 60G42, JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

/-- **Radon-Nikodym derivative `dQ/dP`** for the single-period binomial measure
change. At the up state it equals `q/p`; at the down state, `(1−q)/(1−p)`. -/
noncomputable def binomialRN (p q : ℝ) : Bool → ℝ
  | true => q / p
  | false => (1 - q) / (1 - p)

/-- **The one-flip change of measure**: the `P`-probability of a flip outcome times the density
is its `Q`-probability, `P(b) · Z(b) = Q(b)`. Every identity in this file is this one, summed over
the two outcomes (`binomialRN_expectation_one`, `binomial_riskNeutral_via_RN`) or multiplied
over the flips (`map_flips_coinFlipMeasure_eq_withDensity`). -/
lemma weight_mul_binomialRN {p q : ℝ} (hp : p ≠ 0) (hp1 : p ≠ 1) (b : Bool) :
    (if b then p else 1 - p) * binomialRN p q b = if b then q else 1 - q := by
  have h1p : 1 - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  cases b
  · simp only [binomialRN, Bool.false_eq_true, ↓reduceIte]
    field_simp
  · simp only [binomialRN, ↓reduceIte]
    field_simp

lemma binomialRN_nonneg {p q : ℝ} (hp : 0 ≤ p) (hp1 : p < 1) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (b : Bool) : 0 ≤ binomialRN p q b := by
  cases b
  · exact div_nonneg (sub_nonneg.2 hq1) (sub_nonneg.2 hp1.le)
  · exact div_nonneg hq hp

lemma binomialRN_pos {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (hq1 : q < 1) (b : Bool) :
    0 < binomialRN p q b := by
  cases b
  · exact div_pos (sub_pos.2 hq1) (sub_pos.2 hp1)
  · exact div_pos hq hp

/-- **RN normalisation**: `E^P[Z] = 1`, i.e.
`p · (q/p) + (1 − p) · ((1 − q)/(1 − p)) = 1`.

This is the universal "the change of measure preserves total mass"
property, here in two-state form. -/
theorem binomialRN_expectation_one (p q : ℝ)
    (hp : p ≠ 0) (hp1 : p ≠ 1) :
    p * binomialRN p q true + (1 - p) * binomialRN p q false = 1 := by
  have h1 := weight_mul_binomialRN (q := q) hp hp1 true
  have h0 := weight_mul_binomialRN (q := q) hp hp1 false
  simp only [↓reduceIte, Bool.false_eq_true] at h1 h0
  linear_combination h1 + h0

/-- **Discrete Girsanov pricing identity**: under the binomial measure change,
the `Q`-expectation of any payoff equals the `P`-expectation of `Z · payoff`,
where `Z = dQ/dP`:

  `E^Q[V] = q · V_u + (1−q) · V_d = E^P[Z · V] = p · (q/p) · V_u + (1−p) · ((1−q)/(1−p)) · V_d`.

(Both sides simplify to `q · V_u + (1 − q) · V_d`.) -/
theorem binomial_riskNeutral_via_RN (p q V_u V_d : ℝ)
    (hp : p ≠ 0) (hp1 : p ≠ 1) :
    q * V_u + (1 - q) * V_d =
      p * binomialRN p q true * V_u + (1 - p) * binomialRN p q false * V_d := by
  have h1 := weight_mul_binomialRN (q := q) hp hp1 true
  have h0 := weight_mul_binomialRN (q := q) hp hp1 false
  simp only [↓reduceIte, Bool.false_eq_true] at h1 h0
  linear_combination (-V_u) * h1 + (-V_d) * h0

/-- The **density process** `Z_n(ω) = ∏_{i<n} Z(ωᵢ)`: the product of the one-flip densities over
the first `n` flips. -/
noncomputable def binomialDensity (p q : ℝ) (n : ℕ) (ω : ℕ → Bool) : ℝ :=
  ∏ i ∈ range n, binomialRN p q (ω i)

lemma binomialDensity_eq_prod_flips (p q : ℝ) (n : ℕ) (ω : ℕ → Bool) :
    binomialDensity p q n ω = ∏ i, binomialRN p q (flips n ω i) :=
  (Fin.prod_univ_eq_prod_range (fun i ↦ binomialRN p q (ω i)) n).symm

lemma pathAdaptedAt_binomialDensity (p q : ℝ) (n : ℕ) :
    PathAdaptedAt n (binomialDensity p q n) := fun ω ω' h ↦
  prod_congr rfl fun i hi ↦ by rw [h i (mem_range.1 hi)]

lemma binomialDensity_update_succ (p q : ℝ) (n : ℕ) (ω : ℕ → Bool) (b : Bool) :
    binomialDensity p q (n + 1) (Function.update ω n b)
      = binomialDensity p q n ω * binomialRN p q b := by
  rw [binomialDensity, prod_range_succ, binomialDensity]
  simp only [Function.update_self]
  congr 1
  exact prod_congr rfl fun i hi ↦ by rw [Function.update_of_ne (mem_range.1 hi).ne]

section ChangeOfMeasure

variable {p q : ℝ≥0}

/-- **Girsanov on `n` flips.** For `0 < p < 1` and `q ≤ 1`, the law of the first `n` flips under
i.i.d. `Bernoulli(q)` is their law under i.i.d. `Bernoulli(p)` with density the product
`∏ᵢ binomialRN p q (xᵢ)` of the one-flip Radon–Nikodym derivatives. -/
theorem map_flips_coinFlipMeasure_eq_withDensity (hp0 : 0 < p) (hp : p < 1) (hq : q ≤ 1)
    (n : ℕ) :
    (coinFlipMeasure q hq).map (flips n)
      = ((coinFlipMeasure p hp.le).map (flips n)).withDensity
          fun x ↦ ENNReal.ofReal (∏ i, binomialRN p q (x i)) := by
  have hp0' : (p : ℝ) ≠ 0 := (NNReal.coe_pos.2 hp0).ne'
  have hp1' : (p : ℝ) ≠ 1 := (NNReal.coe_lt_one.2 hp).ne
  have hw (r : ℝ≥0) (hr : r ≤ 1) (b : Bool) :
      (if b then (r : ℝ≥0∞) else 1 - r) = ENNReal.ofReal (if b then (r : ℝ) else 1 - r) := by
    cases b
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [ENNReal.ofReal_sub _ (NNReal.coe_nonneg r), ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]
    · simp
  refine Measure.ext_of_singleton fun x ↦ ?_
  rw [Measure.map_apply (measurable_flips n) (measurableSet_singleton x),
    withDensity_apply _ (measurableSet_singleton x), lintegral_singleton,
    Measure.map_apply (measurable_flips n) (measurableSet_singleton x),
    coinFlipMeasure_flips_preimage, coinFlipMeasure_flips_preimage]
  simp_rw [hw q hq, hw p hp.le]
  have hp1r : (p : ℝ) < 1 := NNReal.coe_lt_one.2 hp
  have hq1r : (q : ℝ) ≤ 1 := by exact_mod_cast hq
  have hwq (b : Bool) : 0 ≤ if b then (q : ℝ) else 1 - q := by cases b <;> simp [hq1r]
  have hwp (b : Bool) : 0 ≤ if b then (p : ℝ) else 1 - p := by cases b <;> simp [hp1r.le]
  have hprod : 0 ≤ ∏ i, binomialRN p q (x i) :=
    prod_nonneg fun i _ ↦ binomialRN_nonneg p.2 hp1r q.2 hq1r (x i)
  rw [← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hwq (x i),
    ← ENNReal.ofReal_prod_of_nonneg fun i _ ↦ hwp (x i), ← ENNReal.ofReal_mul hprod]
  congr 1
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ ↦
    ((weight_mul_binomialRN (q := q) hp0' hp1' (x i)).symm.trans (mul_comm _ _))

/-- **Equivalence of the two coin-flip laws on `n` flips.** For `0 < p < 1` and `0 < q < 1` the
density `∏ᵢ binomialRN p q (xᵢ)` is strictly positive, so the laws of the first `n` flips under
`Bernoulli(q)` and `Bernoulli(p)` are mutually absolutely continuous. -/
theorem map_flips_coinFlipMeasure_equiv (hp0 : 0 < p) (hp : p < 1) (hq0 : 0 < q) (hq : q < 1)
    (n : ℕ) :
    (coinFlipMeasure q hq.le).map (flips n) ≪ (coinFlipMeasure p hp.le).map (flips n) ∧
      (coinFlipMeasure p hp.le).map (flips n) ≪ (coinFlipMeasure q hq.le).map (flips n) := by
  rw [map_flips_coinFlipMeasure_eq_withDensity hp0 hp hq.le n]
  exact ⟨withDensity_absolutelyContinuous _ _,
    absolutelyContinuous_withDensity_ofReal _ (measurable_of_countable _).aemeasurable
      (ae_of_all _ fun x ↦ prod_pos fun i _ ↦
        binomialRN_pos (NNReal.coe_pos.2 hp0) (NNReal.coe_lt_one.2 hp) (NNReal.coe_pos.2 hq0)
          (NNReal.coe_lt_one.2 hq) (x i))⟩

/-- **The two coin-flip laws are equivalent on the information `ℱₙ`** of the first `n` flips, for
`0 < p, q < 1`: an event known by time `n` is the preimage of a set of `n`-flip patterns, null under
one law exactly when under the other (`map_flips_coinFlipMeasure_equiv`). (On the whole path space
the two laws are mutually singular when `p ≠ q`, by the strong law of large numbers; that is not
proved here.) -/
theorem coinFlipMeasure_trim_equiv (hp0 : 0 < p) (hp : p < 1) (hq0 : 0 < q) (hq : q < 1)
    (n : ℕ) :
    (coinFlipMeasure q hq.le).trim (flipFiltration.le n)
        ≪ (coinFlipMeasure p hp.le).trim (flipFiltration.le n) ∧
      (coinFlipMeasure p hp.le).trim (flipFiltration.le n)
        ≪ (coinFlipMeasure q hq.le).trim (flipFiltration.le n) := by
  have key {μ ν : Measure (ℕ → Bool)} (h : μ.map (flips n) ≪ ν.map (flips n)) :
      μ.trim (flipFiltration.le n) ≪ ν.trim (flipFiltration.le n) := by
    refine Measure.AbsolutelyContinuous.mk fun A hA h0 ↦ ?_
    obtain ⟨S, hS, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
    rw [trim_measurableSet_eq _ hA, ← Measure.map_apply (measurable_flips n) hS] at h0
    rw [trim_measurableSet_eq _ hA, ← Measure.map_apply (measurable_flips n) hS]
    exact h h0
  obtain ⟨h₁, h₂⟩ := map_flips_coinFlipMeasure_equiv hp0 hp hq0 hq n
  exact ⟨key h₁, key h₂⟩

/-- **The Radon–Nikodym derivative on `ℱₙ`.** Under the hypotheses of
`map_flips_coinFlipMeasure_eq_withDensity`, the `Bernoulli(q)` probability of an event known by
time `n` is the `Bernoulli(p)` integral of the density process `Zₙ = ∏_{i<n} Z(ωᵢ)` over it:
`Z_n = dQ/dP` on `ℱₙ`. -/
theorem coinFlipMeasure_apply_eq_lintegral (hp0 : 0 < p) (hp : p < 1) (hq : q ≤ 1) (n : ℕ)
    {A : Set (ℕ → Bool)} (hA : MeasurableSet[flipFiltration n] A) :
    coinFlipMeasure q hq A
      = ∫⁻ ω in A, ENNReal.ofReal (binomialDensity p q n ω) ∂coinFlipMeasure p hp.le := by
  obtain ⟨T, hT, rfl⟩ := MeasurableSpace.measurableSet_comap.1 hA
  rw [← Measure.map_apply (measurable_flips n) hT,
    map_flips_coinFlipMeasure_eq_withDensity hp0 hp hq n, withDensity_apply _ hT,
    setLIntegral_map hT (measurable_of_countable _) (measurable_flips n)]
  simp only [binomialDensity_eq_prod_flips]

/-- **Girsanov for expectations of `n`-flip functionals**: `E^Q[F(X₁,…,Xₙ)] = E^P[Zₙ · F(X₁,…,Xₙ)]`
for the density process `Zₙ = ∏_{i<n} Z(ωᵢ)`, `P = Bernoulli(p)^⊗ℕ`, `Q = Bernoulli(q)^⊗ℕ`. -/
theorem integral_comp_flips_eq (hp0 : 0 < p) (hp : p < 1) (hq : q ≤ 1) (n : ℕ)
    (F : (Fin n → Bool) → ℝ) :
    ∫ ω, F (flips n ω) ∂coinFlipMeasure q hq
      = ∫ ω, binomialDensity p q n ω * F (flips n ω) ∂coinFlipMeasure p hp.le := by
  have hp0' : (p : ℝ) ≠ 0 := (NNReal.coe_pos.2 hp0).ne'
  have hp1' : (p : ℝ) ≠ 1 := (NNReal.coe_lt_one.2 hp).ne
  simp_rw [binomialDensity_eq_prod_flips]
  rw [integral_comp_flips q hq n F,
    integral_comp_flips p hp.le n fun x ↦ (∏ i, binomialRN p q (x i)) * F x]
  refine sum_congr rfl fun x _ ↦ ?_
  rw [← mul_assoc]
  congr 1
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ ↦
    (weight_mul_binomialRN (q := q) hp0' hp1' (x i)).symm

end ChangeOfMeasure

/-- **The Girsanov density process is a martingale.** Under `P = Bernoulli(p)^⊗ℕ` with
`0 < p < 1`, `Zₙ = ∏_{i<n} Z(ωᵢ)` is a Mathlib `Martingale` for the natural flip filtration; its
one-step node average is `binomialRN_expectation_one`. -/
theorem martingale_binomialDensity {p : ℝ≥0} (hp0 : 0 < p) (hp : p < 1) (c : ℝ) :
    Martingale (binomialDensity p c) flipFiltration (coinFlipMeasure p hp.le) :=
  martingale_of_oneStep hp.le (pathAdaptedAt_binomialDensity p c) fun n ω ↦ by
    rw [binomialDensity_update_succ, binomialDensity_update_succ]
    linear_combination binomialDensity p c n ω *
      binomialRN_expectation_one p c (NNReal.coe_pos.2 hp0).ne' (NNReal.coe_lt_one.2 hp).ne

end MathFin
