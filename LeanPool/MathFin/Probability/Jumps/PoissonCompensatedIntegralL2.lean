/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Jumps.PoissonCompensatedIsometryAdapted

/-!
# The Itô–Lévy isometry for simple integrands

The jump analogue of `Probability/Brownian/Ito/ItoIsometryAdapted.lean`'s `ito_isometry_discrete` —
the genuine
compensated-Poisson `L²` isometry for a *simple predictable* integrand over a `time × mark` grid.
For a time partition `t₀ ≤ t₁ ≤ ⋯`, disjoint finite-intensity marks `A₀, …, A_{m-1}`, and
coefficients `φⱼₗ` each adapted at `tⱼ` and in `L²`,

  `𝔼[(∑ⱼ ∑ₗ φⱼₗ · Ñ((tⱼ,tⱼ₊₁] × Aₗ))²] = ∑ⱼ ∑ₗ 𝔼[φⱼₗ²] · (tⱼ₊₁ − tⱼ) · ν(Aₗ)`,

the right-hand side being `‖φ‖²` in `L²(dP ⊗ dt ⊗ dν)`. The square expands into a grid-indexed
double sum; every off-diagonal pair vanishes by `integral_cross_compensated_eq_zero` — different
time blocks are disjoint in time, same-block/different-mark pairs are disjoint in the mark — and the
diagonal is `integral_adapted_sq_mul_compensated_sq`. This is `full`: the real second-moment
computation, not a definitional identity.

## Provenance

Design mirrors our continuous Itô `ito_isometry_discrete`; the PRM kernel is from
`Probability/Jumps/PoissonCompensatedIsometryAdapted` (PRM field shape consulted from
`cgarryZA/LevyStochCalc`, cited). LevyStochCalc states this isometry as its cited axiom #6; here it
is proved. References: Applebaum, *Lévy Processes and Stochastic Calculus*, CUP 2009, Thm 4.2.3.

## Main results

* `compensated_simple_isometry`: for a monotone time grid `t` with `0 ≤ t 0`, disjoint
  finite-intensity marks `A l`, and `L²` coefficients `φ j l` adapted at `t j`,
  `𝔼[(∑ⱼ∑ₗ φⱼₗ Ñ((tⱼ, tⱼ₊₁] × Aₗ))²] = ∑ⱼ∑ₗ 𝔼[φⱼₗ²]·(tⱼ₊₁ − tⱼ)·ν(Aₗ).toReal`.

## References

* [Applebaum (2009)][Applebaum2009], Thm 4.2.3
* [*cgarryZA/LevyStochCalc*][LevyStochCalc], cited axiom #6

## Tags

Itô–Lévy isometry, compensated Poisson integral, jump process integral,
simple predictable integrand, Lévy stochastic calculus, MSC 60G51, MSC 60H05, MSC 60G55
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- **The Itô–Lévy isometry for simple integrands.** For a monotone time partition `t` (with
`0 ≤ t 0`), pairwise-disjoint finite-intensity marks `A`, and coefficients `φ j l` adapted at
`t j` and in `L²`,

  `𝔼[(∑ⱼ ∑ₗ φⱼₗ · Ñ((tⱼ,tⱼ₊₁] × Aₗ))²] = ∑ⱼ ∑ₗ 𝔼[φⱼₗ²] · (tⱼ₊₁ − tⱼ) · ν(Aₗ)`. -/
theorem compensated_simple_isometry (N : PoissonRandomMeasure P ν)
    {Nt m : ℕ} {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (hmono : Monotone t)
    {A : ℕ → Set E} (hAms : ∀ l, MeasurableSet (A l)) (hAfin : ∀ l, ν (A l) ≠ ⊤)
    (hAdisj : Pairwise (Function.onFun Disjoint A))
    {φ : ℕ → ℕ → Ω → ℝ} (hadapt : ∀ j l, Measurable[N.pastFiltration (t j)] (φ j l))
    (hmemLp : ∀ j l, MemLp (φ j l) 2 P) :
    ∫ ω, (∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
            φ j l ω * N.compensated (Set.Ioc (t j) (t (j + 1)) ×ˢ A l) ω) ^ 2 ∂P
      = ∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
          (∫ ω, (φ j l ω) ^ 2 ∂P) * ((t (j + 1) - t j) * (ν (A l)).toReal) := by
  classical
  set a : ℕ × ℕ → Ω → ℝ :=
    fun p ω => φ p.1 p.2 ω * N.compensated (Set.Ioc (t p.1) (t (p.1 + 1)) ×ˢ A p.2) ω with ha
  set I : Finset (ℕ × ℕ) := Finset.range Nt ×ˢ Finset.range m with hI
  have ht0j : ∀ j, 0 ≤ t j := fun j => le_trans ht0 (hmono (Nat.zero_le j))
  -- each grid term is `L²`, so every product is integrable
  have haL2 : ∀ p, MemLp (a p) 2 P := fun p =>
    memLp_adapted_mul_compensated N (hAms p.2) (hAfin p.2) (hadapt p.1 p.2) (hmemLp p.1 p.2)
  have hint : ∀ p q, Integrable (fun ω => a p ω * a q ω) P :=
    fun p q => (haL2 p).integrable_mul (haL2 q)
  -- boxes disjoint in time when the earlier time-index precedes the later
  have hdisjT : ∀ p q : ℕ × ℕ, p.1 < q.1 →
      Disjoint (Set.Ioc (t p.1) (t (p.1 + 1)) ×ˢ A p.2)
        (Set.Ioc (t q.1) (t (q.1 + 1)) ×ˢ A q.2) := by
    intro p q hlt
    have hle : t (p.1 + 1) ≤ t q.1 := hmono (Nat.succ_le_of_lt hlt)
    rw [Set.disjoint_left]
    rintro z hz1 hz2
    exact absurd (le_trans (Set.mem_Ioc.mp (Set.mem_prod.mp hz1).1).2 hle)
      (not_le.mpr (Set.mem_Ioc.mp (Set.mem_prod.mp hz2).1).1)
  -- boxes disjoint in the mark when the marks differ
  have hdisjM : ∀ p q : ℕ × ℕ, p.2 ≠ q.2 →
      Disjoint (Set.Ioc (t p.1) (t (p.1 + 1)) ×ˢ A p.2)
        (Set.Ioc (t q.1) (t (q.1 + 1)) ×ˢ A q.2) := by
    intro p q hlm
    rw [Set.disjoint_left]
    rintro z hz1 hz2
    exact (Set.disjoint_left.mp (hAdisj hlm)) (Set.mem_prod.mp hz1).2 (Set.mem_prod.mp hz2).2
  -- oriented cross-term (later time-index carries the fresh increment)
  have cross_oriented : ∀ p q : ℕ × ℕ, t p.1 ≤ t q.1 →
      Disjoint (Set.Ioc (t p.1) (t (p.1 + 1)) ×ˢ A p.2)
        (Set.Ioc (t q.1) (t (q.1 + 1)) ×ˢ A q.2) → ∫ ω, a p ω * a q ω ∂P = 0 :=
    fun p q hab hdisj => integral_cross_compensated_eq_zero N hab
      (measurableSet_Ioc.prod (hAms p.2)) (hAms q.2) (hAfin q.2) hdisj
      (hadapt p.1 p.2) (hadapt q.1 q.2)
  -- every off-diagonal pair vanishes
  have cross_zero : ∀ p q : ℕ × ℕ, p ≠ q → ∫ ω, a p ω * a q ω ∂P = 0 := by
    intro p q hpq
    rcases lt_trichotomy p.1 q.1 with hlt | heq | hgt
    · exact cross_oriented p q (hmono hlt.le) (hdisjT p q hlt)
    · exact cross_oriented p q (le_of_eq (congrArg t heq))
        (hdisjM p q (fun h => hpq (Prod.ext heq h)))
    · rw [show (fun ω => a p ω * a q ω) = (fun ω => a q ω * a p ω) from
            funext fun ω => mul_comm _ _]
      exact cross_oriented q p (hmono hgt.le) (hdisjT q p hgt)
  -- diagonal energy
  have diag_eval : ∀ p : ℕ × ℕ, ∫ ω, a p ω * a p ω ∂P
      = (∫ ω, (φ p.1 p.2 ω) ^ 2 ∂P) * ((t (p.1 + 1) - t p.1) * (ν (A p.2)).toReal) := by
    intro p
    have h1 : (fun ω => a p ω * a p ω)
        = fun ω => (φ p.1 p.2 ω) ^ 2
            * (N.compensated (Set.Ioc (t p.1) (t (p.1 + 1)) ×ˢ A p.2) ω) ^ 2 := by
      funext ω; simp only [ha]; ring
    rw [h1, integral_adapted_sq_mul_compensated_sq N (hAms p.2) (hAfin p.2) (hadapt p.1 p.2),
        referenceIntensity_box_toReal (ht0j p.1) (hmono (Nat.le_succ p.1))]
  -- fold nested grid sums into a single pair sum
  have hsum : ∀ ω, (∑ p ∈ I, a p ω)
      = ∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
          φ j l ω * N.compensated (Set.Ioc (t j) (t (j + 1)) ×ˢ A l) ω := by
    intro ω; simp only [hI, Finset.sum_product, ha]
  calc ∫ ω, (∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
              φ j l ω * N.compensated (Set.Ioc (t j) (t (j + 1)) ×ˢ A l) ω) ^ 2 ∂P
      = ∫ ω, ∑ p ∈ I, ∑ q ∈ I, a p ω * a q ω ∂P := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
        change (∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
              φ j l ω * N.compensated (Set.Ioc (t j) (t (j + 1)) ×ˢ A l) ω) ^ 2
            = ∑ p ∈ I, ∑ q ∈ I, a p ω * a q ω
        rw [← hsum ω, pow_two, Finset.sum_mul_sum]
    _ = ∑ p ∈ I, ∑ q ∈ I, ∫ ω, a p ω * a q ω ∂P := by
        rw [integral_finsetSum _ (fun p _ => integrable_finsetSum _ fun q _ => hint p q)]
        exact Finset.sum_congr rfl fun p _ => integral_finsetSum _ fun q _ => hint p q
    _ = ∑ p ∈ I, ∫ ω, a p ω * a p ω ∂P := by
        refine Finset.sum_congr rfl fun p hp => ?_
        exact Finset.sum_eq_single p (fun q _ hqp => cross_zero p q (Ne.symm hqp))
          (fun hp' => absurd hp hp')
    _ = ∑ p ∈ I, (∫ ω, (φ p.1 p.2 ω) ^ 2 ∂P) * ((t (p.1 + 1) - t p.1) * (ν (A p.2)).toReal) :=
        Finset.sum_congr rfl fun p _ => diag_eval p
    _ = ∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
          (∫ ω, (φ j l ω) ^ 2 ∂P) * ((t (j + 1) - t j) * (ν (A l)).toReal) := by
        simp only [hI, Finset.sum_product]

end MathFin
