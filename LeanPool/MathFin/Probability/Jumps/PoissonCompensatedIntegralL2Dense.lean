/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Jumps.PoissonCompensatedIntegralL2

/-!
# The Itô–Lévy isometry in `L²`-norm form

`Probability/Jumps/PoissonCompensatedIntegralL2.lean` proved the compensated-Poisson isometry with
the
right-hand side written as an explicit sum `∑ⱼ∑ₗ 𝔼[φⱼₗ²]·(tⱼ₊₁−tⱼ)·ν(Aₗ)`. This module recognises
that sum as the `L²`-norm of the *integrand itself* against the product reference measure `P ⊗ ν̂`
(`ν̂ = Leb[0,∞) ⊗ ν`): the simple integrand `H(ω,z) = ∑ⱼ∑ₗ φⱼₗ(ω)·𝟙_{(tⱼ,tⱼ₊₁]×Aₗ}(z)` has

  `∫ H² d(P ⊗ ν̂) = ∑ⱼ∑ₗ 𝔼[φⱼₗ²]·(tⱼ₊₁−tⱼ)·ν(Aₗ)`,

so the isometry becomes the norm identity `𝔼[(∫ H dÑ)²] = ‖H‖²_{L²(dP ⊗ dt ⊗ dν)}` — the shape the
compensated-integral CLM is completed from (`LinearMap.extendOfNorm`) and the shape in which the
Itô–Lévy isometry is usually stated. The integrand-`L²`-norm computation is the jump analogue of
`ItoIntegralL2.simpleProcessL2_norm_sq`, but *simpler*: the grid boxes are pairwise disjoint, so the
cross terms vanish by `ν̂(boxᵢ ∩ boxⱼ) = 0` rather than an interval-overlap formula.

## Provenance

Mirrors our continuous `ItoIntegralL2.simpleProcessL2_norm_sq`; consumes B1
(`compensated_simple_isometry`), whose Poisson-random-measure object's field shape is consulted from
`cgarryZA/LevyStochCalc` (Apache-2.0, cited) — a faithful rendering of Applebaum 2009 Def. 2.3.1.
The isometry proved here (and in B1) is our own: LevyStochCalc states it as its cited **axiom #6**
(`itoIsometry_compensated_unified_existence`); we prove it. The extension to a continuous-integral
CLM over the *characterised* predictable `L²` (their axiom #6 in full generality) needs a
marked-predictable `σ`-algebra + density argument built from scratch for the PRM filtration — a
declared, deferred Summit. Reference: Applebaum, *Lévy Processes and Stochastic Calculus*, CUP 2009,
Thm 4.2.3.

## Main results

* `simpleIntegrand_sq_integral`: for the grid integrand `H(ω, z) = ∑ⱼ∑ₗ φⱼₗ(ω)·𝟙_{(tⱼ,tⱼ₊₁]×Aₗ}(z)`
  with `L²` coefficients, `∫ H² d(P ⊗ ν̂) = ∑ⱼ∑ₗ 𝔼[φⱼₗ²]·(tⱼ₊₁ − tⱼ)·ν(Aₗ).toReal`.
* `compensated_integral_isometry`: for adapted `L²` coefficients, the squared compensated integral
  of `H` has `𝔼[(∑ⱼ∑ₗ φⱼₗ Ñ((tⱼ, tⱼ₊₁] × Aₗ))²] = ∫ H² d(P ⊗ ν̂)`.

## References

* [Applebaum (2009)][Applebaum2009], Thm 4.2.3
* [*cgarryZA/LevyStochCalc*][LevyStochCalc], cited axiom #6

## Tags

Itô–Lévy isometry, L2 norm identity, compensated Poisson integral, reference intensity measure,
jump integrand, MSC 60G51, MSC 60H05, MSC 60G55
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E]
  {P : Measure Ω} [IsProbabilityMeasure P] {ν : Measure E} [SigmaFinite ν]

/-- **The integrand's `L²`-norm² equals the isometry's right-hand side.** For the grid simple
integrand `H(ω,z) = ∑ⱼ∑ₗ φⱼₗ(ω)·𝟙_{(tⱼ,tⱼ₊₁]×Aₗ}(z)`,
`∫ H² d(P ⊗ ν̂) = ∑ⱼ∑ₗ 𝔼[φⱼₗ²]·(tⱼ₊₁−tⱼ)·ν(Aₗ)`. The square expands into a grid double sum; each
product integral factorises (Fubini, `integral_prod_mul`) into `𝔼[φᵢφⱼ]·ν̂(boxᵢ ∩ boxⱼ).toReal`,
which is `0` off the diagonal (disjoint boxes) and `𝔼[φⱼₗ²]·(tⱼ₊₁−tⱼ)·ν(Aₗ)` on it. -/
theorem simpleIntegrand_sq_integral
    {Nt m : ℕ} {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (hmono : Monotone t)
    {A : ℕ → Set E} (hAms : ∀ l, MeasurableSet (A l)) (hAfin : ∀ l, ν (A l) ≠ ⊤)
    (hAdisj : Pairwise (Function.onFun Disjoint A))
    {φ : ℕ → ℕ → Ω → ℝ} (hmemLp : ∀ j l, MemLp (φ j l) 2 P) :
    ∫ p, (∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
            φ j l p.1
              * (Set.Ioc (t j) (t (j + 1)) ×ˢ A l).indicator (fun _ => (1 : ℝ)) p.2) ^ 2
          ∂(P.prod (referenceIntensity ν))
      = ∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
          (∫ ω, (φ j l ω) ^ 2 ∂P) * ((t (j + 1) - t j) * (ν (A l)).toReal) := by
  classical
  -- box of a pair index, and the elementary term
  set box : ℕ × ℕ → Set (ℝ × E) := fun i => Set.Ioc (t i.1) (t (i.1 + 1)) ×ˢ A i.2 with hbox
  set a : ℕ × ℕ → (Ω × (ℝ × E)) → ℝ :=
    fun i p => φ i.1 i.2 p.1 * (box i).indicator (fun _ => (1 : ℝ)) p.2 with ha
  set I : Finset (ℕ × ℕ) := Finset.range Nt ×ˢ Finset.range m with hI
  have ht0j : ∀ j, 0 ≤ t j := fun j => le_trans ht0 (hmono (Nat.zero_le j))
  have hboxms : ∀ i : ℕ × ℕ, MeasurableSet (box i) := fun i => measurableSet_Ioc.prod (hAms i.2)
  have hboxfin : ∀ i : ℕ × ℕ, referenceIntensity ν (box i) ≠ ⊤ :=
    fun i => referenceIntensity_box_ne_top (hAfin i.2)
  -- indicator product = indicator of the intersection
  have hind : ∀ i j : ℕ × ℕ,
      (fun z => (box i).indicator (fun _ => (1 : ℝ)) z * (box j).indicator (fun _ => (1 : ℝ)) z)
        = (box i ∩ box j).indicator (fun _ => (1 : ℝ)) := by
    intro i j; funext z
    by_cases hzi : z ∈ box i <;> by_cases hzj : z ∈ box j <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, hzi, hzj]
  -- coefficient products are `L¹`; indicator products are `L¹` on the finite boxes
  have hφint : ∀ i j : ℕ × ℕ, Integrable (fun ω => φ i.1 i.2 ω * φ j.1 j.2 ω) P :=
    fun i j => (hmemLp i.1 i.2).integrable_mul (hmemLp j.1 j.2)
  have hGint : ∀ i j : ℕ × ℕ, Integrable
      (fun z => (box i).indicator (fun _ => (1 : ℝ)) z * (box j).indicator (fun _ => (1 : ℝ)) z)
      (referenceIntensity ν) := by
    intro i j
    rw [hind i j]
    exact (integrable_indicator_iff ((hboxms i).inter (hboxms j))).mpr
      (integrableOn_const (hs := (lt_of_le_of_lt (measure_mono Set.inter_subset_left)
        (hboxfin i).lt_top).ne))
  -- product term: shape, integrability, value
  have hprodform : ∀ i j : ℕ × ℕ, (fun p : Ω × (ℝ × E) => a i p * a j p)
      = fun p => (φ i.1 i.2 p.1 * φ j.1 j.2 p.1)
          * ((box i).indicator (fun _ => (1 : ℝ)) p.2 *
              (box j).indicator (fun _ => (1 : ℝ)) p.2) := by
    intro i j; funext p; simp only [ha]; ring
  have hint : ∀ i j : ℕ × ℕ,
      Integrable (fun p => a i p * a j p) (P.prod (referenceIntensity ν)) := by
    intro i j; rw [hprodform i j]; exact (hφint i j).mul_prod (hGint i j)
  have hterm : ∀ i j : ℕ × ℕ, ∫ p, a i p * a j p ∂(P.prod (referenceIntensity ν))
      = (∫ ω, φ i.1 i.2 ω * φ j.1 j.2 ω ∂P) * (referenceIntensity ν (box i ∩ box j)).toReal := by
    intro i j
    rw [hprodform i j, integral_prod_mul (fun ω => φ i.1 i.2 ω * φ j.1 j.2 ω)
        (fun z => (box i).indicator (fun _ => (1 : ℝ)) z * (box j).indicator (fun _ => (1 : ℝ)) z),
        hind i j, integral_indicator ((hboxms i).inter (hboxms j)), setIntegral_const,
        smul_eq_mul, mul_one, measureReal_def]
  -- distinct grid boxes are disjoint (time-index apart ⇒ disjoint in time; else in mark)
  have hdisj : ∀ i j : ℕ × ℕ, i ≠ j → Disjoint (box i) (box j) := by
    intro i j hij
    rcases lt_trichotomy i.1 j.1 with hlt | heq | hgt
    · have hle : t (i.1 + 1) ≤ t j.1 := hmono (Nat.succ_le_of_lt hlt)
      rw [hbox, Set.disjoint_left]
      rintro z hz1 hz2
      exact absurd (le_trans (Set.mem_Ioc.mp (Set.mem_prod.mp hz1).1).2 hle)
        (not_le.mpr (Set.mem_Ioc.mp (Set.mem_prod.mp hz2).1).1)
    · have hlm : i.2 ≠ j.2 := fun h => hij (Prod.ext heq h)
      rw [hbox, Set.disjoint_left]
      rintro z hz1 hz2
      exact (Set.disjoint_left.mp (hAdisj hlm)) (Set.mem_prod.mp hz1).2 (Set.mem_prod.mp hz2).2
    · have hle : t (j.1 + 1) ≤ t i.1 := hmono (Nat.succ_le_of_lt hgt)
      rw [hbox, Set.disjoint_left]
      rintro z hz1 hz2
      exact absurd (le_trans (Set.mem_Ioc.mp (Set.mem_prod.mp hz2).1).2 hle)
        (not_le.mpr (Set.mem_Ioc.mp (Set.mem_prod.mp hz1).1).1)
  -- fold the nested grid sum into a single pair sum
  have hsum : ∀ p, (∑ i ∈ I, a i p)
      = ∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
          φ j l p.1
            * (Set.Ioc (t j) (t (j + 1)) ×ˢ A l).indicator (fun _ => (1 : ℝ)) p.2 := by
    intro p; simp only [hI, Finset.sum_product, ha, hbox]
  calc ∫ p, (∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
              φ j l p.1
                * (Set.Ioc (t j) (t (j + 1)) ×ˢ A l).indicator (fun _ => (1 : ℝ)) p.2) ^ 2
            ∂(P.prod (referenceIntensity ν))
      = ∫ p, ∑ i ∈ I, ∑ j ∈ I, a i p * a j p ∂(P.prod (referenceIntensity ν)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
        change (∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
              φ j l p.1
                * (Set.Ioc (t j) (t (j + 1)) ×ˢ A l).indicator (fun _ => (1 : ℝ)) p.2) ^ 2
            = ∑ i ∈ I, ∑ j ∈ I, a i p * a j p
        rw [← hsum p, pow_two, Finset.sum_mul_sum]
    _ = ∑ i ∈ I, ∑ j ∈ I, ∫ p, a i p * a j p ∂(P.prod (referenceIntensity ν)) := by
        rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => hint i j)]
        exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => hint i j
    _ = ∑ i ∈ I, ∫ p, a i p * a i p ∂(P.prod (referenceIntensity ν)) := by
        refine Finset.sum_congr rfl fun i hi => ?_
        refine Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi' => absurd hi hi')
        rw [hterm i j, Set.disjoint_iff_inter_eq_empty.mp (hdisj i j (Ne.symm hji)),
          measure_empty, ENNReal.toReal_zero, mul_zero]
    _ = ∑ i ∈ I, (∫ ω, (φ i.1 i.2 ω) ^ 2 ∂P) * ((t (i.1 + 1) - t i.1) * (ν (A i.2)).toReal) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hterm i i, Set.inter_self, hbox,
          referenceIntensity_box_toReal (ν := ν) (ht0j i.1) (hmono (Nat.le_succ i.1))]
        congr 1
        exact integral_congr_ae (Filter.Eventually.of_forall fun ω => (pow_two (φ i.1 i.2 ω)).symm)
    _ = ∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
          (∫ ω, (φ j l ω) ^ 2 ∂P) * ((t (j + 1) - t j) * (ν (A l)).toReal) := by
        simp only [hI, Finset.sum_product]

/-- **The Itô–Lévy isometry in norm form.** `𝔼[(∫ H dÑ)²] = ‖H‖²_{L²(dP ⊗ dt ⊗ dν)}`: the
compensated integral of the simple integrand `H(ω,z) = ∑ⱼ∑ₗ φⱼₗ(ω)·𝟙_{(tⱼ,tⱼ₊₁]×Aₗ}(z)` has the same
`L²(P)`-norm as `H` has in `L²(P ⊗ ν̂)`. Combines B1's `compensated_simple_isometry` with the
integrand-norm computation; this is the norm identity the compensated-integral CLM completes from.
-/
theorem compensated_integral_isometry (N : PoissonRandomMeasure P ν)
    {Nt m : ℕ} {t : ℕ → ℝ} (ht0 : 0 ≤ t 0) (hmono : Monotone t)
    {A : ℕ → Set E} (hAms : ∀ l, MeasurableSet (A l)) (hAfin : ∀ l, ν (A l) ≠ ⊤)
    (hAdisj : Pairwise (Function.onFun Disjoint A))
    {φ : ℕ → ℕ → Ω → ℝ} (hadapt : ∀ j l, Measurable[N.pastFiltration (t j)] (φ j l))
    (hmemLp : ∀ j l, MemLp (φ j l) 2 P) :
    ∫ ω, (∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
            φ j l ω * N.compensated (Set.Ioc (t j) (t (j + 1)) ×ˢ A l) ω) ^ 2 ∂P
      = ∫ p, (∑ j ∈ Finset.range Nt, ∑ l ∈ Finset.range m,
            φ j l p.1
              * (Set.Ioc (t j) (t (j + 1)) ×ˢ A l).indicator (fun _ => (1 : ℝ)) p.2) ^ 2
          ∂(P.prod (referenceIntensity ν)) := by
  rw [compensated_simple_isometry N ht0 hmono hAms hAfin hAdisj hadapt hmemLp,
      simpleIntegrand_sq_integral ht0 hmono hAms hAfin hAdisj hmemLp]

end MathFin
