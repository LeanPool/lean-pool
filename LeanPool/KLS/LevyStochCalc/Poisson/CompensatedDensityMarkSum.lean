/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Lean Pool port: project-qualified imports and Lean Pool style.
-- Modified 2026-10-27 by the KLS formalization project: update deprecated aliases and
-- proof-local bindings for warning-free Lean v4.33.0 builds; see vendor/port.patch.

-- Modified 2026-10-31 by the KLS formalization project: ported to the Lean module system
-- (module header, public imports, exposed public section) for Lean/Mathlib v4.35.0.
module

public import LeanPool.KLS.LevyStochCalc.Poisson.CompensatedDensityBoxIsometry

/-!
# The mark-sum process and its `L²` isometry

The process `∑ᵢ ∑ₖ ξᵢₖ Ñ((tᵢ, tᵢ₊₁] × Bₖ)` attached to adapted bounded coefficients, its second
moment as the `L²(P ⊗ ds ⊗ ν)` energy of the associated integrand, and the isometry for the
difference of two such processes. The energy is computed from the product form of the reference
intensity on time-mark boxes; completeness of `L²(P)` then turns a Cauchy sequence of such
processes into a limit.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson.Compensated

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- **Mark-sum square at one time interval (overlapping marks).** For a single interval
`(a,b]`, arbitrary marks `B k`, and adapted bounded coeffs `ξ k`,
`E[(∑ₖ ξₖ Ñ((a,b]×Bₖ))²] = ∑ₖ ∑ₖ' ν̂((a,b]×(Bₖ∩Bₖ'))·E[ξₖ·ξₖ']`. Expand the square and
apply the weighted same-time bilinear covariance to each `(k,k')` term. -/
lemma markSum_sq_sametime
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) {K : ℕ}
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin K → Ω → ℝ) (hξb : ∀ k, ∃ M, ∀ ω, |ξ k ω| ≤ M) (hξm : ∀ k, Measurable (ξ k))
    (hadapt : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) (ξ k)) :
    ∫ ω, (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω) ^ 2 ∂P
      = ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ k ω * ξ k' ω ∂P := by
  have hBxm : ∀ k, MeasurableSet (Set.Ioc a b ×ˢ B k) := fun k => measurableSet_Ioc.prod (hBm k)
  have hBxf : ∀ k, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ B k) ≠ ⊤ :=
    fun k => referenceIntensity_Ioc_prod_ne_top (hBf k)
  -- integrability of each cross term.
  have hint : ∀ k k', MeasureTheory.Integrable
      (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
        * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω)) P := by
    intro k k'
    obtain ⟨Mk, hMk⟩ := hξb k
    obtain ⟨Mk', hMk'⟩ := hξb k'
    have hcross := compensated_cross_integrable N (hBxm k) (hBxm k') (hBxf k) (hBxf k')
    have heq : (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω))
        = (fun ω => (ξ k ω * ξ k' ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc a b ×ˢ B k') ω)) := funext (fun ω => by ring)
    rw [heq]
    refine hcross.bdd_mul (c := Mk * Mk') ((hξm k).mul (hξm k')).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMk ω) (hMk' ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
  rw [show (fun ω => (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω) ^ 2)
      = fun ω => ∑ k : Fin K, ∑ k' : Fin K,
          (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω) from
    funext (fun ω => by rw [sq]; exact Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun k _ => MeasureTheory.integrable_finsetSum _
      (fun k' _ => hint k k'))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => hint k k')]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  obtain ⟨Mk, hMk⟩ := hξb k
  obtain ⟨Mk', hMk'⟩ := hξb k'
  have hbnd : ∀ ω, |ξ k ω * ξ k' ω| ≤ Mk * Mk' := fun ω => by
    rw [abs_mul]
    exact mul_le_mul (hMk ω) (hMk' ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
  have hgadapt : @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) (fun ω => ξ k ω * ξ k' ω) :=
    (hadapt k).mul (hadapt k')
  rw [show (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ξ k' ω * N.compensated (Set.Ioc a b ×ˢ B k') ω))
        = fun ω => (ξ k ω * ξ k' ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc a b ×ˢ B k') ω) from funext (fun ω => by ring),
    weighted_box_cross_sametime N ℱ hℱ ha hab (hBm k) (hBm k') (hBf k) (hBf k') hgadapt hbnd,
    mul_comm]

/-- **Cross of mark-sums over time-ordered intervals vanishes.** For two intervals
`(a,b]`, `(c,d]` with `b ≤ c`, marks `B`, coeffs `ξ` (adapted at `a`) and `ζ` (adapted
at `c`), `E[(∑ₖ ξₖ Ñ((a,b]×Bₖ))·(∑ₗ ζₗ Ñ((c,d]×Bₗ))] = 0`. Each `(k,l)` term vanishes
by `weighted_box_cross_timeordered_zero`. -/
lemma markSum_cross_timeordered
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {a b c d : ℝ} (hc : 0 ≤ c) (hab : a < b) (hbc : b ≤ c) (hcd : c < d) {K : ℕ}
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ ζ : Fin K → Ω → ℝ)
    (hξb : ∀ k, ∃ M, ∀ ω, |ξ k ω| ≤ M) (hζb : ∀ k, ∃ M, ∀ ω, |ζ k ω| ≤ M)
    (hξm : ∀ k, Measurable (ξ k)) (hζm : ∀ k, Measurable (ζ k))
    (hξadapt : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ a) (ξ k))
    (hζadapt : ∀ k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ c) (ζ k)) :
    ∫ ω, (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
        * (∑ l : Fin K, ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω) ∂P = 0 := by
  have hac : a ≤ c := hab.le.trans hbc
  have hBxm : ∀ k, MeasurableSet (Set.Ioc a b ×ˢ B k) := fun k => measurableSet_Ioc.prod (hBm k)
  have hCxm : ∀ l, MeasurableSet (Set.Ioc c d ×ˢ B l) := fun l => measurableSet_Ioc.prod (hBm l)
  have hBxf : ∀ k, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ B k) ≠ ⊤ :=
    fun k => referenceIntensity_Ioc_prod_ne_top (hBf k)
  have hCxf : ∀ l, LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc c d ×ˢ B l) ≠ ⊤ :=
    fun l => referenceIntensity_Ioc_prod_ne_top (hBf l)
  have hint : ∀ k l, MeasureTheory.Integrable
      (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
        * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω)) P := by
    intro k l
    obtain ⟨Mk, hMk⟩ := hξb k
    obtain ⟨Ml, hMl⟩ := hζb l
    have hcross := compensated_cross_integrable N (hBxm k) (hCxm l) (hBxf k) (hCxf l)
    have heq : (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω))
        = (fun ω => (ξ k ω * ζ l ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc c d ×ˢ B l) ω)) := funext (fun ω => by ring)
    rw [heq]
    refine hcross.bdd_mul (c := Mk * Ml) ((hξm k).mul (hζm l)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => ?_))
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hMk ω) (hMl ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
  rw [show (fun ω => (∑ k : Fin K, ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (∑ l : Fin K, ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω))
      = fun ω => ∑ k : Fin K, ∑ l : Fin K,
          (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω) from
    funext (fun ω => Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun k _ => MeasureTheory.integrable_finsetSum _
      (fun l _ => hint k l))]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun l _ => hint k l)]
  refine Finset.sum_eq_zero (fun l _ => ?_)
  have hgadapt : @MeasureTheory.StronglyMeasurable Ω ℝ _ (ℱ.seq c) (fun ω => ξ k ω * ζ l ω) :=
    ((hξadapt k).mono (ℱ.mono hac)).mul (hζadapt l)
  rw [show (fun ω => (ξ k ω * N.compensated (Set.Ioc a b ×ˢ B k) ω)
          * (ζ l ω * N.compensated (Set.Ioc c d ×ˢ B l) ω))
        = fun ω => (ξ k ω * ζ l ω)
          * (N.compensated (Set.Ioc a b ×ˢ B k) ω
            * N.compensated (Set.Ioc c d ×ˢ B l) ω) from funext (fun ω => by ring)]
  exact weighted_box_cross_timeordered_zero N ℱ hℱ hc hbc hcd (hBm k) (hBm l) (hBf l) hgadapt

/-- **Overlapping-mark step-integral isometry (sum form).** For a shared partition `p`,
arbitrary marks `B`, adapted bounded coeffs `ξ`,
`E[(∑ᵢ ∑ₖ ξᵢₖ Ñ((pᵢ,pᵢ₊₁]×Bₖ))²] = ∑ᵢ ∑ₖ ∑ₖ' ν̂((pᵢ,pᵢ₊₁]×(Bₖ∩Bₖ'))·E[ξᵢₖ·ξᵢₖ']`.
The `i`-level expansion: diagonal `E[markSumᵢ²]` by `markSum_sq_sametime`, off-diagonal
(time-ordered) by `markSum_cross_timeordered`. **No disjointness on the marks.** -/
lemma markSumProcess_isometry
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k))
    (h_adapt : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ i k)) :
    ∫ ω, (∑ i : Fin N₀, ∑ k : Fin K,
        ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2 ∂P
      = ∑ i : Fin N₀, ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ i k ω * ξ i k' ω ∂P := by
  have hpnn : ∀ j : Fin (N₀ + 1), 0 ≤ p j := fun j => by
    have := hpmono.monotone (Fin.zero_le j); rwa [hp0] at this
  have hlt : ∀ i : Fin N₀, p i.castSucc < p i.succ := fun i => hpmono Fin.castSucc_lt_succ
  -- mark-sum at time-piece `i`.
  set S : Fin N₀ → Ω → ℝ := fun i ω =>
    ∑ k : Fin K, ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω with hSdef
  -- integrability of `Sᵢ · Sᵢ'` (finite sum of integrable cross terms).
  have hSS : ∀ i i', MeasureTheory.Integrable (fun ω => S i ω * S i' ω) P := by
    intro i i'
    have hbox : ∀ (j : Fin N₀) (k : Fin K),
        MeasurableSet (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ B k) :=
      fun j k => measurableSet_Ioc.prod (hBm k)
    have hboxf : ∀ (j : Fin N₀) (k : Fin K),
        LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p j.castSucc) (p j.succ) ×ˢ B k) ≠ ⊤ :=
      fun j k => referenceIntensity_Ioc_prod_ne_top (hBf k)
    have hterm : ∀ k l, MeasureTheory.Integrable
        (fun ω => (ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
          * (ξ i' l ω * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω)) P := by
      intro k l
      obtain ⟨Mk, hMk⟩ := hξb i k
      obtain ⟨Ml, hMl⟩ := hξb i' l
      have hcross := compensated_cross_integrable N (hbox i k) (hbox i' l)
        (hboxf i k) (hboxf i' l)
      rw [show (fun ω => (ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
            * (ξ i' l ω * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω))
          = (fun ω => (ξ i k ω * ξ i' l ω)
            * (N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω
              * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω))
          from funext (fun ω => by ring)]
      refine hcross.bdd_mul (c := Mk * Ml) ((hξm i k).mul (hξm i' l)).aestronglyMeasurable
        (Filter.Eventually.of_forall (fun ω => ?_))
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hMk ω) (hMl ω) (abs_nonneg _) ((abs_nonneg _).trans (hMk ω))
    rw [show (fun ω => S i ω * S i' ω)
        = fun ω => ∑ k : Fin K, ∑ l : Fin K,
            (ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
            * (ξ i' l ω * N.compensated (Set.Ioc (p i'.castSucc) (p i'.succ) ×ˢ B l) ω) from
      funext (fun ω => by rw [hSdef]; exact Finset.sum_mul_sum _ _ _ _)]
    exact MeasureTheory.integrable_finsetSum _
      (fun k _ => MeasureTheory.integrable_finsetSum _ (fun l _ => hterm k l))
  -- expand `(∑ᵢ Sᵢ)²` and integrate.
  rw [show (fun ω => (∑ i : Fin N₀, ∑ k : Fin K,
          ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2)
      = fun ω => ∑ i : Fin N₀, ∑ i' : Fin N₀, S i ω * S i' ω from
    funext (fun ω => by rw [sq]; exact Finset.sum_mul_sum _ _ _ _),
    MeasureTheory.integral_finsetSum _ (fun i _ => MeasureTheory.integrable_finsetSum _
      (fun i' _ => hSS i i'))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun i' _ => hSS i i'), Finset.sum_eq_single i]
  · -- diagonal `i' = i`: `∫ Sᵢ² = markSum_sq_sametime`.
    rw [show (fun ω => S i ω * S i ω) = fun ω => (S i ω) ^ 2 from funext (fun ω => (sq _).symm)]
    exact markSum_sq_sametime N ℱ hℱ (hpnn _) (hlt i) B hBm hBf (fun k => ξ i k)
      (fun k => hξb i k) (fun k => hξm i k) (fun k => h_adapt i k)
  · -- off-diagonal `i' ≠ i`: time-ordered, vanishes.
    intro i' _ hi'
    rcases lt_trichotomy i i' with hlt' | hlt' | hlt'
    · have hbc : p i.succ ≤ p i'.castSucc :=
      hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hlt')
      exact markSum_cross_timeordered N ℱ hℱ (hpnn _) (hlt i) hbc (hlt i') B hBm hBf
        (fun k => ξ i k) (fun k => ξ i' k) (fun k => hξb i k) (fun k => hξb i' k)
        (fun k => hξm i k) (fun k => hξm i' k) (fun k => h_adapt i k) (fun k => h_adapt i' k)
    · exact absurd hlt' hi'.symm
    · have hbc : p i'.succ ≤ p i.castSucc :=
      hpmono.monotone (Fin.succ_le_castSucc_iff.mpr hlt')
      rw [show (fun ω => S i ω * S i' ω) = fun ω => S i' ω * S i ω from funext (fun ω => by ring)]
      exact markSum_cross_timeordered N ℱ hℱ (hpnn _) (hlt i') hbc (hlt i) B hBm hBf
        (fun k => ξ i' k) (fun k => ξ i k) (fun k => hξb i' k) (fun k => hξb i k)
        (fun k => hξm i' k) (fun k => hξm i k) (fun k => h_adapt i' k) (fun k => h_adapt i k)
  · intro h; exact absurd (Finset.mem_univ i) h

/-- **Reference-intensity of a time-mark box factorises.** For `0 ≤ a`,
`ν̂((a,b]×A) = ofReal(b−a)·ν(A)` (`referenceIntensity = (volume.restrict (Ici 0)).prod ν`
and `(a,b] ⊆ [0,∞)`). -/
lemma referenceIntensity_Ioc_prod_eq
    {ν : Measure E} [SigmaFinite ν] {a b : ℝ} (ha : 0 ≤ a) {A : Set E} :
    LevyStochCalc.Poisson.referenceIntensity ν (Set.Ioc a b ×ˢ A)
      = ENNReal.ofReal (b - a) * ν A := by
  unfold LevyStochCalc.Poisson.referenceIntensity
  rw [MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.restrict_apply measurableSet_Ioc,
    Set.inter_eq_self_of_subset_left
      (show Set.Ioc a b ⊆ Set.Ici 0 from fun x hx => ha.trans hx.1.le), Real.volume_Ioc]

/-- **Mark-space `L²` of a finite mark-simple function.** For arbitrary marks `B k`
(finite `ν`) and reals `c k`,
`∫_E (∑ₖ cₖ·𝟙_{Bₖ}(e))² dν = ∑ₖ ∑ₖ' cₖ·cₖ'·ν(Bₖ∩Bₖ')`. The mark-direction analogue of
`markSum_sq_sametime`; underlies the Tonelli bridge from the isometry sum-form to the
integrand `L²` norm. -/
lemma mark_sq_integral
    {ν : Measure E} {K : ℕ}
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤) (c : Fin K → ℝ) :
    ∫ e, (∑ k : Fin K, c k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2 ∂ν
      = ∑ k : Fin K, ∑ k' : Fin K, c k * c k' * (ν (B k ∩ B k')).toReal := by
  have hinterm : ∀ k k', MeasurableSet (B k ∩ B k') := fun k k' => (hBm k).inter (hBm k')
  have hinterf : ∀ k k', ν (B k ∩ B k') ≠ ⊤ :=
    fun k k' => ne_top_of_le_ne_top (hBf k) (measure_mono Set.inter_subset_left)
  have hexp : (fun e => (∑ k : Fin K, c k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2)
      = fun e => ∑ k : Fin K, ∑ k' : Fin K,
          (c k * c k') * (B k ∩ B k').indicator (fun _ => (1 : ℝ)) e := by
    funext e
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
    by_cases h1 : e ∈ B k <;> by_cases h2 : e ∈ B k' <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, h1, h2]
  have hintg : ∀ k k', MeasureTheory.Integrable
      (fun e => (c k * c k') * (B k ∩ B k').indicator (fun _ => (1 : ℝ)) e) ν :=
    fun k k' => (((MeasureTheory.integrable_indicator_iff (hinterm k k')).mpr
      (MeasureTheory.integrableOn_const (hinterf k k')))).const_mul _
  rw [hexp, MeasureTheory.integral_finsetSum _ (fun k _ =>
      MeasureTheory.integrable_finsetSum _ (fun k' _ => hintg k k'))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => hintg k k')]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_indicator_const (1 : ℝ) (hinterm k k'),
    smul_eq_mul, mul_one, MeasureTheory.measureReal_def]

/-- **Time-direction `L²` of a partition-indicator sum (disjoint intervals).** For a
strictly-increasing partition `p` in `[0,T]` and reals `f i`,
`∫_{[0,T]} (∑ᵢ 𝟙_{(pᵢ,pᵢ₊₁]}(s)·fᵢ)² ds = ∑ᵢ (pᵢ₊₁−pᵢ)·fᵢ²`. The square collapses to the
diagonal (intervals disjoint) and each indicator integrates to the interval length. -/
lemma timeIndicator_sq_integral
    {N₀ : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T) (f : Fin N₀ → ℝ) :
    ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * f i) ^ 2 ∂volume
      = ∑ i : Fin N₀, (p i.succ - p i.castSucc) * (f i) ^ 2 := by
  have hpnn : ∀ j : Fin (N₀ + 1), 0 ≤ p j := fun j => by
    have := hpmono.monotone (Fin.zero_le j); rwa [hp0] at this
  have hle : ∀ i : Fin N₀, p i.castSucc ≤ p i.succ := fun i => (hpmono Fin.castSucc_lt_succ).le
  have hsubT : ∀ i : Fin N₀, Set.Ioc (p i.castSucc) (p i.succ) ⊆ Set.Icc (0 : ℝ) T := by
    intro i x hx
    exact ⟨(hpnn _).trans hx.1.le, hx.2.trans ((hpmono.monotone (Fin.le_last _)).trans hpleT)⟩
  -- pointwise: the square collapses to the diagonal.
  have hpt : ∀ s, (∑ i : Fin N₀,
        (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * f i) ^ 2
      = ∑ i : Fin N₀,
        (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * (f i) ^ 2 := by
    intro s
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_eq_single i]
    · by_cases hs : s ∈ Set.Ioc (p i.castSucc) (p i.succ) <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs]; ring
    · intro i' _ hi'
      have hdisj : Disjoint (Set.Ioc (p i.castSucc) (p i.succ))
          (Set.Ioc (p i'.castSucc) (p i'.succ)) := by
        rw [Set.Ioc_disjoint_Ioc]
        rcases lt_or_gt_of_ne hi' with h | h
        · exact le_trans (min_le_right _ _)
            (le_trans (hpmono.monotone (Fin.succ_le_castSucc_iff.mpr h)) (le_max_left _ _))
        · exact le_trans (min_le_left _ _)
            (le_trans (hpmono.monotone (Fin.succ_le_castSucc_iff.mpr h)) (le_max_right _ _))
      by_cases hs : s ∈ Set.Ioc (p i.castSucc) (p i.succ)
      · have hns : s ∉ Set.Ioc (p i'.castSucc) (p i'.succ) := fun hs' => hdisj.le_bot ⟨hs, hs'⟩
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, hs, hns]
      · simp [Set.indicator_of_notMem hs]
    · intro h; exact absurd (Finset.mem_univ i) h
  have hfin : MeasureTheory.IsFiniteMeasure (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ, Real.volume_Icc]
        exact ENNReal.ofReal_lt_top⟩
  have hintg : ∀ i : Fin N₀, MeasureTheory.Integrable
      (fun s => (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s * (f i) ^ 2)
      (volume.restrict (Set.Icc (0 : ℝ) T)) :=
    fun i => ((MeasureTheory.integrable_const (1 : ℝ)).indicator measurableSet_Ioc).mul_const _
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun s _ => hpt s),
    MeasureTheory.integral_finsetSum _ (fun i _ => hintg i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_mul_const, MeasureTheory.setIntegral_indicator measurableSet_Ioc,
    MeasureTheory.setIntegral_const, Set.inter_eq_self_of_subset_right (hsubT i),
    Real.volume_real_Ioc_of_le (hle i), smul_eq_mul, mul_one]

/-- **`(s,e)` double integral of `eval²`** (`e`-outer, `s`-inner). For a partition `p`
in `[0,T]`, arbitrary marks `B`, and real coeffs `c`,
`∫_E ∫_{[0,T]} (∑ᵢ 𝟙_{(pᵢ,pᵢ₊₁]}(s)·(∑ₖ cᵢₖ·𝟙_{Bₖ}(e)))² ds dν
  = ∑ᵢ (pᵢ₊₁−pᵢ)·∑ₖ∑ₖ' cᵢₖ·cᵢₖ'·ν(Bₖ∩Bₖ')`. The `s`-integral collapses by
`timeIndicator_sq_integral`, the `e`-integral by `mark_sq_integral`. -/
lemma eval_sq_integral
    {ν : Measure E} {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0)
    (hpmono : StrictMono p) {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (c : Fin N₀ → Fin K → ℝ) :
    ∫ e, (∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2 ∂volume) ∂ν
      = ∑ i : Fin N₀, (p i.succ - p i.castSucc)
        * ∑ k : Fin K, ∑ k' : Fin K, c i k * c i k' * (ν (B k ∩ B k')).toReal := by
  have hinterm : ∀ k k', MeasurableSet (B k ∩ B k') := fun k k' => (hBm k).inter (hBm k')
  have hinterf : ∀ k k', ν (B k ∩ B k') ≠ ⊤ :=
    fun k k' => ne_top_of_le_ne_top (hBf k) (measure_mono Set.inter_subset_left)
  -- `s`-integral collapses (per `e`) via `timeIndicator_sq_integral`.
  rw [show (fun e => ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2 ∂volume)
      = fun e => ∑ i : Fin N₀, (p i.succ - p i.castSucc)
          * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2 from
    funext (fun e => timeIndicator_sq_integral p hp0 hpmono hpleT
      (fun i => ∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e))]
  -- `e`-integral term-by-term, each via `mark_sq_integral`.
  have hint_e : ∀ i : Fin N₀, MeasureTheory.Integrable
      (fun e => (p i.succ - p i.castSucc)
        * (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2) ν := by
    intro i
    refine MeasureTheory.Integrable.const_mul ?_ _
    have hpt : (fun e => (∑ k : Fin K, c i k * (B k).indicator (fun _ => (1 : ℝ)) e) ^ 2)
        = fun e => ∑ k : Fin K, ∑ k' : Fin K,
            (c i k * c i k') * (B k ∩ B k').indicator (fun _ => (1 : ℝ)) e := by
      funext e
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun k' _ => ?_))
      by_cases h1 : e ∈ B k <;> by_cases h2 : e ∈ B k' <;>
        simp [Set.indicator_of_mem, Set.indicator_of_notMem, Set.mem_inter_iff, h1, h2]
    rw [hpt]
    refine MeasureTheory.integrable_finsetSum _ (fun k _ =>
      MeasureTheory.integrable_finsetSum _ (fun k' _ => ?_))
    exact ((MeasureTheory.integrable_indicator_iff (hinterm k k')).mpr
      (MeasureTheory.integrableOn_const (hinterf k k'))).const_mul _
  rw [MeasureTheory.integral_finsetSum _ (fun i _ => hint_e i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul, mark_sq_integral B hBm hBf (fun k => c i k)]

/-- **Tonelli bridge: integrand `L²` norm = isometry sum-form.** For a partition `p`
in `[0,T]`, arbitrary marks `B`, adapted bounded coeffs `ξ`,
`E[∫_E ∫_{[0,T]} (∑ᵢ 𝟙_{(pᵢ,pᵢ₊₁]}(s)·(∑ₖ ξᵢₖ·𝟙_{Bₖ}(e)))² ds dν]
  = ∑ᵢ∑ₖ∑ₖ' ν̂((pᵢ,pᵢ₊₁]×(Bₖ∩Bₖ'))·E[ξᵢₖ·ξᵢₖ']`, matching `markSumProcess_isometry`. -/
lemma markSumProcess_L2_eq
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k)) :
    ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, ξ i k ω * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2
        ∂volume ∂ν) ∂P
      = ∑ i : Fin N₀, ∑ k : Fin K, ∑ k' : Fin K,
        (LevyStochCalc.Poisson.referenceIntensity ν
          (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ (B k ∩ B k'))).toReal
        * ∫ ω, ξ i k ω * ξ i k' ω ∂P := by
  have hpnn : ∀ j : Fin (N₀ + 1), 0 ≤ p j := fun j => by
    have := hpmono.monotone (Fin.zero_le j); rwa [hp0] at this
  have hle : ∀ i : Fin N₀, p i.castSucc ≤ p i.succ := fun i => (hpmono Fin.castSucc_lt_succ).le
  have hinterf : ∀ k k', ν (B k ∩ B k') ≠ ⊤ :=
    fun k k' => ne_top_of_le_ne_top (hBf k) (measure_mono Set.inter_subset_left)
  have hξint : ∀ i k, MeasureTheory.Integrable (ξ i k) P := by
    intro i k; obtain ⟨M, hM⟩ := hξb i k
    exact (MeasureTheory.integrable_const M).mono' (hξm i k).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hM ω))
  have hξξint : ∀ i k k', MeasureTheory.Integrable (fun ω => ξ i k ω * ξ i k' ω) P := by
    intro i k k'; obtain ⟨M, hM⟩ := hξb i k
    exact (hξint i k').bdd_mul (hξm i k).aestronglyMeasurable
      (c := M) (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hM ω))
  -- factorisation `ν̂((pᵢ,pᵢ₊₁]×(Bₖ∩Bₖ')) = (pᵢ₊₁−pᵢ)·ν(Bₖ∩Bₖ')` in `toReal`.
  have hfact : ∀ (i : Fin N₀) (k k' : Fin K), (LevyStochCalc.Poisson.referenceIntensity ν
        (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ (B k ∩ B k'))).toReal
      = (p i.succ - p i.castSucc) * (ν (B k ∩ B k')).toReal := by
    intro i k k'
    rw [referenceIntensity_Ioc_prod_eq (hpnn _), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by linarith [hle i])]
  -- replace the `ω`-integrand by its `(s,e)` value.
  rw [show (fun ω => ∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, ξ i k ω * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2 ∂volume ∂ν)
      = fun ω => ∑ i : Fin N₀, (p i.succ - p i.castSucc)
          * ∑ k : Fin K, ∑ k' : Fin K,
            ξ i k ω * ξ i k' ω * (ν (B k ∩ B k')).toReal from
    funext (fun ω => eval_sq_integral p hp0 hpmono hpleT B hBm hBf (fun i k => ξ i k ω))]
  -- pull the finite sums and constants through `E[·]`, then refold via `hfact`.
  rw [MeasureTheory.integral_finsetSum _ (fun i _ =>
    (MeasureTheory.integrable_finsetSum _ (fun k _ =>
      MeasureTheory.integrable_finsetSum _ (fun k' _ =>
        (hξξint i k k').mul_const _))).const_mul _)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_finsetSum _ (fun k _ =>
    MeasureTheory.integrable_finsetSum _ (fun k' _ => (hξξint i k k').mul_const _)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [MeasureTheory.integral_finsetSum _ (fun k' _ => (hξξint i k k').mul_const _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k' _ => ?_)
  rw [MeasureTheory.integral_mul_const, hfact i k k']
  ring

/-- **Itô–Lévy `L²` isometry (multi-mark, integrand form).** For a shared partition `p`
in `[0,T]`, arbitrary marks `B`, adapted bounded coeffs `ξ`,
`E[(∑ᵢ∑ₖ ξᵢₖ Ñ((pᵢ,pᵢ₊₁]×Bₖ))²] = E[∫_E ∫_{[0,T]} eval² ds dν]` where
`eval(ω,s,e) = ∑ᵢ 𝟙_{(pᵢ,pᵢ₊₁]}(s)·∑ₖ ξᵢₖ(ω)·𝟙_{Bₖ}(e)`. Both sides equal the
isometry sum-form (`markSumProcess_isometry`, `markSumProcess_L2_eq`). This is the
isometry in the textbook `E[(∫dÑ)²] = E[∫∫|φ|²]` form the `Lp`-limit consumes. -/
lemma markSumProcess_isometry_L2
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξm : ∀ i k, Measurable (ξ i k))
    (h_adapt : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ i k)) :
    ∫ ω, (∑ i : Fin N₀, ∑ k : Fin K,
        ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, ξ i k ω * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2
        ∂volume ∂ν) ∂P :=
  (markSumProcess_isometry N ℱ hℱ p hp0 hpmono B hBm hBf ξ hξb hξm h_adapt).trans
    (markSumProcess_L2_eq p hp0 hpmono hpleT B hBm hBf ξ hξb hξm).symm

/-- **Difference isometry (Cauchy engine).** For two adapted bounded coefficient families
`ξ, ξ'` on the same partition/marks,
`E[(I(ξ) − I(ξ'))²] = E[∫∫ (eval(ξ) − eval(ξ'))²]`, i.e. the `L²(P)` distance of the
two simple ("Euler") integrals equals the `L²(P⊗vol⊗ν)` distance of their integrands.
Immediate from `markSumProcess_isometry_L2` on the coefficient difference `ξ − ξ'`,
using `ℝ`-linearity of both the integral and the eval in the coefficients. -/
lemma markSumProcess_diff_isometry_L2
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    {N₀ K : ℕ} (p : Fin (N₀ + 1) → ℝ) (hp0 : p 0 = 0) (hpmono : StrictMono p)
    {T : ℝ} (hpleT : p (Fin.last N₀) ≤ T)
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure P ν)
    (ℱ : Filtration ℝ ‹MeasurableSpace Ω›) (hℱ : IsPoissonFiltration N ℱ)
    (B : Fin K → Set E) (hBm : ∀ k, MeasurableSet (B k)) (hBf : ∀ k, ν (B k) ≠ ⊤)
    (ξ ξ' : Fin N₀ → Fin K → Ω → ℝ)
    (hξb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω| ≤ M) (hξ'b : ∀ i k, ∃ M, ∀ ω, |ξ' i k ω| ≤ M)
    (hξm : ∀ i k, Measurable (ξ i k)) (hξ'm : ∀ i k, Measurable (ξ' i k))
    (h_adapt : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ i k))
    (h_adapt' : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc)) (ξ' i k)) :
    ∫ ω, ((∑ i : Fin N₀, ∑ k : Fin K,
          ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
        - (∑ i : Fin N₀, ∑ k : Fin K,
          ξ' i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)) ^ 2 ∂P
      = ∫ ω, (∫ e, ∫ s in Set.Icc (0 : ℝ) T,
        (∑ i : Fin N₀, (Set.Ioc (p i.castSucc) (p i.succ)).indicator (fun _ => (1 : ℝ)) s
          * (∑ k : Fin K, (ξ i k ω - ξ' i k ω) * (B k).indicator (fun _ => (1 : ℝ)) e)) ^ 2
        ∂volume ∂ν) ∂P := by
  -- bounds/measurability/adaptedness of the difference coefficients.
  have hηb : ∀ i k, ∃ M, ∀ ω, |ξ i k ω - ξ' i k ω| ≤ M := by
    intro i k; obtain ⟨M, hM⟩ := hξb i k; obtain ⟨M', hM'⟩ := hξ'b i k
    exact ⟨M + M', fun ω => (abs_sub _ _).trans (add_le_add (hM ω) (hM' ω))⟩
  have hηm : ∀ i k, Measurable (fun ω => ξ i k ω - ξ' i k ω) :=
    fun i k => (hξm i k).sub (hξ'm i k)
  have hηa : ∀ i k, @MeasureTheory.StronglyMeasurable Ω ℝ _
      (ℱ (p i.castSucc))
      (fun ω => ξ i k ω - ξ' i k ω) := fun i k => (h_adapt i k).sub (h_adapt' i k)
  have key := markSumProcess_isometry_L2 p hp0 hpmono hpleT N ℱ hℱ B hBm hBf
    (fun i k ω => ξ i k ω - ξ' i k ω) hηb hηm hηa
  rw [show (fun ω => ((∑ i : Fin N₀, ∑ k : Fin K,
            ξ i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)
          - (∑ i : Fin N₀, ∑ k : Fin K,
            ξ' i k ω * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω)) ^ 2)
        = fun ω => (∑ i : Fin N₀, ∑ k : Fin K,
            (ξ i k ω - ξ' i k ω)
              * N.compensated (Set.Ioc (p i.castSucc) (p i.succ) ×ˢ B k) ω) ^ 2 from by
      funext ω
      congr 1
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      ring]
  exact key

/-- **`L²`-limit of a Cauchy sequence of integrands/integrals.** If `Mₙ ∈ L²(P)` and the
`Lp` lifts form a Cauchy sequence, there is an `M ∈ L²(P)` with `eLpNorm(Mₙ − M) → 0`.
Lp completeness + `tendsto_Lp_iff_tendsto_eLpNorm''`. The "define the integral as the
`L²`-limit" half of the masterApprox construction (→ dissertation #2(B)). -/
lemma exists_L2_limit_of_memLp_cauchySeq
    {P : Measure Ω}
    {Mₙ : ℕ → Ω → ℝ} (hmem : ∀ n, MeasureTheory.MemLp (Mₙ n) 2 P)
    (hcs : CauchySeq (fun n => (hmem n).toLp (Mₙ n))) :
    ∃ M : Ω → ℝ, MeasureTheory.MemLp M 2 P ∧
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (Mₙ n - M) 2 P) Filter.atTop (nhds 0) := by
  have : Fact ((1 : ℝ≥0∞) ≤ 2) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨g, MeasureTheory.Lp.memLp g, ?_⟩
  rw [← MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' Mₙ hmem (↑↑g)
    (MeasureTheory.Lp.memLp g)]
  rwa [MeasureTheory.Lp.toLp_coeFn g (MeasureTheory.Lp.memLp g)]

end LevyStochCalc.Poisson.Compensated
