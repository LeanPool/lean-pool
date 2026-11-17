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

public import LeanPool.KLS.LevyStochCalc.Basic
public import LeanPool.KLS.LevyStochCalc.Poisson.PoissonSuperposition
public import LeanPool.KLS.LevyStochCalc.Poisson.RegionIndependence
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Independence.Basic

/-!
# Poisson random measure on `[0, ∞) × E`

A *Poisson random measure* on the time-space `[0, ∞) × E` (where `E` is a
measurable mark space with σ-finite intensity `ν`), defined over a
probability space `(Ω, P)`, is a measurable family

  `N : Ω → Measure (ℝ × E)`

with the following properties:

* For each measurable `B ⊆ ℝ × E` with `(volume.restrict [0,∞) ⊗ ν)(B) < ∞`,
  `N(·, B) ~ Poisson` with mean equal to that intensity.
* For any pairwise-disjoint family of such sets, the random variables
  `(N(·, B_i))_i` are independent under `P`.

This is the time-aware structure required for the *compensated* integral
`∫_0^t ∫_E φ(s, e) Ñ(ds, de)` to be well-defined.

## References

* Applebaum, *Lévy Processes and Stochastic Calculus*, Cambridge 2009, §2.3, Thm 2.3.1.
* Ikeda–Watanabe, *Stochastic Differential Equations and Diffusion Processes*,
  North-Holland 1989, §I.8.
* Sato, *Lévy Processes and Infinitely Divisible Distributions*,
  Cambridge 1999, §19.

## Construction

The intensity is `volume.restrict (Set.Ici 0) ⊗ ν` (Lebesgue restricted to `[0, ∞)` tensor `ν`
on the mark space). `PoissonRandomMeasure.exists_of_sigmaFinite` builds a Poisson random
measure by the Poisson recipe: the time-space is cut into the cells `[n, n+1) × sₘ` of a
σ-finite decomposition, each cell of positive intensity carries a Poisson number of
independent marks distributed according to the normalised intensity, and the cells are
superposed (`LevyStochCalc.Poisson.superposition`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LevyStochCalc.Poisson

universe u v

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MeasurableSpace E]

/-- The Poisson distribution `Poisson(μ)` viewed as a measure on `ℝ≥0∞` (via
the natural inclusion `ℕ ↪ ℝ≥0∞`). Convenience for stating
`P.map (N · A) = …` since `N(·, A) : Ω → ℝ≥0∞` (an extended-real count). -/
noncomputable def poissonMeasureENN (μ : ℝ≥0) : Measure ℝ≥0∞ :=
  (ProbabilityTheory.poissonMeasure μ).map (fun n : ℕ => (n : ℝ≥0∞))

/-- The reference intensity on `ℝ × E`: Lebesgue on `[0, ∞)` tensor `ν` on
the mark space. -/
noncomputable def referenceIntensity {E : Type v} [MeasurableSpace E]
    (ν : Measure E) : Measure (ℝ × E) :=
  (volume.restrict (Set.Ici (0 : ℝ))).prod ν

/-- A *Poisson random measure on `[0, ∞) × E`* with intensity
`volume.restrict [0,∞) ⊗ ν`, defined over a probability space `(Ω, P)`.

The Applebaum (2009) Definition 2.3.1 properties are: (a) `N(·, A)` is
Poisson-distributed (captured by `poisson_law`); (b) disjoint-family values
are independent (captured by `independent_disjoint`); (c) `N(ω, ·)` is an
integer-valued atomic measure.

Of (c) the fields below record only the following. For each fixed region of
finite intensity, `integer_valued` gives an almost surely integer value, with an
exceptional null set that depends on that region; there is therefore no single
null set outside which `N ω` is integer-valued on every region at once.
Atomicity is not a field. The simultaneous integer-valued statement on a window
of finite intensity is `Poisson.ae_isIntegerValued_restrict`, and the matching
atomicity — a finite sum of Dirac masses — is `Poisson.ae_exists_eq_sum_dirac`,
both in `Poisson/Atomic.lean` and both under additional countable-generation
hypotheses on the mark space. -/
structure PoissonRandomMeasure
    (P : Measure Ω) [IsProbabilityMeasure P]
    (ν : Measure E) [SigmaFinite ν] where
  /-- The underlying ω-indexed family of measures on `ℝ × E`. -/
  N : Ω → Measure (ℝ × E)
  /-- For each measurable `B ⊆ ℝ × E`, the map `ω ↦ N(ω, B)` is measurable. -/
  measurable_eval : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    Measurable (fun ω => N ω B)
  /-- **Applebaum 2.3.1(c), finite-intensity case.** For measurable `B` with
  finite intensity, `N(·, B)` is a.s. `ℕ`-valued (in the natural embedding
  `ℕ ↪ ℝ≥0∞`). Follows from `poisson_law` since the Poisson distribution
  is supported on `ℕ`. Exposed as a structural field so downstream code
  can use it without re-deriving through the Poisson-law characterisation. -/
  integer_valued : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    referenceIntensity ν B ≠ ⊤ →
    ∀ᵐ ω ∂P, ∃ n : ℕ, N ω B = n
  /-- **Applebaum 2.3.1(c), infinite-intensity case.** For measurable `B` with
  INFINITE intensity, `N(·, B) = ∞` almost surely. This completes the Applebaum
  2.3.1(c) encoding — `integer_valued` covers only the finite-intensity branch.
  Under the literature Poisson recipe construction,
  this is automatic: an infinite-intensity set decomposes into countably
  many finite-intensity pieces, each contributing Poisson(λ_n) atoms, with
  total count = ∑_n Poisson(λ_n) which is a.s. infinite when ∑_n λ_n = ∞. -/
  infinite_at_infinite_intensity : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    referenceIntensity ν B = ⊤ → ∀ᵐ ω ∂P, N ω B = ⊤
  /-- `N(·, B)` has `Poisson` law with mean `(referenceIntensity ν)(B)` under
  `P`, for every measurable `B` with finite intensity. -/
  poisson_law : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
    referenceIntensity ν B ≠ ⊤ →
    P.map (fun ω => N ω B) = poissonMeasureENN (referenceIntensity ν B).toNNReal
  /-- For any pairwise-disjoint countable family of measurable subsets of
  `ℝ × E`, the family of evaluation random variables `(ω ↦ N(ω, B_i))_i` is
  independent under `P`.

  The `[Countable ι]` hypothesis matches the literature: standard PRM
  independence (Kallenberg 3.5.1 / Applebaum 2.3.1(b)) is for COUNTABLE
  pairwise-disjoint families. Allowing uncountable `ι` would invoke
  Mathlib's `iIndepFun` at uncountable index types, a more delicate notion
  that does not match Applebaum's formulation. -/
  independent_disjoint :
    ∀ {ι : Type*} [Countable ι] (B : ι → Set (ℝ × E)),
      (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) →
      ProbabilityTheory.iIndepFun (fun (i : ι) (ω : Ω) => N ω (B i)) P
  /-- **σ-algebra-level past/future independence.** The σ-algebra generated by
  `{N(·, B) : B ⊆ (−∞, s] × E, B measurable}` (the "past at time `s`") is
  independent of `σ(N(·, (s, t] × A))` (a future increment).

  This is strictly stronger than `independent_disjoint` (which is iIndepFun
  for finite/countable families) and is needed to apply
  `MeasureTheory.condExp_indep_eq` in the compensated stochastic-integral
  proofs. For PRMs it follows from joint independence on disjoint subsets;
  packaged as a structural hypothesis in the same spirit as
  `BrownianMotion.joint_increment_independent`. -/
  joint_past_future_independent :
    ∀ {s t : ℝ}, 0 ≤ s → s < t → ∀ {A : Set E}, MeasurableSet A → ν A ≠ ⊤ →
      ProbabilityTheory.Indep
        (⨆ B ∈ { C : Set (ℝ × E) | C ⊆ Set.Iic s ×ˢ Set.univ ∧ MeasurableSet C },
          MeasurableSpace.comap (fun ω => N ω B) inferInstance)
        (MeasurableSpace.comap
          (fun ω => N ω (Set.Ioc s t ×ˢ A)) inferInstance)
        P

/-- The compensated random measure: `Ñ(B) := N(B) − ν̂(B)` where
`ν̂ := referenceIntensity ν`. Returns a real number when `ν̂(B) < ∞`. -/
noncomputable def PoissonRandomMeasure.compensated
    {P : Measure Ω} [IsProbabilityMeasure P]
    {ν : Measure E} [SigmaFinite ν]
    (N : PoissonRandomMeasure P ν) (B : Set (ℝ × E)) (ω : Ω) : ℝ :=
  (N.N ω B).toReal - (referenceIntensity ν B).toReal

/-- **Step 1: σ-finite decomposition of the intensity.** A σ-finite measure `ν`
on `E` decomposes as a sequence of pairwise-disjoint measurable sets each of
finite mass covering all of `E`. Built from `MeasureTheory.spanningSets` +
`Set.disjointed`. -/
lemma sigmaFinite_decomposition
    (E : Type v) [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν] :
    ∃ s : ℕ → Set E,
      (∀ n, MeasurableSet (s n)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) ∧
      (∀ n, ν (s n) < ⊤) ∧
      (⋃ n, s n) = Set.univ := by
  refine ⟨disjointed (MeasureTheory.spanningSets ν), ?_, ?_, ?_, ?_⟩
  · intro n
    exact MeasurableSet.disjointed (MeasureTheory.measurableSet_spanningSets ν) n
  · exact disjoint_disjointed _
  · intro n
    refine lt_of_le_of_lt ?_ (MeasureTheory.measure_spanningSets_lt_top ν n)
    exact MeasureTheory.measure_mono (disjointed_subset _ _)
  · rw [iUnion_disjointed]
    exact MeasureTheory.iUnion_spanningSets ν

/-- For every σ-finite intensity `ν` on a measurable mark space `E`, some probability space
carries a Poisson random measure with intensity `volume.restrict [0,∞) ⊗ ν`
(Applebaum, *Lévy Processes and Stochastic Calculus*, Theorem 2.3.1; Kallenberg, *Random
Measures, Theory and Applications*, Proposition 3.6). -/
theorem PoissonRandomMeasure.exists_of_sigmaFinite
    (E : Type v) [MeasurableSpace E]
    (ν : Measure E) [SigmaFinite ν] :
    ∃ (Ω : Type v) (_ : MeasurableSpace Ω) (P : Measure Ω)
      (_ : IsProbabilityMeasure P), Nonempty (PoissonRandomMeasure P ν) := by
  classical
  obtain ⟨s, hs_meas, hs_disj, hs_fin, hs_univ⟩ := sigmaFinite_decomposition E ν
  set Λ := referenceIntensity ν with hΛ
  -- the time-space cells `[n, n+1) × sₘ`
  let A : ℕ × ℕ → Set (ℝ × E) := fun q => Set.Ico (q.1 : ℝ) (q.1 + 1) ×ˢ s q.2
  have hA_meas : ∀ q, MeasurableSet (A q) := fun q => measurableSet_Ico.prod (hs_meas q.2)
  have hA_disj : Pairwise fun q q' => Disjoint (A q) (A q') := by
    rintro ⟨n, m⟩ ⟨n', m'⟩ hne
    change Disjoint (Set.Ico (n : ℝ) (n + 1) ×ˢ s m) (Set.Ico (n' : ℝ) (n' + 1) ×ˢ s m')
    rw [Set.disjoint_prod]
    by_cases hn : n = n'
    · subst hn
      exact Or.inr (hs_disj fun h => hne (by rw [h]))
    · refine Or.inl (Set.Ico_disjoint_Ico.2 ?_)
      rcases lt_or_gt_of_ne hn with h | h
      · have : (n : ℝ) + 1 ≤ n' := by exact_mod_cast h
        exact (min_le_left _ _).trans (this.trans (le_max_right _ _))
      · have : (n' : ℝ) + 1 ≤ n := by exact_mod_cast h
        exact (min_le_right _ _).trans (this.trans (le_max_left _ _))
  have hA_fin : ∀ q, Λ (A q) ≠ ⊤ := by
    intro q
    rw [hΛ, referenceIntensity, Measure.prod_prod]
    refine ENNReal.mul_ne_top ?_ (hs_fin q.2).ne
    refine ne_top_of_le_ne_top (b := volume (Set.Ico (q.1 : ℝ) (q.1 + 1))) ?_
      (Measure.restrict_le_self _)
    rw [Real.volume_Ico]
    exact ENNReal.ofReal_ne_top
  -- the cells of positive intensity, with their normalised intensities
  let ι := {q : ℕ × ℕ // Λ (A q) ≠ 0}
  let r : ι → ℝ≥0 := fun p => (Λ (A p.1)).toNNReal
  let ρ : ι → Measure (ℝ × E) := fun p => (Λ (A p.1))⁻¹ • Λ.restrict (A p.1)
  have : ∀ p, IsProbabilityMeasure (ρ p) := fun p => ⟨by
    change ((Λ (A p.1))⁻¹ • Λ.restrict (A p.1)) Set.univ = 1
    rw [Measure.smul_apply, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
      smul_eq_mul, ENNReal.inv_mul_cancel p.2 (hA_fin p.1)]⟩
  -- the superposition has intensity `Λ`
  have hcell : ∀ p : ι, (r p : ℝ≥0∞) • ρ p = Λ.restrict (A p.1) := by
    intro p
    change ((Λ (A p.1)).toNNReal : ℝ≥0∞) • ((Λ (A p.1))⁻¹ • Λ.restrict (A p.1)) = _
    rw [ENNReal.coe_toNNReal (hA_fin p.1), smul_smul, ENNReal.mul_inv_cancel p.2 (hA_fin p.1),
      one_smul]
  have hnull : Λ (⋃ p : ι, A p.1)ᶜ = 0 := by
    have hsub : (⋃ p : ι, A p.1)ᶜ
        ⊆ (Set.Ici (0 : ℝ) ×ˢ Set.univ)ᶜ ∪ ⋃ q : {q : ℕ × ℕ // Λ (A q) = 0}, A q.1 := by
      intro x hx
      by_cases hx0 : x ∈ Set.Ici (0 : ℝ) ×ˢ Set.univ
      · right
        obtain ⟨m, hm⟩ : ∃ m, x.2 ∈ s m := by
          have := hs_univ ▸ Set.mem_univ x.2
          exact Set.mem_iUnion.1 this
        have hx1 : x.1 ∈ Set.Ici (0 : ℝ) := (Set.mem_prod.1 hx0).1
        have hxA : x ∈ A (⌊x.1⌋₊, m) :=
          Set.mem_prod.2 ⟨⟨Nat.floor_le hx1, Nat.lt_floor_add_one x.1⟩, hm⟩
        by_cases h0 : Λ (A (⌊x.1⌋₊, m)) = 0
        · exact Set.mem_iUnion.2 ⟨⟨_, h0⟩, hxA⟩
        · exact absurd (Set.mem_iUnion.2 ⟨⟨_, h0⟩, hxA⟩) hx
      · exact Or.inl hx0
    refine measure_mono_null hsub (measure_union_null ?_ (measure_iUnion_null fun q => q.2))
    rw [hΛ, referenceIntensity, Measure.restrict_prod_eq_prod_univ,
      Measure.restrict_apply (measurableSet_Ici.prod MeasurableSet.univ).compl,
      Set.compl_inter_self, measure_empty]
  have hint : superIntensity r ρ = Λ := by
    unfold superIntensity
    simp_rw [hcell]
    rw [← Measure.restrict_iUnion (fun p q hpq => hA_disj (Subtype.val_injective.ne hpq))
      fun p => hA_meas p.1]
    exact Measure.restrict_eq_self_of_ae_mem (ae_iff.2 hnull)
  -- assembly
  refine ⟨ι → PieceSpace (ℝ × E), inferInstance, superLaw r ρ, inferInstance, ⟨?_⟩⟩
  have hN_meas : ∀ {B : Set (ℝ × E)}, MeasurableSet B →
      Measurable fun ω : ι → PieceSpace (ℝ × E) => superposition ω B :=
    fun hB => measurable_superposition hB
  have hN_indep : ∀ {κ : Type} [Countable κ] (B : κ → Set (ℝ × E)), (∀ i, MeasurableSet (B i)) →
      Pairwise (fun i j => Disjoint (B i) (B j)) →
      iIndepFun (fun i ω => superposition ω (B i)) (superLaw r ρ) :=
    fun B hB hd => iIndepFun_superposition r ρ hB hd
  exact
    { N := superposition
      measurable_eval := hN_meas
      integer_valued := fun hB hfin => ae_exists_nat_superposition r ρ hB (by rwa [hint])
      infinite_at_infinite_intensity := fun hB hinf =>
        ae_eq_top_superposition r ρ hB (by rwa [hint])
      poisson_law := fun hB hfin => by
        rw [map_superposition r ρ hB (by rwa [hint]), hint]
        rfl
      independent_disjoint := fun B hB hd => iIndepFun_superposition r ρ hB hd
      joint_past_future_independent := fun {t₁ t₂} _ h12 {S} hS _ => by
        have h := indep_of_disjoint_region_of_indep hN_meas hN_indep
          (measurableSet_Ioc.prod hS : MeasurableSet (Set.Ioc t₁ t₂ ×ˢ S))
        refine indep_of_indep_of_le_left h (iSup₂_le fun C hC => le_iSup₂_of_le C ?_ le_rfl)
        exact ⟨(Set.disjoint_prod.2 (Or.inl (Set.Iic_disjoint_Ioc le_rfl))).mono_left hC.1,
          hC.2⟩ }

end LevyStochCalc.Poisson
