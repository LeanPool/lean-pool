/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Statements.Main
public import LeanPool.RareSubtreePatterns.Bridge.CriterionM
public import LeanPool.RareSubtreePatterns.Cyclic.UniformVertex
public import LeanPool.RareSubtreePatterns.Lukasiewicz.Coding
public import LeanPool.RareSubtreePatterns.Stable.ToolkitProof
public import Mathlib.Data.Finsupp.Multiset

/-!
# Fringe subtree counts: Corollary `cor:Poisson_fringe` and Remark `rem:implication_fringe`

Source lines 924–969 (Corollary 3.1 and its proof, inventory C3.1, U05) and 971–1006
(Remark 3.2, inventory R3.2).

Theorem 1.1 (`thm:PoissonApproximation`) is taken as the explicit hypothesis
`h1 : PoissonApproximationStatement` (the paper's own theorem, proved elsewhere).
`PoissonApproximationConclusion μ G k` is the conclusion of Theorem 1.1 (both regimes), and
`poissonApproximationStatement_iff` records (by `Iff.rfl`) that Theorem 1.1 is exactly
"`(M)` and `(C)` for some cutoff imply `PoissonApproximationConclusion`".

## Main statements

* `uniformFringeLaw_real_eq_of_forces_size`: the identity of the proof of Corollary 3.1,
  `P(G(𝒯^n_{U_n}) = 1) = π Ψ_{n-s}(0) / Ψ_n(-1)` for a mark forcing the size `s`
  (from Corollary `cor:cyclicshift`).
* `microscopic_of_forces_size`, `nonClustering_of_forces_size`: Assumptions (M) and (C) for
  marks forcing a size `s_n → ∞`, `s_n = o(n)`, with the cutoff `M_n = max 1 s_n`.
* `poisson_fringe_of_forces_size`: Theorem 1.1's conclusion for marks `G_{k_n}` forcing a size
  `s_n` with `s_n → ∞`, `s_n = o(n)` (eventually in `n`).
* `poisson_fringe_of` (**Corollary `cor:Poisson_fringe`**, exactly as stated: `G_k(τ) = 1 ⇒
  |τ| = k` for every `k ≥ 1`, `k_n → ∞`, `k_n = o(n)`).
* Remark `rem:implication_fringe`: `poisson_fringe_prescribed_tree` (`G_{k_n}(T) = 1{T = T_n}`
  with `|T_n| = k_n`), `poisson_fringe_size` (`G_k(T) = 1{|T| = k}`) and
  `poisson_fringe_degreeStatistic` (`G_{k_n}(T) = 1{T ∈ 𝕋_{𝐧_{k_n}}}` for degree statistics
  `𝐧_{k_n}` of size `k_n`), together with the identity `∑_i n(i) = 1 + ∑_i i n(i) = |T|` for the
  degree statistic of every tree (`isDegreeStatistic_degreeStatistic`) and the fact that the
  degree-statistic marks force the size (`vertexCount_eq_of_hasDegreeStatistic`).

## Departures

* The paper takes the cutoff `M_n = k_n`; `IsCutoff` requires `M_n ≥ 1` for every `n ≥ 1`, so we
  use `M_n = max 1 k_n`, which equals `k_n` for all large `n` (both (M) and (C) only concern
  large `n`).
* In Remark 3.2 the marks `G_{k_n}` are indexed by `n` (the trees `T_n` and the statistics
  `𝐧_{k_n}` are arbitrary sequences in `n`); they are therefore encoded with the index sequence
  `id` and the size sequence `k`, through the slight generalization
  `poisson_fringe_of_forces_size` of Corollary 3.1 (the proof is unchanged).
* The historical comparisons with [CD17, Theorems 1.3, 1.4] and [BHJ26, Theorem 4.2] are
  bibliographic and are not formalized.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.DirectApplications

open PlaneTree

/-! ### The conclusion of Theorem 1.1 -/

/-- The conclusion of Theorem 1.1 for the marks `(G_k)` along `(k_n)`: (i) bounded mean
`n π_n` gives `d_TV(N_n, Po(n π_n)) → 0`; (ii) `n π_n → ∞` gives `N_n / (n π_n) → 1` in
probability and `N_n → ∞` in probability, where `N_n = #{u ∈ 𝒯^n : G_{k_n}(𝒯^n_u) = 1}`. -/
def PoissonApproximationConclusion (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ) : Prop :=
  ((∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * markProb μ G k n ≤ C) →
      Tendsto (fun n : ℕ => paperTVDist (markedCountLaw μ G k n)
        (poissonMeasure (Real.toNNReal ((n : ℝ) * markProb μ G k n))))
        (admissibleSizes μ) (𝓝 0)) ∧
    (Tendsto (fun n : ℕ => (n : ℝ) * markProb μ G k n) (admissibleSizes μ) atTop →
      (∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
        {T | ε < |(PlaneTree.markCount (G (k n)) T : ℝ) / ((n : ℝ) * markProb μ G k n) - 1|})
        (admissibleSizes μ) (𝓝 0)) ∧
      (∀ K : ℕ, Tendsto (fun n : ℕ => (PlaneTree.conditioned μ n).real
        {T | PlaneTree.markCount (G (k n)) T ≤ K}) (admissibleSizes μ) (𝓝 0)))

/-- Theorem 1.1 says exactly: (M) and (C) for some cutoff give `PoissonApproximationConclusion`. -/
theorem poissonApproximationStatement_iff :
    PoissonApproximationStatement ↔ ∀ (μ : PMF ℕ), InStableDomain μ →
      ∀ (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ),
        (∃ M : ℕ → ℕ, IsCutoff M ∧ Microscopic μ G k M ∧ NonClustering μ G k M) →
        PoissonApproximationConclusion μ G k :=
  Iff.rfl

/-! ### Marks forcing the size -/

/-- `M_n = max 1 s_n` is a cutoff sequence when `s_n → ∞` and `s_n = o(n)`. -/
theorem isCutoff_max_one {s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    (hso : (fun n => (s n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    IsCutoff (fun n => max 1 (s n)) where
  pos _ _ := lt_of_lt_of_le one_pos (le_max_left _ _)
  tendsto_atTop := tendsto_atTop_mono (fun n => le_max_right _ _) hs
  isLittleO := by
    refine hso.congr' ?_ EventuallyEq.rfl
    filter_upwards [hs.eventually_ge_atTop 1] with n hn
    rw [max_eq_right hn]

/-- The identity of the proof of Corollary 3.1 (source lines 963–965), from Corollary
`cor:cyclicshift`: if `G` forces the size `s`, then
`P(G(𝒯^n_{U_n}) = 1) = P(G(𝒯) = 1) Ψ_{n-s}(0) / Ψ_n(-1)`. -/
theorem uniformFringeLaw_real_eq_of_forces_size (μ : PMF ℕ) (n : ℕ) {G : PlaneTree → Prop}
    {s : ℕ} (hG : ∀ τ, G τ → τ.vertexCount = s) :
    (uniformFringeLaw μ n).real {T | G T} =
      (bienayme μ).real {T | G T} * (walkProb μ ((n : ℤ) - s) 0 / walkProb μ n (-1)) := by
  rw [Cyclic.uniformFringeLaw_real_eq]
  have h : {T | G T}.indicator (fun T => walkProb μ ((n : ℤ) - T.vertexCount) 0) =
      {T | G T}.indicator (fun _ => walkProb μ ((n : ℤ) - s) 0) :=
    Set.indicator_congr fun T hT => by rw [hG T hT]
  rw [h, integral_indicator_const _ MeasurableSet.of_discrete, smul_eq_mul]
  ring

/-- Assumption (M) for marks forcing a size `s_n → ∞` with `s_n = o(n)`, with respect to the
cutoff `M_n = max 1 s_n` (proof of Corollary 3.1, source lines 962–966): the marked fringe
subtree has size exactly `s_n ≤ M_n`, so the tail condition of Lemma `lem:M` is trivial. -/
theorem microscopic_of_forces_size {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (hT : StableToolkit μ α a)
    {G : ℕ → PlaneTree → Prop} {k s : ℕ → ℕ} (hs : Tendsto s atTop atTop)
    (hso : (fun n => (s n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hG : ∀ᶠ n in atTop, ∀ τ, G (k n) τ → τ.vertexCount = s n) :
    Microscopic μ G k (fun n => max 1 (s n)) := by
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  refine Bridge.microscopic_of_tail hT (isCutoff_max_one hs hso) ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hl hG] with n hn
  have hempty : {T : PlaneTree | G (k n) T} ∩ {T | max 1 (s n) < T.vertexCount} = ∅ := by
    ext T
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false,
      not_and, not_lt]
    intro hGT
    rw [hn T hGT]
    exact le_max_right _ _
  rw [measureReal_def, cond_apply MeasurableSet.of_discrete, hempty, measure_empty, mul_zero,
    ENNReal.toReal_zero, mul_zero]

/-- **`U05`** for a mark forcing a size `s` (source lines 914–920, 966–967): a fringe subtree of
size `s` contains no proper fringe subtree of size `s`, so `A_n(ℓ) = 0` for all `ℓ ≥ 1`. -/
theorem pairProb_eq_zero_of_forces_size' (μ : PMF ℕ) (G : ℕ → PlaneTree → Prop) (k : ℕ → ℕ)
    (n : ℕ) {s : ℕ} (hG : ∀ τ, G (k n) τ → τ.vertexCount = s) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    pairProb μ G k n ℓ = 0 := by
  have h : {T : PlaneTree | ℓ + 1 ≤ T.vertexCount ∧ G (k n) T ∧
      ∃ U ∈ T.fringeTrees[ℓ]?, G (k n) U} = ∅ := by
    ext T
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨-, hT, U, hU, hGU⟩
    obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hU
    exact not_forced_size_nested hG hG T hlt hℓ ⟨hT, hGU⟩
  rw [pairProb, h, measureReal_empty]

/-- Assumption (C) for marks forcing a size (eventually in `n`), with respect to any cutoff:
all `A_n(ℓ)`, `ℓ ≥ 1`, vanish (source lines 966–967). -/
theorem nonClustering_of_forces_size {μ : PMF ℕ} {G : ℕ → PlaneTree → Prop} {k s M : ℕ → ℕ}
    (hG : ∀ᶠ n in atTop, ∀ τ, G (k n) τ → τ.vertexCount = s n) :
    NonClustering μ G k M := by
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  refine (isLittleO_zero _ _).congr' ?_ EventuallyEq.rfl
  filter_upwards [hl hG] with n hn
  exact (Finset.sum_eq_zero fun ℓ hℓ =>
    pairProb_eq_zero_of_forces_size' μ G k n hn (Finset.mem_Icc.1 hℓ).1).symm

/-- Corollary 3.1 for marks `G_{k_n}` forcing a size `s_n` (eventually in `n`) with `s_n → ∞`
and `s_n = o(n)`: both conclusions of Theorem 1.1 hold. -/
theorem poisson_fringe_of_forces_size (h1 : PoissonApproximationStatement) {μ : PMF ℕ}
    (hμ : InStableDomain μ) {G : ℕ → PlaneTree → Prop} {k s : ℕ → ℕ}
    (hs : Tendsto s atTop atTop) (hso : (fun n => (s n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hG : ∀ᶠ n in atTop, ∀ τ, G (k n) τ → τ.vertexCount = s n) :
    PoissonApproximationConclusion μ G k := by
  obtain ⟨α, a, hstab⟩ := hμ
  exact h1 μ ⟨α, a, hstab⟩ G k ⟨_, isCutoff_max_one hs hso,
    microscopic_of_forces_size (Stable.stableToolkit hstab) hs hso hG,
    nonClustering_of_forces_size hG⟩

/-- **Corollary `cor:Poisson_fringe`** (source lines 924–958), from Theorem 1.1. Let `μ` be
critical in the domain of attraction of an `α`-stable law, `α ∈ (1,2]`, let `k_n → ∞` with
`k_n = o(n)`, and assume `G_k(τ) = 1 ⇒ |τ| = k` for every `k ≥ 1` and every plane tree `τ`.
Then (i) if `(n π_n)` is bounded, `d_TV(N_n, Po(n π_n)) → 0`; (ii) if `n π_n → ∞`,
`N_n / (n π_n) → 1` and `N_n → ∞` in probability. -/
theorem poisson_fringe_of (h1 : PoissonApproximationStatement) {μ : PMF ℕ}
    (hμ : InStableDomain μ) {G : ℕ → PlaneTree → Prop} {k : ℕ → ℕ}
    (hk : Tendsto k atTop atTop) (hko : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hG : ∀ j : ℕ, 1 ≤ j → ∀ τ : PlaneTree, G j τ → τ.vertexCount = j) :
    PoissonApproximationConclusion μ G k :=
  poisson_fringe_of_forces_size h1 hμ hk hko
    ((hk.eventually_ge_atTop 1).mono fun n hn => hG (k n) hn)

/-! ### Remark 3.2: three specializations -/

/-- Remark 3.2, first case (Cai–Devroye, Theorem 1.3): one prescribed tree `T_n` with
`|T_n| = k_n`, i.e. `G_{k_n}(T) = 1{T = T_n}`. -/
theorem poisson_fringe_prescribed_tree (h1 : PoissonApproximationStatement) {μ : PMF ℕ}
    (hμ : InStableDomain μ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hko : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ))) (Tn : ℕ → PlaneTree)
    (hTn : ∀ n, (Tn n).vertexCount = k n) :
    PoissonApproximationConclusion μ (fun n T => T = Tn n) id :=
  poisson_fringe_of_forces_size h1 hμ hk hko
    (Eventually.of_forall fun n τ hτ => by rw [show τ = Tn n from hτ, hTn n])

/-- Remark 3.2, second case (Cai–Devroye, Theorem 1.4): all trees of size `k_n`,
`G_k(T) = 1{|T| = k}`. -/
theorem poisson_fringe_size (h1 : PoissonApproximationStatement) {μ : PMF ℕ}
    (hμ : InStableDomain μ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hko : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    PoissonApproximationConclusion μ (fun j T => T.vertexCount = j) k :=
  poisson_fringe_of h1 hμ hk hko fun _ _ _ h => h

/-- A degree statistic of size `k` (source lines 981–987): a finitely supported sequence
`𝐧 = (n(i))_{i ≥ 0}` of nonnegative integers with `∑_i n(i) = 1 + ∑_i i n(i) = k`. -/
def IsDegreeStatistic (N : ℕ →₀ ℕ) (k : ℕ) : Prop :=
  (N.sum fun _ c => c) = k ∧ 1 + (N.sum fun i c => i * c) = k

/-- The degree statistic of a tree, `n(i) = #{v ∈ T : k_v(T) = i}` (source lines 988–993). -/
def degreeStatistic (T : PlaneTree) : ℕ →₀ ℕ := Multiset.toFinsupp (T.degSeq : Multiset ℕ)

theorem degreeStatistic_apply (T : PlaneTree) (i : ℕ) :
    degreeStatistic T i = T.degSeq.count i := by
  rw [degreeStatistic, Multiset.toFinsupp_apply, Multiset.coe_count]

/-- `T ∈ 𝕋_𝐧`: the tree `T` has degree statistic `𝐧`, i.e. `n(i) = #{v ∈ T : k_v(T) = i}` for
every `i ≥ 0`. -/
def HasDegreeStatistic (N : ℕ →₀ ℕ) (T : PlaneTree) : Prop :=
  ∀ i : ℕ, N i = T.degSeq.count i

theorem hasDegreeStatistic_iff (N : ℕ →₀ ℕ) (T : PlaneTree) :
    HasDegreeStatistic N T ↔ degreeStatistic T = N := by
  constructor
  · intro h
    ext i
    rw [degreeStatistic_apply, h i]
  · rintro rfl i
    rw [degreeStatistic_apply]

private theorem sum_map_sub_one (l : List ℕ) :
    (l.map fun d : ℕ => (d : ℤ) - 1).sum = (l.sum : ℤ) - l.length := by
  induction l with
  | nil => simp
  | cons d l ih =>
    rw [List.map_cons, List.sum_cons, ih, List.sum_cons, List.length_cons]
    push_cast
    ring

/-- The handshake identity: the outdegrees of a tree sum to `|T| - 1`. -/
theorem sum_degSeq_add_one (T : PlaneTree) : T.degSeq.sum + 1 = T.vertexCount := by
  have h := T.sum_dfsSeq
  rw [dfsSeq, sum_map_sub_one, length_degSeq] at h
  omega

/-- The degree statistic of every tree `T` is a degree statistic of size `|T|`:
`∑_i n(i) = 1 + ∑_i i n(i) = |T|` (the identity of source lines 981–987 for the family
`𝕋_𝐧`). -/
theorem isDegreeStatistic_degreeStatistic (T : PlaneTree) :
    IsDegreeStatistic (degreeStatistic T) T.vertexCount := by
  have hm : Finsupp.toMultiset (degreeStatistic T) = (T.degSeq : Multiset ℕ) :=
    Multiset.toFinsupp_toMultiset _
  constructor
  · have h := Finsupp.card_toMultiset (degreeStatistic T)
    rw [hm, Multiset.coe_card, length_degSeq] at h
    exact h.symm
  · have h := Finsupp.sum_toMultiset (degreeStatistic T)
    rw [hm, Multiset.sum_coe] at h
    have h' : ((degreeStatistic T).sum fun i c => i * c) =
        (degreeStatistic T).sum fun a n => n • a :=
      Finsupp.sum_congr fun i _ => by rw [smul_eq_mul, mul_comm]
    rw [h', ← h, add_comm]
    exact sum_degSeq_add_one T

/-- A tree with degree statistic `𝐧` has size `∑_i n(i)`; in particular, if `𝐧` is a degree
statistic of size `k`, the mark `1{T ∈ 𝕋_𝐧}` forces the size `k`. -/
theorem vertexCount_eq_of_hasDegreeStatistic {N : ℕ →₀ ℕ} {k : ℕ} (hN : IsDegreeStatistic N k)
    {T : PlaneTree} (hT : HasDegreeStatistic N T) : T.vertexCount = k := by
  rw [hasDegreeStatistic_iff] at hT
  rw [← hN.1, ← hT]
  exact (isDegreeStatistic_degreeStatistic T).1.symm

/-- Remark 3.2, third case (the Poisson part of Berzunza–Holmgren–Janson, Theorem 4.2, for
conditioned Bienaymé trees): `G_{k_n}(T) = 1{T ∈ 𝕋_{𝐧_{k_n}}}` for degree statistics
`𝐧_{k_n}` of size `k_n` (indexed by `n`). -/
theorem poisson_fringe_degreeStatistic (h1 : PoissonApproximationStatement) {μ : PMF ℕ}
    (hμ : InStableDomain μ) {k : ℕ → ℕ} (hk : Tendsto k atTop atTop)
    (hko : (fun n => (k n : ℝ)) =o[atTop] (fun n => (n : ℝ))) (N : ℕ → ℕ →₀ ℕ)
    (hN : ∀ n, IsDegreeStatistic (N n) (k n)) :
    PoissonApproximationConclusion μ (fun n T => HasDegreeStatistic (N n) T) id :=
  poisson_fringe_of_forces_size h1 hμ hk hko
    (Eventually.of_forall fun n _ hτ => vertexCount_eq_of_hasDegreeStatistic (hN n) hτ)

end PoissonDeclumping.DirectApplications
