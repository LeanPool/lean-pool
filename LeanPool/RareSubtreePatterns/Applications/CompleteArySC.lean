/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Applications.TreeCompleteClass
public import LeanPool.RareSubtreePatterns.Applications.TreeCriteria
public import LeanPool.RareSubtreePatterns.Patterns.CutGraftBound
public import LeanPool.RareSubtreePatterns.Bridge.CriterionS

import LeanPool.RareSubtreePatterns.LeafHeight.Recursion
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Complete `r`-ary marks: Assumptions (S) and (C) (Lemmas `lem:S_rary` and `lem:C_rary`)

Section 6.2 of the paper, source lines 2623–2792 (inventory L6.2 (i),(ii), L6.3, P19, P21).
Marks: `G_k(T) = 1{H_{r,k} ≺ T}` (`Embeds (completeTree r k)`) and its declumping
`Ĝ_k(T) = 1{k_∅(T) ≠ r} 1{∃ u ∈ Γ_∅(T), G_k(T_u) = 1}`
(`declumpedMark {d | d ≠ r} (Embeds (completeTree r k))`). `π_k = P(H_{r,k} ≺ 𝒯)`.

## Main statements

* `structuralMicroscopic_embeds`: for any sequence of patterns `P_j` with
  `s(P_{k_n}) + ℓ(P_{k_n}) = n^{o(1)}` (internal vertices plus leaves), the marks `P_j ≺ ·` satisfy
  Assumption (S) with respect to `M_n = max 1 ⌊n^{1-η}⌋₊`, `η ∈ (0, 1 - 1/α)`. Its specialization
  `lem_S_rary_i` is **Lemma `lem:S_rary`(i)**; `lem_S_rary_i_one` (`r = 1`, `k_n = n^{o(1)}`) and
  `lem_S_rary_i_of_two_le` (`r ≥ 2`, `r^{k_n} = n^{o(1)}`) restate the hypothesis through U07.
* `pairSum_completeTree_le` (**P19**): one constant `K` such that for all `k`, `M`,
  `∑_{ℓ=1}^{M} P(|𝒯| ≥ ℓ+1, G_k(𝒯) = 1, G_k(𝒯_{u_{ℓ+1}}) = 1) ≤ K π_k + M π_k²`.
* `lem_S_rary_ii` (**Lemma `lem:S_rary`(ii)**): if `n π_{k_n} → ∞` and `M_n = o(n)`, then
  Assumption (C) holds; `lem_S_rary` packages (i) and (ii) with the paper's hypotheses.
* `pair_declumped_completeTree_le` (**P21**) and `lem_C_rary` (**Lemma `lem:C_rary`**): the
  declumped marks satisfy `A_n(ℓ) ≤ π̂_{k_n}²` for every `ℓ ≥ 1`, hence Assumption (C) for every
  level sequence and every cutoff with `M_n = o(n)`.

## Proof of P19 (departure from the paper's bookkeeping)

The paper splits the descendants `u_{ℓ+1}` of a root occurrence into the vertices of the displayed
skeleton and those of the grafted forest, and bounds the forest part by a union bound over DFS
positions of an infinite forest. Here both parts are handled by the cut-and-graft decomposition
`T = Cut_ℓ(T)[T_{u_{ℓ+1}}]` at each fixed position `ℓ`: every position has a class `j ≤ k`
(`exists_replaceClass`; `j = 0` for forest vertices and skeleton leaves, `j = k - a` for internal
skeleton vertices at depth `a`), and the cut-and-graft factorization gives exactly
`P(ℓ < |𝒯|, class j, G_k(𝒯_{u_{ℓ+1}})) = (π_k / π_j) P(ℓ < |𝒯|, G_k(𝒯), class j)`. The class `0`
terms give `M π_k²` (the paper's forest bound `M_n π_{k_n} · π_{k_n}`; the "fresh increment"
property at a fixed forest position is the factorization `𝐏(A[S]) = w(A) 𝐏(S)`), and the classes
`j ≥ 1` give at most `r^{k-j}` positions each (`classCount_le`). With `a = k - j` this is the
paper's skeleton sum `π_k ∑_{a} r^a π_k / π_{k-a}`; using `π_k / π_{k-a} ≤ μ_r^{s_{r,a}}`
(superadditivity of `s_{r,·}`) it is bounded by `K π_k` with the `k`-independent convergent series
`K = ∑_a r^a μ_r^{s_{r,a}}` (`μ_r < 1`). For `r = 1` this is the paper's geometric continuation
`∑_a μ_1^a`; for `r ≥ 2` the paper uses instead the bound `k r^k μ_r^{r^{k-1}} + r^k π_k` (its
leaf term `r^k π_k` is part of our class `0`). No forest DFS bookkeeping is needed.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal

namespace PoissonDeclumping

open PlaneTree

namespace Applications

/-! ### Assumption (S) -/

/-- Under the decomposition `embedsSkeletonLaw μ T'` (U06), `C = s(T')` and `L = ℓ(T')` are
deterministic, so `E[C + L] ≤ s(T') + ℓ(T')`. -/
theorem lintegral_embedsSkeletonLaw_le (μ : PMF ℕ) (T' : PlaneTree) :
    ∫⁻ ω, ((ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞)) ∂embedsSkeletonLaw μ T' ≤
      ((internalCount T' + leafCount T' : ℕ) : ℝ≥0∞) := by
  have hae : (fun ω : PlaneTree × ℕ × List PlaneTree => (ω.2.1 : ℝ≥0∞) + (ω.2.2.length : ℝ≥0∞))
      =ᵐ[embedsSkeletonLaw μ T'] fun _ => ((internalCount T' + leafCount T' : ℕ) : ℝ≥0∞) := by
    filter_upwards [embedsSkeletonLaw_ae μ T'] with ω hω
    rw [hω.1, hω.2.1]
    push_cast
    rfl
  rw [lintegral_congr_ae hae, lintegral_const]
  have hu : embedsSkeletonLaw μ T' Set.univ ≤ 1 := by
    rw [embedsSkeletonLaw_apply]
    exact cond_univ_le_one _ _
  calc ((internalCount T' + leafCount T' : ℕ) : ℝ≥0∞) * embedsSkeletonLaw μ T' Set.univ
      ≤ ((internalCount T' + leafCount T' : ℕ) : ℝ≥0∞) * 1 := mul_le_mul_right hu _
    _ = _ := mul_one _

/-- Assumption (S) for non-fringe pattern marks `G_j = 1{P_j ≺ ·}` whose skeleton size
`s(P_{k_n}) + ℓ(P_{k_n})` (internal vertices plus leaves) is `n^{o(1)}`, with respect to the
polynomial cutoff `M_n = max 1 ⌊n^{1-η}⌋₊` (`= ⌊n^{1-η}⌋` for `n ≥ 1`), `η ∈ (0, 1 - 1/α)`:
Lemma `lem:critM` applied to the decomposition of U06 (source lines 2655–2668). -/
theorem structuralMicroscopic_embeds {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}
    (hT : StableToolkit μ α a) {η : ℝ} (hη : 0 < η ∧ η < 1 - 1 / α) (P : ℕ → PlaneTree)
    {k : ℕ → ℕ}
    (hk : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      ((internalCount (P (k n)) + leafCount (P (k n)) : ℕ) : ℝ) ≤ (n : ℝ) ^ δ) :
    StructuralMicroscopic μ a (fun j => Embeds (P j)) k
      (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) :=
  Bridge.critM hT hη (fun j => embedsSkeletonLaw μ (P j))
    (fun _ hpos => skeleton_embeds hT.critical hT.nondegenerate hpos) fun δ hδ => by
      filter_upwards [hk δ hδ] with n hn
      refine (lintegral_embedsSkeletonLaw_le μ _).trans ?_
      rw [← ENNReal.ofReal_natCast]
      exact ENNReal.ofReal_le_ofReal hn

/-- **Lemma `lem:S_rary`(i)** (source lines 2644–2668): if
`s_{r,k_n} + ℓ_{r,k_n} = n^{o(1)}` (`s_{r,k}` = number of internal vertices and `ℓ_{r,k}` =
number of leaves of `H_{r,k}`, identified with `k, 1` resp. `(r^k - 1)/(r - 1), r^k` by U07),
then `G_k = 1{H_{r,k} ≺ ·}` satisfies Assumption (S) along `(k_n)` with respect to
`M_n = max 1 ⌊n^{1-η}⌋₊`, for every `η ∈ (0, 1 - 1/α)`. The `n^{o(1)}` hypothesis is used only
through its upper half `≤ n^δ` (for every `δ > 0`, eventually along admissible sizes). -/
theorem lem_S_rary_i {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (hT : StableToolkit μ α a) {r : ℕ}
    {η : ℝ} (hη : 0 < η ∧ η < 1 - 1 / α) {k : ℕ → ℕ}
    (hk : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      ((internalCount (completeTree r (k n)) + leafCount (completeTree r (k n)) : ℕ) : ℝ) ≤
        (n : ℝ) ^ δ) :
    StructuralMicroscopic μ a (fun j => Embeds (completeTree r j)) k
      (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) :=
  structuralMicroscopic_embeds hT hη (completeTree r) hk

/-- **Lemma `lem:S_rary`(i)**, `r = 1`: the hypothesis `s_{1,k_n} + ℓ_{1,k_n} = k_n + 1 = n^{o(1)}`
is `k_n = n^{o(1)}`. -/
theorem lem_S_rary_i_one {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (hT : StableToolkit μ α a) {η : ℝ}
    (hη : 0 < η ∧ η < 1 - 1 / α) {k : ℕ → ℕ}
    (hk : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, (k n : ℝ) ≤ (n : ℝ) ^ δ) :
    StructuralMicroscopic μ a (fun j => Embeds (completeTree 1 j)) k
      (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) := by
  refine lem_S_rary_i hT hη fun δ hδ => ?_
  filter_upwards [eventually_mul_add_le_rpow inf_le_left hk zero_le_one 1 δ hδ] with n hn
  rw [internalCount_completeTree_one, leafCount_completeTree_one]
  push_cast
  linarith

/-- **Lemma `lem:S_rary`(i)**, `r ≥ 2`: the hypothesis
`s_{r,k_n} + ℓ_{r,k_n} = (r^{k_n} - 1)/(r - 1) + r^{k_n} = n^{o(1)}` is `r^{k_n} = n^{o(1)}`. -/
theorem lem_S_rary_i_of_two_le {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ} (hT : StableToolkit μ α a)
    {r : ℕ} (hr : 2 ≤ r) {η : ℝ} (hη : 0 < η ∧ η < 1 - 1 / α) {k : ℕ → ℕ}
    (hk : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ, (r : ℝ) ^ k n ≤ (n : ℝ) ^ δ) :
    StructuralMicroscopic μ a (fun j => Embeds (completeTree r j)) k
      (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) := by
  refine lem_S_rary_i hT hη fun δ hδ => ?_
  filter_upwards [eventually_mul_add_le_rpow inf_le_left hk zero_le_two 0 δ hδ] with n hn
  have hs : internalCount (completeTree r (k n)) ≤ r ^ k n := by
    rw [internalCount_completeTree_of_two_le hr]
    exact (Nat.div_le_self _ _).trans (Nat.sub_le _ _)
  have hs' : ((internalCount (completeTree r (k n)) : ℕ) : ℝ) ≤ (r : ℝ) ^ k n := by
    exact_mod_cast hs
  rw [leafCount_completeTree (by omega)]
  push_cast
  linarith

/-! ### P19: the summed pair bound for the raw marks -/

/-- The cut trees `A ∈ 𝒜_ℓ` of class `j`: `H_{r,k} ≺ A[S] ↔ H_{r,j} ≺ S` for every `S`. -/
def classCut (r k ℓ j : ℕ) : Set MarkedTree :=
  {A | A.pos = ℓ ∧ ∀ S, Embeds (completeTree r k) (A.graft S) ↔ Embeds (completeTree r j) S}

theorem classCut_subset (r k ℓ j : ℕ) : classCut r k ℓ j ⊆ cutFamily ℓ :=
  fun _ hA => mem_cutFamily_iff.2 hA.1

theorem cut_mem_classCut_iff {r k ℓ j : ℕ} {T : PlaneTree} (h : ℓ < T.vertexCount) :
    cut ℓ T ∈ classCut r k ℓ j ↔ ReplaceClass r k T ℓ j := by
  simp only [classCut, Set.mem_ofPred_eq, cut_pos h, true_and, graft_cut_eq_replaceAt h,
    ReplaceClass]

variable {μ : PMF ℕ}

/-- The cut-and-graft factorization for one class (P19):
`P(ℓ < |𝒯|, class j, 𝒯_{u_{ℓ+1}} ∈ G_k) π_j = P(ℓ < |𝒯|, class j, 𝒯_{u_{ℓ+1}} ∈ G_j) π_k`. -/
theorem bienayme_classCut_mul (μ : PMF ℕ) (r k ℓ j : ℕ) :
    bienayme μ {T | ℓ + 1 ≤ T.vertexCount ∧ cut ℓ T ∈ classCut r k ℓ j ∧
        fringeAt T ℓ ∈ {S | Embeds (completeTree r k) S}} *
      bienayme μ {S | Embeds (completeTree r j) S} =
    bienayme μ {T | ℓ + 1 ≤ T.vertexCount ∧ cut ℓ T ∈ classCut r k ℓ j ∧
        fringeAt T ℓ ∈ {S | Embeds (completeTree r j) S}} *
      bienayme μ {S | Embeds (completeTree r k) S} := by
  have h1 := bienayme_cut_mem μ ℓ (classCut r k ℓ j) (classCut_subset r k ℓ j)
    (fun _ => {S | Embeds (completeTree r k) S})
  have h2 := bienayme_cut_mem μ ℓ (classCut r k ℓ j) (classCut_subset r k ℓ j)
    (fun _ => {S | Embeds (completeTree r j) S})
  rw [h1, h2]
  simp_rw [Set.indicator_mul_const, ENNReal.tsum_mul_right]
  exact mul_right_comm _ _ _

/-- The event `{ℓ < |𝒯|, G_k(𝒯) = 1, position ℓ of class j}`. -/
def classEvent (r k ℓ j : ℕ) : Set PlaneTree :=
  {T | ℓ + 1 ≤ T.vertexCount ∧ Embeds (completeTree r k) T ∧ ReplaceClass r k T ℓ j}

theorem bienayme_classCut_le (μ : PMF ℕ) (r k ℓ j : ℕ) :
    bienayme μ {T | ℓ + 1 ≤ T.vertexCount ∧ cut ℓ T ∈ classCut r k ℓ j ∧
        fringeAt T ℓ ∈ {S | Embeds (completeTree r j) S}} ≤
      bienayme μ (classEvent r k ℓ j) := by
  refine measure_mono fun T hT => ?_
  obtain ⟨h1, h2, h3⟩ := hT
  have hc := (cut_mem_classCut_iff (by omega)).1 h2
  refine ⟨h1, ?_, hc⟩
  have := (hc (fringeAt T ℓ)).2 h3
  rwa [replaceAt_fringeAt (by omega)] at this

/-- `π_j = P(H_{r,j} ≺ 𝒯) = μ_r^{s_{r,j}}` as a real number (U07). -/
theorem bienayme_real_embeds_completeTree (hc : IsCritical μ) (hne : μ 1 ≠ 1) {r : ℕ}
    (hr : 1 ≤ r) (j : ℕ) :
    (bienayme μ).real {S | Embeds (completeTree r j) S} =
      (μ r).toReal ^ internalCount (completeTree r j) := by
  rw [measureReal_def, bienayme_embeds_completeTree hc hne hr, ENNReal.toReal_pow]

/-- **P19, one position.** `A(ℓ) ≤ ∑_{j ≤ k} (π_k / π_j) P(ℓ < |𝒯|, G_k(𝒯) = 1, class j)`. -/
theorem pair_completeTree_le (hc : IsCritical μ) (hne : μ 1 ≠ 1) {r : ℕ} (hr : 1 ≤ r)
    (hμr : 0 < μ r) (k ℓ : ℕ) :
    (bienayme μ).real {T | ℓ + 1 ≤ T.vertexCount ∧ Embeds (completeTree r k) T ∧
        ∃ U ∈ T.fringeTrees[ℓ]?, Embeds (completeTree r k) U} ≤
      ∑ j ∈ Finset.range (k + 1),
        (bienayme μ).real {S | Embeds (completeTree r k) S} /
          (bienayme μ).real {S | Embeds (completeTree r j) S} *
          (bienayme μ).real (classEvent r k ℓ j) := by
  have hx : 0 < (μ r).toReal := ENNReal.toReal_pos hμr.ne' (PMF.apply_ne_top μ r)
  have hπ : ∀ j, 0 < (bienayme μ).real {S | Embeds (completeTree r j) S} := fun j => by
    rw [bienayme_real_embeds_completeTree hc hne hr]
    positivity
  have hset : {T | ℓ + 1 ≤ T.vertexCount ∧ Embeds (completeTree r k) T ∧
      ∃ U ∈ T.fringeTrees[ℓ]?, Embeds (completeTree r k) U} =
        {T | ℓ + 1 ≤ T.vertexCount ∧ T ∈ {S | Embeds (completeTree r k) S} ∧
          fringeAt T ℓ ∈ {S | Embeds (completeTree r k) S}} :=
    setOf_pair_eq ℓ {S | Embeds (completeTree r k) S}
  rw [hset]
  refine (measureReal_mono (?_ : _ ⊆ ⋃ j ∈ Finset.range (k + 1),
      {T | ℓ + 1 ≤ T.vertexCount ∧ cut ℓ T ∈ classCut r k ℓ j ∧
        fringeAt T ℓ ∈ {S | Embeds (completeTree r k) S}}) (measure_ne_top _ _)).trans
    ((measureReal_biUnion_finset_le _ _).trans (Finset.sum_le_sum fun j _ => ?_))
  · intro T hT
    obtain ⟨h1, h2, h3⟩ := hT
    obtain ⟨j, hj, hcl⟩ := exists_replaceClass hr k h2 (by omega : ℓ < T.vertexCount)
    exact Set.mem_biUnion (Finset.mem_range.2 (by omega))
      ⟨h1, (cut_mem_classCut_iff (by omega)).2 hcl, h3⟩
  · have e := congrArg ENNReal.toReal (bienayme_classCut_mul μ r k ℓ j)
    simp only [ENNReal.toReal_mul, ← measureReal_def] at e
    have hle := ENNReal.toReal_mono (measure_ne_top _ _) (bienayme_classCut_le μ r k ℓ j)
    simp only [← measureReal_def] at hle
    rw [div_mul_eq_mul_div, le_div_iff₀ (hπ j), e]
    rw [mul_comm ((bienayme μ).real {S | Embeds (completeTree r k) S})]
    exact mul_le_mul_of_nonneg_right hle measureReal_nonneg

/-- **P19, count of skeleton positions.** For `j ≥ 1`,
`∑_{ℓ=1}^{M} P(ℓ < |𝒯|, G_k(𝒯) = 1, class j) ≤ r^{k-j} π_k`. -/
theorem sum_bienayme_classEvent_le {r : ℕ} (hr : 1 ≤ r) (k M j : ℕ) (hj : 1 ≤ j) :
    ∑ ℓ ∈ Finset.Icc 1 M, bienayme μ (classEvent r k ℓ j) ≤
      classBound r k j * bienayme μ {S | Embeds (completeTree r k) S} := by
  calc ∑ ℓ ∈ Finset.Icc 1 M, bienayme μ (classEvent r k ℓ j)
      = ∑ ℓ ∈ Finset.Icc 1 M, ∫⁻ T, (classEvent r k ℓ j).indicator 1 T ∂bienayme μ := by
        simp only [lintegral_indicator_one MeasurableSet.of_discrete]
    _ = ∫⁻ T, ∑ ℓ ∈ Finset.Icc 1 M, (classEvent r k ℓ j).indicator 1 T ∂bienayme μ :=
        (lintegral_finsetSum _ fun _ _ => Measurable.of_discrete).symm
    _ ≤ ∫⁻ T, (classBound r k j : ℝ≥0∞) *
          {S | Embeds (completeTree r k) S}.indicator 1 T ∂bienayme μ := by
        refine lintegral_mono fun T => ?_
        by_cases hT : Embeds (completeTree r k) T
        · rw [Set.indicator_of_mem (show T ∈ {S | Embeds (completeTree r k) S} from hT),
            Pi.one_apply, mul_one]
          refine le_trans ?_ (classCount_le hr k hT hj)
          refine (Finset.sum_le_sum_of_ne_zero fun ℓ _ hne => ?_).trans
            (Finset.sum_le_sum fun ℓ _ => ?_)
          · by_contra hℓ
            refine hne (Set.indicator_of_notMem (fun h => hℓ ?_) _)
            exact Finset.mem_range.2 (by have := h.1; omega)
          · by_cases hℓ : T ∈ classEvent r k ℓ j
            · rw [Set.indicator_of_mem hℓ, Set.indicator_of_mem hℓ.2.2]
              exact le_rfl
            · rw [Set.indicator_of_notMem hℓ]
              exact zero_le
        · rw [Set.indicator_of_notMem (show T ∉ {S | Embeds (completeTree r k) S} from hT),
            mul_zero]
          refine le_of_eq (Finset.sum_eq_zero fun ℓ _ => Set.indicator_of_notMem ?_ _)
          exact fun h => hT h.2.1
    _ = (classBound r k j : ℝ≥0∞) * bienayme μ {S | Embeds (completeTree r k) S} := by
        rw [lintegral_const_mul _ Measurable.of_discrete,
          lintegral_indicator_one MeasurableSet.of_discrete]

theorem sum_measureReal_classEvent_le {r : ℕ} (hr : 1 ≤ r) (k M j : ℕ) (hj : 1 ≤ j) :
    ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real (classEvent r k ℓ j) ≤
      classBound r k j * (bienayme μ).real {S | Embeds (completeTree r k) S} := by
  have h := ENNReal.toReal_mono (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _)
    (measure_ne_top _ _)) (sum_bienayme_classEvent_le (μ := μ) hr k M j hj)
  rwa [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _), ENNReal.toReal_mul,
    ENNReal.toReal_natCast] at h

/-- `s_{r,c} + s_{r,a} ≤ s_{r,a+c}` (`r ≥ 1`), where `s_{r,a}` is the number of internal
vertices of `H_{r,a}`. -/
theorem internalCount_completeTree_add_le {r : ℕ} (hr : 1 ≤ r) (a c : ℕ) :
    internalCount (completeTree r c) + internalCount (completeTree r a) ≤
      internalCount (completeTree r (c + a)) := by
  simp only [internalCount_completeTree hr, Finset.sum_range_add, pow_add]
  gcongr with i
  exact Nat.le_mul_of_pos_left _ (pow_pos hr _)

/-- The weights `g_a = r^a μ_r^{s_{r,a}}` of the skeleton contribution are summable (`μ_r < 1`):
for `r = 1` this is the geometric series `∑ μ_1^a`, for `r ≥ 2` the ratio `r μ_r^{r^a}` tends
to `0`. -/
theorem summable_skeletonWeight {r : ℕ} (hr : 1 ≤ r) {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Summable fun a : ℕ => (r : ℝ) ^ a * x ^ internalCount (completeTree r a) := by
  have hstep : ∀ a, (r : ℝ) ^ (a + 1) * x ^ internalCount (completeTree r (a + 1)) =
      ((r : ℝ) * x ^ (r ^ a)) * ((r : ℝ) ^ a * x ^ internalCount (completeTree r a)) := by
    intro a
    rw [internalCount_completeTree hr, internalCount_completeTree hr, Finset.sum_range_succ,
      pow_add, pow_succ]
    ring
  have hρ : max x (1 / 2) < 1 := max_lt hx1 (by norm_num)
  refine summable_of_ratio_norm_eventually_le hρ ?_
  have hev : ∀ᶠ a in atTop, (r : ℝ) * x ^ (r ^ a) ≤ max x (1 / 2) := by
    rcases eq_or_lt_of_le hr with h1 | h2
    · subst h1
      exact Eventually.of_forall fun a => by simp
    · have ht : Tendsto (fun a : ℕ => (r : ℝ) * x ^ (r ^ a)) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one hx0 hx1).comp
          (tendsto_pow_atTop_atTop_of_one_lt (show 1 < r by omega))
        simpa using this.const_mul (r : ℝ)
      filter_upwards [ht.eventually (ge_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with a ha
      exact ha.trans (le_max_right _ _)
  filter_upwards [hev] with a ha
  have hg : 0 ≤ (r : ℝ) ^ a * x ^ internalCount (completeTree r a) := by positivity
  have hg' : 0 ≤ (r : ℝ) ^ (a + 1) * x ^ internalCount (completeTree r (a + 1)) := by positivity
  rw [Real.norm_of_nonneg hg, Real.norm_of_nonneg hg', hstep]
  exact mul_le_mul_of_nonneg_right ha hg

/-- **P19** (source lines 2670–2750): for `r ≥ 1` with `μ_r > 0` there is one constant `K` such
that, for every level `k` and every `M`,
`∑_{ℓ=1}^{M} P(|𝒯| ≥ ℓ+1, G_k(𝒯) = 1, G_k(𝒯_{u_{ℓ+1}(𝒯)}) = 1) ≤ K π_k + M π_k²`. -/
theorem pairSum_completeTree_le (hc : IsCritical μ) (hne : μ 1 ≠ 1) {r : ℕ} (hr : 1 ≤ r)
    (hμr : 0 < μ r) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ k M : ℕ,
      ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real {T | ℓ + 1 ≤ T.vertexCount ∧
          Embeds (completeTree r k) T ∧ ∃ U ∈ T.fringeTrees[ℓ]?, Embeds (completeTree r k) U} ≤
        K * (bienayme μ).real {S | Embeds (completeTree r k) S} +
          M * (bienayme μ).real {S | Embeds (completeTree r k) S} ^ 2 := by
  set x := (μ r).toReal with hx_def
  have hx0 : 0 < x := ENNReal.toReal_pos hμr.ne' (PMF.apply_ne_top μ r)
  have hx1 : x < 1 := by
    have hpair : LeafHeight.mass μ 0 + LeafHeight.mass μ r ≤ 1 := by
      have := sum_le_hasSum ({0, r} : Finset ℕ) (fun i _ => LeafHeight.mass_nonneg (μ := μ) i)
        (LeafHeight.hasSum_mass (μ := μ))
      rwa [Finset.sum_pair (by omega)] at this
    have h0 := LeafHeight.mass_zero_pos hc hne
    simp only [LeafHeight.mass] at hpair h0
    rw [hx_def]
    linarith
  set s : ℕ → ℕ := fun a => internalCount (completeTree r a) with hs_def
  set g : ℕ → ℝ := fun a => (r : ℝ) ^ a * x ^ s a with hg_def
  have hgs : Summable g := summable_skeletonWeight hr hx0.le hx1
  have hg0 : ∀ a, 0 ≤ g a := fun a => by positivity
  refine ⟨∑' a, g a, tsum_nonneg hg0, fun k M => ?_⟩
  set π : ℕ → ℝ := fun j => (bienayme μ).real {S | Embeds (completeTree r j) S} with hπ_def
  have hπx : ∀ j, π j = x ^ s j := fun j => bienayme_real_embeds_completeTree hc hne hr j
  have hπ0 : ∀ j, 0 < π j := fun j => by rw [hπx]; positivity
  -- the class `0` terms: at most `M π_k²`
  have hzero : π k / π 0 * ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real (classEvent r k ℓ 0) ≤
      M * π k ^ 2 := by
    have h0 : π 0 = 1 := by rw [hπx]; simp [hs_def]
    rw [h0, div_one]
    have hsum : ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real (classEvent r k ℓ 0) ≤ M * π k := by
      calc ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real (classEvent r k ℓ 0)
          ≤ ∑ ℓ ∈ Finset.Icc 1 M, π k :=
            Finset.sum_le_sum fun ℓ _ => measureReal_mono fun T hT => hT.2.1
        _ = M * π k := by simp
    calc π k * ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real (classEvent r k ℓ 0)
        ≤ π k * (M * π k) := mul_le_mul_of_nonneg_left hsum (hπ0 k).le
      _ = M * π k ^ 2 := by ring
  -- the class `j = i + 1 ≥ 1` terms: at most `g (k - 1 - i) π_k`
  have hpos : ∀ i ∈ Finset.range k,
      π k / π (i + 1) * ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real (classEvent r k ℓ (i + 1)) ≤
        g (k - 1 - i) * π k := by
    intro i hi
    have hik : i + 1 ≤ k := Finset.mem_range.1 hi
    have hcnt := sum_measureReal_classEvent_le (μ := μ) hr k M (i + 1) (by omega)
    have hb : (classBound r k (i + 1) : ℝ) = (r : ℝ) ^ (k - 1 - i) := by
      simp [classBound, hik, show k - (i + 1) = k - 1 - i by omega]
    rw [hb] at hcnt
    have hratio : π k / π (i + 1) ≤ x ^ s (k - 1 - i) := by
      rw [div_le_iff₀ (hπ0 _), hπx, hπx, ← pow_add]
      refine pow_le_pow_of_le_one hx0.le hx1.le ?_
      have := internalCount_completeTree_add_le hr (k - 1 - i) (i + 1)
      rw [show i + 1 + (k - 1 - i) = k by omega] at this
      simp only [hs_def]
      omega
    calc π k / π (i + 1) * ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real (classEvent r k ℓ (i + 1))
        ≤ x ^ s (k - 1 - i) * ((r : ℝ) ^ (k - 1 - i) * π k) :=
          mul_le_mul hratio hcnt (Finset.sum_nonneg fun _ _ => measureReal_nonneg)
            (by positivity)
      _ = g (k - 1 - i) * π k := by simp only [hg_def]; ring
  calc ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real {T | ℓ + 1 ≤ T.vertexCount ∧
          Embeds (completeTree r k) T ∧ ∃ U ∈ T.fringeTrees[ℓ]?, Embeds (completeTree r k) U}
      ≤ ∑ ℓ ∈ Finset.Icc 1 M, ∑ j ∈ Finset.range (k + 1),
          π k / π j * (bienayme μ).real (classEvent r k ℓ j) :=
        Finset.sum_le_sum fun ℓ _ => pair_completeTree_le hc hne hr hμr k ℓ
    _ = ∑ j ∈ Finset.range (k + 1),
          π k / π j * ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real (classEvent r k ℓ j) := by
        rw [Finset.sum_comm]
        simp_rw [Finset.mul_sum]
    _ = ∑ i ∈ Finset.range k, π k / π (i + 1) *
            ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real (classEvent r k ℓ (i + 1)) +
          π k / π 0 * ∑ ℓ ∈ Finset.Icc 1 M, (bienayme μ).real (classEvent r k ℓ 0) :=
        Finset.sum_range_succ' _ _
    _ ≤ ∑ i ∈ Finset.range k, g (k - 1 - i) * π k + M * π k ^ 2 :=
        add_le_add (Finset.sum_le_sum hpos) hzero
    _ = (∑ a ∈ Finset.range k, g a) * π k + M * π k ^ 2 := by
        rw [← Finset.sum_mul, Finset.sum_range_reflect g k]
    _ ≤ (∑' a, g a) * π k + M * π k ^ 2 :=
        add_le_add_left (mul_le_mul_of_nonneg_right (hgs.sum_le_tsum _ fun a _ => hg0 a)
          (hπ0 k).le) _

/-- **Lemma `lem:S_rary`(ii)** (source lines 2670–2753), for an arbitrary cutoff with
`M_n = o(n)` (the paper takes `M_n = ⌊n^{1-η}⌋`, see `lem_S_rary`): if `μ_r > 0` (`r ≥ 1`) and
`n π_{k_n} → ∞` along admissible sizes, the raw marks `G_k = 1{H_{r,k} ≺ ·}` satisfy
Assumption (C) along `(k_n)` with respect to `(M_n)`. The hypothesis
`s_{r,k_n} + ℓ_{r,k_n} = n^{o(1)}` of the lemma is not needed for this part. -/
theorem lem_S_rary_ii (hc : IsCritical μ) (hne : μ 1 ≠ 1) {r : ℕ} (hr : 1 ≤ r) (hμr : 0 < μ r)
    {k M : ℕ → ℕ} (hM : (fun n => (M n : ℝ)) =o[atTop] (fun n => (n : ℝ)))
    (hπ : Tendsto (fun n : ℕ => (n : ℝ) * markProb μ (fun j => Embeds (completeTree r j)) k n)
      (admissibleSizes μ) atTop) :
    NonClustering μ (fun j => Embeds (completeTree r j)) k M := by
  obtain ⟨K, -, hb⟩ := pairSum_completeTree_le hc hne hr hμr
  refine nonClustering_of_pairSum_le hM zero_le_one (eventually_mul_le_of_tendsto hπ K)
    fun n => ?_
  simpa only [pairProb, markProb, one_mul] using hb (k n) (M n)

/-- **Lemma `lem:S_rary`(i) and (ii)** with the paper's hypotheses (source lines 2644–2753):
`r ≥ 1`, `μ_r > 0`, `s_{r,k_n} + ℓ_{r,k_n} = n^{o(1)}`, `η ∈ (0, 1 - 1/α)` and
`M_n = max 1 ⌊n^{1-η}⌋₊` (`= ⌊n^{1-η}⌋` for `n ≥ 1`). Part (iii) (`E[N_{k_n}(𝒯^n)] ∼ n π_{k_n}`)
is Corollary `cor:SM`(ii) and is not included. -/
theorem lem_S_rary {α : ℝ} {a : ℕ → ℝ} (hT : StableToolkit μ α a) {r : ℕ} (hr : 1 ≤ r)
    (hμr : 0 < μ r) {η : ℝ} (hη : 0 < η ∧ η < 1 - 1 / α) {k : ℕ → ℕ}
    (hk : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in admissibleSizes μ,
      ((internalCount (completeTree r (k n)) + leafCount (completeTree r (k n)) : ℕ) : ℝ) ≤
        (n : ℝ) ^ δ) :
    StructuralMicroscopic μ a (fun j => Embeds (completeTree r j)) k
        (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊) ∧
      (Tendsto (fun n : ℕ => (n : ℝ) * markProb μ (fun j => Embeds (completeTree r j)) k n)
          (admissibleSizes μ) atTop →
        NonClustering μ (fun j => Embeds (completeTree r j)) k
          (fun n => max 1 ⌊(n : ℝ) ^ (1 - η)⌋₊)) := by
  have hη1 : η < 1 := by have := hT.rho_pos; linarith
  refine ⟨lem_S_rary_i hT hη hk, fun hπ => ?_⟩
  exact lem_S_rary_ii hT.critical hT.nondegenerate hr hμr
    (Bridge.isCutoff_max_one_floor_rpow hη.1 hη1).isLittleO hπ

/-! ### Lemma `lem:C_rary`: the declumped marks -/

/-- **P21** (source lines 2768–2786): for every `r`, `k` and `ℓ ≥ 1`,
`P(|𝒯| ≥ ℓ+1, Ĝ_k(𝒯) = 1, Ĝ_k(𝒯_{u_{ℓ+1}(𝒯)}) = 1) ≤ π̂_k²`, by Lemma `lem:cut_graft` with
`𝓠_0` the whole tree space and `𝓡` the cut trees all of whose re-graftings are in `{Ĝ_k = 1}`. -/
theorem pair_declumped_completeTree_le (hc : IsCritical μ) (hne : μ 1 ≠ 1) (r k ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) :
    (bienayme μ).real {T | ℓ + 1 ≤ T.vertexCount ∧
        declumpedMark {d | d ≠ r} (Embeds (completeTree r k)) T ∧
        ∃ U ∈ T.fringeTrees[ℓ]?, declumpedMark {d | d ≠ r} (Embeds (completeTree r k)) U} ≤
      (bienayme μ).real {T | declumpedMark {d | d ≠ r} (Embeds (completeTree r k)) T} ^ 2 := by
  have := bienayme_isProbabilityMeasure hc hne
  set E := {T | declumpedMark {d | d ≠ r} (Embeds (completeTree r k)) T} with hE
  have h := lem_cut_graft_real μ ℓ E (I := Unit) (fun _ => Set.univ)
    (fun _ => by rw [bienayme_univ hc hne]; exact one_pos)
    {A | A.pos = ℓ ∧ ∀ S, A.graft S ∈ E} (fun A hA => mem_cutFamily_iff.2 hA.1) (fun _ => ())
    (fun A S _ => A.2.2 S) (fun T h1 h2 h3 => ⟨⟨cut_pos (by omega), fun S => by
      rw [graft_cut_eq_replaceAt (by omega)]
      exact declumpedMark_replaceAt S h2 hℓ (by omega) fun t q ht hq heq =>
        embeds_completeTree_replaceAt k ht hq (by rw [heq]; exact h3.1) S⟩, trivial⟩)
  refine h.trans ?_
  rw [sq]
  refine mul_le_mul_of_nonneg_left (Finset.sup'_le _ _ fun m _ => ?_) measureReal_nonneg
  rw [cond_univ]

/-- **Lemma `lem:C_rary`** (source lines 2762–2791): for every `r`, every level sequence `(k_n)`
and every cutoff sequence with `M_n = o(n)`, the declumped complete `r`-ary marks
`Ĝ_k = 1{k_∅ ≠ r} 1{∃ child c, H_{r,k} ≺ 𝒯_c}` satisfy Assumption (C):
`∑_{ℓ=1}^{M_n} Â_n(ℓ) ≤ M_n π̂_{k_n}² = o(n π̂_{k_n}²)`. -/
theorem lem_C_rary (hc : IsCritical μ) (hne : μ 1 ≠ 1) (r : ℕ) (k M : ℕ → ℕ)
    (hM : (fun n => (M n : ℝ)) =o[atTop] (fun n => (n : ℝ))) :
    NonClustering μ (fun j => declumpedMark {d | d ≠ r} (Embeds (completeTree r j))) k M := by
  refine nonClustering_of_pairSum_le hM (K := 0) zero_le_one
    (fun ε hε => Eventually.of_forall fun n => by
      rw [zero_mul]
      exact mul_nonneg hε.le (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))) fun n => ?_
  calc ∑ ℓ ∈ Finset.Icc 1 (M n), pairProb μ
        (fun j => declumpedMark {d | d ≠ r} (Embeds (completeTree r j))) k n ℓ
      ≤ ∑ ℓ ∈ Finset.Icc 1 (M n), markProb μ
          (fun j => declumpedMark {d | d ≠ r} (Embeds (completeTree r j))) k n ^ 2 :=
        Finset.sum_le_sum fun ℓ hℓ =>
          pair_declumped_completeTree_le hc hne r (k n) ℓ (Finset.mem_Icc.1 hℓ).1
    _ = 0 * markProb μ (fun j => declumpedMark {d | d ≠ r} (Embeds (completeTree r j))) k n +
          1 * (M n : ℝ) * markProb μ
            (fun j => declumpedMark {d | d ≠ r} (Embeds (completeTree r j))) k n ^ 2 := by
        simp

/-- **Lemma `lem:C_rary`** for every cutoff sequence (`IsCutoff M`). -/
theorem lem_C_rary_of_isCutoff (hc : IsCritical μ) (hne : μ 1 ≠ 1) (r : ℕ) (k : ℕ → ℕ)
    {M : ℕ → ℕ} (hM : IsCutoff M) :
    NonClustering μ (fun j => declumpedMark {d | d ≠ r} (Embeds (completeTree r j))) k M :=
  lem_C_rary hc hne r k M hM.isLittleO

end Applications

end PoissonDeclumping
