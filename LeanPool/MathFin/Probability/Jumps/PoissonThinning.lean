/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.IdentDistrib
public import Mathlib.Topology.UniformSpace.Uniformizable

/-!
# Thinning (splitting) of a Poisson count: the binomial-marking factorisation

Saporito, Theorem 3.3.10: mark each event of a `Poisson(r)` count
independently as type 1 with probability `p`, type 2 with probability `1 − p`.
Then the two type counts are **independent** Poissons with rates `p·r` and
`(1−p)·r`. The surprise is the conclusion — independence plus the thinned
marginal laws — and none of it is in Mathlib.

The textbook marking mechanism says: the joint pmf of the pair
`(type-1 count, type-2 count)` at `(j, k)` is

  `P(N = j+k) · C(j+k, j) pʲ (1−p)ᵏ  =  e^{−r} r^{j+k}/(j+k)! · C(j+k,j) pʲ (1−p)ᵏ`

(a Poisson count split by a conditional Binomial). This file takes exactly
that marking law as the hypothesis and **derives** the theorem: the marked
joint measure *is* the product `Poisson(p·r) × Poisson((1−p)·r)`. The heart is
the pointwise factorisation `C(j+k,j)/(j+k)! = 1/(j!·k!)` together with
`e^{−r} = e^{−p·r}·e^{−(1−p)·r}` — after which marginals fall out by
projection and independence by the joint-law-equals-product-law criterion.

The marking law itself is derived as well, from the mechanism it describes: a `Poisson(r)`
count `N` and i.i.d. marks `Y 0, Y 1, …` independent of `N`, the type of the `i`-th event being
whether `Y i` lies in a set `A`. Given `N = n` the number of the first `n` marks in `A` is
`Binomial(n, p)` with `p = P(Y 0 ∈ A)`, by independence and identical distribution of the
marks (a sum over the `C(n, j)` sets of `j` indices), and `N` is independent of the marks; so
the pair of counts satisfies the marking hypothesis (`thinned_streams_of_iid_marks`).

## Main definitions

* `markedWeight`: the weight `e^{−r} r^{j+k}/(j+k)! · C(j+k, j) pʲ (1−p)ᵏ` of the binomially
  marked `Poisson(r)` pair law at `(j, k)`.
* `markedPoissonMeasure`: the measure on `ℕ × ℕ` with these weights.
* `marksIn`: the number of the first `n` marks `Y 0, …, Y (n−1)` that lie in `A`.

## Main results

* `PoissonThinning.markedPoissonMeasure_eq_prod` — the marked joint measure
  factorises as `Poisson(p·r) ×ₘ Poisson((1−p)·r)`.
* `PoissonThinning.thinned_streams` — for counts `M, K` whose joint law is the
  binomial marking of `Poisson(r)`: `M ∼ Poisson(p·r)`, `K ∼ Poisson((1−p)·r)`,
  and `M ⟂ K` (Theorem 3.3.10, all three conclusions derived). `thinned_streams₀` is the
  same statement for a.e.-measurable counts.
* `PoissonThinning.measure_marksIn_eq` — the number of the first `n` i.i.d. marks in `A` is
  `Binomial(n, P(Y 0 ∈ A))`.
* `PoissonThinning.thinned_streams_of_iid_marks` — Theorem 3.3.10 from the mechanism: for a
  `Poisson(r)` count with i.i.d. marks independent of it, the counts of marks in `A` and in
  `Aᶜ` are independent with laws `Poisson(p·r)` and `Poisson((1−p)·r)`.

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 3.3.10

## Tags

Poisson thinning, Poisson splitting, binomial marking, independent Poisson counts,
marked Poisson process, MSC 60G55, MSC 60E05
-/

@[expose] public section

namespace MathFin

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal Nat

namespace PoissonThinning

/-! ### The marked joint measure -/

/-- Weight of the binomially-marked `Poisson(r)` pair law at `(j, k)`:
`e^{−r} r^{j+k}/(j+k)! · C(j+k, j) pʲ (1−p)ᵏ` — "`j+k` events arrived, and a
Binomial(`j+k`, `p`) draw sent `j` of them to stream 1". -/
noncomputable def markedWeight (r p : ℝ≥0) (jk : ℕ × ℕ) : ℝ :=
  rexp (-(r : ℝ)) * (r : ℝ) ^ (jk.1 + jk.2) / (jk.1 + jk.2)! *
    ((jk.1 + jk.2).choose jk.1) * (p : ℝ) ^ jk.1 * (1 - (p : ℝ)) ^ jk.2

/-- The joint law of the two thinned counts, as a measure on `ℕ × ℕ`. -/
noncomputable def markedPoissonMeasure (r p : ℝ≥0) : Measure (ℕ × ℕ) :=
  Measure.sum fun jk ↦ ENNReal.ofReal (markedWeight r p jk) • Measure.dirac jk

lemma markedPoissonMeasure_singleton (r p : ℝ≥0) (jk : ℕ × ℕ) :
    markedPoissonMeasure r p {jk} = ENNReal.ofReal (markedWeight r p jk) := by
  rw [markedPoissonMeasure, Measure.sum_smul_dirac_singleton]

/-! ### The pointwise factorisation -/

/-- **Pointwise factorisation of the marked weight.** For `p ≤ 1`,
`e^{−r} r^{j+k}/(j+k)! · C(j+k,j) pʲ (1−p)ᵏ
  = [e^{−pr}(pr)ʲ/j!] · [e^{−(1−p)r}((1−p)r)ᵏ/k!]`. -/
private lemma markedWeight_eq {r p : ℝ≥0} (hp : p ≤ 1) (j k : ℕ) :
    markedWeight r p (j, k)
      = rexp (-((p * r : ℝ≥0) : ℝ)) * ((p * r : ℝ≥0) : ℝ) ^ j / j ! *
          (rexp (-(((1 - p) * r : ℝ≥0) : ℝ)) *
            (((1 - p) * r : ℝ≥0) : ℝ) ^ k / k !) := by
  have hq : (((1 : ℝ≥0) - p : ℝ≥0) : ℝ) = 1 - (p : ℝ) := by
    rw [NNReal.coe_sub hp, NNReal.coe_one]
  have hfact : ((j + k).choose j : ℝ) * (j ! : ℝ) * (k ! : ℝ) = ((j + k)! : ℝ) := by
    rw [show (j + k).choose j = (j + k).choose k from Nat.choose_symm_add]
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ)
      (Nat.add_choose_mul_factorial_mul_factorial j k)
  have hsplit : rexp (-(r : ℝ))
      = rexp (-((p : ℝ) * r)) * rexp (-((1 - (p : ℝ)) * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hj0 : (j ! : ℝ) ≠ 0 := by positivity
  have hk0 : (k ! : ℝ) ≠ 0 := by positivity
  have hjk0 : ((j + k)! : ℝ) ≠ 0 := by positivity
  rw [markedWeight]
  push_cast [hq]
  rw [hsplit]
  simp only [mul_pow]
  field_simp
  linear_combination (r : ℝ) ^ (j + k) * (p : ℝ) ^ j * (1 - (p : ℝ)) ^ k * hfact

/-! ### The measure-level factorisation -/

/-- **Thinning factorisation (Theorem 3.3.10, law level).** The binomially
marked `Poisson(r)` joint measure is the product
`Poisson(p·r) ×ₘ Poisson((1−p)·r)` — thinned streams are independent Poissons
at the thinned rates. -/
theorem markedPoissonMeasure_eq_prod (r : ℝ≥0) {p : ℝ≥0} (hp : p ≤ 1) :
    markedPoissonMeasure r p
      = (poissonMeasure (p * r)).prod (poissonMeasure ((1 - p) * r)) := by
  refine Measure.ext_of_singleton fun jk ↦ ?_
  obtain ⟨j, k⟩ := jk
  rw [markedPoissonMeasure_singleton, markedWeight_eq hp,
    show ({(j, k)} : Set (ℕ × ℕ)) = {j} ×ˢ {k} from
      (Set.singleton_prod_singleton).symm,
    Measure.prod_prod, poissonMeasure_singleton, poissonMeasure_singleton,
    ENNReal.ofReal_mul (by positivity)]

/-! ### Thinned streams at random-variable level -/

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The marking hypothesis at event level determines the joint law (a.e.-measurable counts). -/
theorem map_pair_eq_marked₀ {M K : Ω → ℕ} (hM : AEMeasurable M μ) (hK : AEMeasurable K μ)
    {r p : ℝ≥0}
    (hjoint : ∀ j k : ℕ, μ {ω | M ω = j ∧ K ω = k}
        = ENNReal.ofReal (markedWeight r p (j, k))) :
    μ.map (fun ω ↦ (M ω, K ω)) = markedPoissonMeasure r p := by
  refine Measure.ext_of_singleton fun jk ↦ ?_
  obtain ⟨j, k⟩ := jk
  rw [Measure.map_apply_of_aemeasurable (hM.prodMk hK) (measurableSet_singleton _),
    markedPoissonMeasure_singleton,
    show (fun ω ↦ (M ω, K ω)) ⁻¹' {(j, k)} = {ω | M ω = j ∧ K ω = k} by
      ext ω; simp [Prod.ext_iff]]
  exact hjoint j k

/-- The marking hypothesis at event level determines the joint law. -/
theorem map_pair_eq_marked {M K : Ω → ℕ} (hM : Measurable M) (hK : Measurable K)
    {r p : ℝ≥0}
    (hjoint : ∀ j k : ℕ, μ {ω | M ω = j ∧ K ω = k}
        = ENNReal.ofReal (markedWeight r p (j, k))) :
    μ.map (fun ω ↦ (M ω, K ω)) = markedPoissonMeasure r p :=
  map_pair_eq_marked₀ hM.aemeasurable hK.aemeasurable hjoint

/-- **Theorem 3.3.10 (thinning/splitting) for a.e.-measurable counts.** If the joint law of the
type counts `(M, K)` is the binomial marking of `Poisson(r)` with marking probability `p ≤ 1`,
then `M ∼ Poisson(p·r)`, `K ∼ Poisson((1−p)·r)`, and `M` and `K` are independent. -/
theorem thinned_streams₀ {M K : Ω → ℕ} (hM : AEMeasurable M μ) (hK : AEMeasurable K μ)
    {r p : ℝ≥0} (hp : p ≤ 1)
    (hjoint : ∀ j k : ℕ, μ {ω | M ω = j ∧ K ω = k}
        = ENNReal.ofReal (markedWeight r p (j, k))) :
    μ.map M = poissonMeasure (p * r) ∧
      μ.map K = poissonMeasure ((1 - p) * r) ∧
      IndepFun M K μ := by
  have hpair : μ.map (fun ω ↦ (M ω, K ω))
      = (poissonMeasure (p * r)).prod (poissonMeasure ((1 - p) * r)) := by
    rw [map_pair_eq_marked₀ hM hK hjoint, markedPoissonMeasure_eq_prod r hp]
  have hMlaw : μ.map M = poissonMeasure (p * r) := by
    rw [← Measure.fst_map_prodMk₀ hM hK, hpair, Measure.fst_prod]
  have hKlaw : μ.map K = poissonMeasure ((1 - p) * r) := by
    rw [← Measure.snd_map_prodMk₀ hM hK, hpair, Measure.snd_prod]
  have σM : SigmaFinite (μ.map M) := by rw [hMlaw]; infer_instance
  have σK : SigmaFinite (μ.map K) := by rw [hKlaw]; infer_instance
  refine ⟨hMlaw, hKlaw, ?_⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map' hM hK σM σK, hMlaw, hKlaw]
  exact hpair

/-- **Theorem 3.3.10 (thinning/splitting), all three conclusions.** If the
joint law of the type counts `(M, K)` is the binomial marking of `Poisson(r)`
with marking probability `p ≤ 1`, then `M ∼ Poisson(p·r)`,
`K ∼ Poisson((1−p)·r)`, and `M` and `K` are **independent**. -/
theorem thinned_streams {M K : Ω → ℕ} (hM : Measurable M) (hK : Measurable K)
    {r p : ℝ≥0} (hp : p ≤ 1)
    (hjoint : ∀ j k : ℕ, μ {ω | M ω = j ∧ K ω = k}
        = ENNReal.ofReal (markedWeight r p (j, k))) :
    μ.map M = poissonMeasure (p * r) ∧
      μ.map K = poissonMeasure ((1 - p) * r) ∧
      IndepFun M K μ :=
  thinned_streams₀ hM.aemeasurable hK.aemeasurable hp hjoint

/-! ### Thinning by i.i.d. marks -/

section IidMarks

open Finset

variable {α : Type*} {mα : MeasurableSpace α}

open scoped Classical in
/-- The number of the first `n` marks `Y 0 ω, …, Y (n - 1) ω` that lie in `A`. -/
noncomputable def marksIn (Y : ℕ → Ω → α) (A : Set α) (n : ℕ) (ω : Ω) : ℕ :=
  ((range n).filter fun i ↦ Y i ω ∈ A).card

open scoped Classical in
/-- The event that the indices `i < n` with `Y i ∈ A` are exactly `S ⊆ range n` is the
intersection of the events `{Y i ∈ A}` (`i ∈ S`) and `{Y i ∉ A}` (`i ∉ S`), `i < n`. -/
lemma setOf_filter_eq (Y : ℕ → Ω → α) (A : Set α) {n : ℕ} {S : Finset ℕ}
    (hS : S ⊆ range n) :
    {ω | (range n).filter (fun i ↦ Y i ω ∈ A) = S}
      = ⋂ i ∈ range n, Y i ⁻¹' (if i ∈ S then A else Aᶜ) := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_preimage, Finset.ext_iff, mem_filter,
    mem_range]
  constructor
  · intro h i hi
    split_ifs with hiS
    · exact ((h i).2 hiS).2
    · exact fun hA ↦ hiS ((h i).1 ⟨hi, hA⟩)
  · intro h i
    constructor
    · rintro ⟨hi, hA⟩
      have hi' := h i hi
      split_ifs at hi' with hiS
      · exact hiS
      · exact absurd hA hi'
    · intro hiS
      have hi := mem_range.1 (hS hiS)
      have hi' := h i hi
      rw [ite_eq_left hiS] at hi'
      exact ⟨hi, hi'⟩

open scoped Classical in
lemma measurableSet_setOf_filter_eq {Y : ℕ → Ω → α} (hY : ∀ i, Measurable (Y i)) {A : Set α}
    (hA : MeasurableSet A) {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n) :
    MeasurableSet {ω | (range n).filter (fun i ↦ Y i ω ∈ A) = S} := by
  rw [setOf_filter_eq Y A hS]
  exact Finset.measurableSet_biInter _ fun i _ ↦ hY i (by split_ifs; exacts [hA, hA.compl])

open scoped Classical in
/-- **The pattern of marks.** For i.i.d. marks, the probability that the indices `i < n` with
`Y i ∈ A` are exactly `S ⊆ range n` is `pᵏ (1 − p)ⁿ⁻ᵏ`, `p = P(Y 0 ∈ A)`, `k = #S`. -/
lemma measure_setOf_filter_eq [IsProbabilityMeasure μ] {Y : ℕ → Ω → α}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ) (hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    {A : Set α} (hA : MeasurableSet A) {n : ℕ} {S : Finset ℕ} (hS : S ⊆ range n) :
    μ {ω | (range n).filter (fun i ↦ Y i ω ∈ A) = S}
      = μ (Y 0 ⁻¹' A) ^ S.card * (1 - μ (Y 0 ⁻¹' A)) ^ (n - S.card) := by
  have hp (i : ℕ) : μ (Y i ⁻¹' A) = μ (Y 0 ⁻¹' A) := (hid i).measure_mem_eq hA
  have hq (i : ℕ) : μ (Y i ⁻¹' Aᶜ) = 1 - μ (Y 0 ⁻¹' A) := by
    rw [Set.preimage_compl, prob_compl_eq_one_sub (hY i hA), hp i]
  have hc1 : ((range n).filter fun i ↦ i ∈ S).card = S.card := by
    rw [filter_mem_eq_inter, inter_eq_right.2 hS]
  have hc2 : ((range n).filter fun i ↦ ¬ i ∈ S).card = n - S.card := by
    have h := card_filter_add_card_filter_not (s := range n) fun i ↦ i ∈ S
    rw [hc1, card_range] at h
    omega
  have hfac : ∀ i ∈ range n, μ (Y i ⁻¹' (if i ∈ S then A else Aᶜ))
      = if i ∈ S then μ (Y 0 ⁻¹' A) else 1 - μ (Y 0 ⁻¹' A) := fun i _ ↦ by
    split_ifs
    exacts [hp i, hq i]
  have hmeas : ∀ i ∈ range n, MeasurableSet (if i ∈ S then A else Aᶜ) := fun i _ ↦ by
    split_ifs
    exacts [hA, hA.compl]
  rw [setOf_filter_eq Y A hS,
    hind.measure_inter_preimage_eq_mul (range n) (sets := fun i ↦ if i ∈ S then A else Aᶜ) hmeas,
    prod_congr rfl hfac, prod_ite, prod_const, prod_const, hc1, hc2]

open scoped Classical in
/-- The event "exactly `j` of the first `n` marks lie in `A`" is the disjoint union, over the
`j`-element subsets `S` of `range n`, of the events "the marks in `A` are exactly `S`". -/
lemma setOf_marksIn_eq (Y : ℕ → Ω → α) (A : Set α) (n j : ℕ) :
    {ω | marksIn Y A n ω = j}
      = ⋃ S ∈ (range n).powersetCard j, {ω | (range n).filter (fun i ↦ Y i ω ∈ A) = S} := by
  ext ω
  simp only [marksIn, Set.mem_ofPred_eq, Set.mem_iUnion, mem_powersetCard, exists_prop]
  constructor
  · intro h
    exact ⟨_, ⟨filter_subset _ _, h⟩, rfl⟩
  · rintro ⟨S, ⟨-, hS⟩, rfl⟩
    exact hS

open scoped Classical in
lemma measurableSet_marksIn_eq {Y : ℕ → Ω → α} (hY : ∀ i, Measurable (Y i)) {A : Set α}
    (hA : MeasurableSet A) (n j : ℕ) : MeasurableSet {ω | marksIn Y A n ω = j} := by
  rw [setOf_marksIn_eq]
  exact Finset.measurableSet_biUnion _ fun S hS ↦
    measurableSet_setOf_filter_eq hY hA (mem_powersetCard.1 hS).1

open scoped Classical in
/-- **The binomial count of i.i.d. marks.** For i.i.d. marks, the number of the first `n` marks
in `A` is `Binomial(n, p)`, `p = P(Y 0 ∈ A)`:
`P(#{i < n : Y i ∈ A} = j) = C(n, j) pʲ (1 − p)ⁿ⁻ʲ`. -/
theorem measure_marksIn_eq [IsProbabilityMeasure μ] {Y : ℕ → Ω → α}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ) (hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ)
    {A : Set α} (hA : MeasurableSet A) (n j : ℕ) :
    μ {ω | marksIn Y A n ω = j}
      = n.choose j * μ (Y 0 ⁻¹' A) ^ j * (1 - μ (Y 0 ⁻¹' A)) ^ (n - j) := by
  rw [setOf_marksIn_eq, measure_biUnion_finset]
  · have hterm : ∀ S ∈ (range n).powersetCard j,
        μ {ω | (range n).filter (fun i ↦ Y i ω ∈ A) = S}
          = μ (Y 0 ⁻¹' A) ^ j * (1 - μ (Y 0 ⁻¹' A)) ^ (n - j) := fun S hS ↦ by
      rw [measure_setOf_filter_eq hY hind hid hA (mem_powersetCard.1 hS).1,
        (mem_powersetCard.1 hS).2]
    rw [sum_congr rfl hterm, sum_const, card_powersetCard, card_range, nsmul_eq_mul, mul_assoc]
  · intro S _ T _ hST
    exact Set.disjoint_left.2 fun ω h₁ h₂ ↦
      hST ((show (range n).filter (fun i ↦ Y i ω ∈ A) = S from h₁).symm.trans h₂)
  · exact fun S hS ↦ measurableSet_setOf_filter_eq hY hA (mem_powersetCard.1 hS).1

open scoped Classical in
/-- The count of marks in `A` among the first `n`, as a function of `n` and of the whole mark
sequence, is measurable. -/
lemma measurable_marksIn_uncurry {A : Set α} (hA : MeasurableSet A) :
    Measurable fun q : ℕ × (ℕ → α) ↦ marksIn (fun i y ↦ y i) A q.1 q.2 := by
  refine measurable_to_countable' fun j ↦ ?_
  have h : (fun q : ℕ × (ℕ → α) ↦ marksIn (fun i y ↦ y i) A q.1 q.2) ⁻¹' {j}
      = ⋃ n : ℕ, {n} ×ˢ {y | marksIn (fun i y ↦ y i) A n y = j} := by
    ext ⟨n, y⟩
    simp
  rw [h]
  exact MeasurableSet.iUnion fun n ↦ (measurableSet_singleton n).prod
    (measurableSet_marksIn_eq (fun i ↦ measurable_pi_apply i) hA n j)

open scoped Classical in
/-- **Thinning by i.i.d. marks (Theorem 3.3.10, the marking derived).** Let `N` be a `Poisson(r)`
count and `Y 0, Y 1, …` i.i.d. marks independent of `N`, and let `A` be a measurable set of marks,
`p = P(Y 0 ∈ A)`. Then the number of the first `N` marks in `A` and the number in `Aᶜ` are
independent, with laws `Poisson(p·r)` and `Poisson((1 − p)·r)`.

The binomial-marking hypothesis of `thinned_streams` is derived: the pair of counts is
`(j, k)` exactly when `N = j + k` and `j` of the first `j + k` marks lie in `A`; the two events
are independent (`N` is independent of the marks), the first has probability
`e^{−r} r^{j+k}/(j+k)!` and the second `C(j+k, j) pʲ (1 − p)ᵏ` (`measure_marksIn_eq`). -/
theorem thinned_streams_of_iid_marks [IsProbabilityMeasure μ] {r : ℝ≥0} {N : Ω → ℕ}
    {Y : ℕ → Ω → α} {A : Set α} (hA : MeasurableSet A)
    (hN : HasLaw N (poissonMeasure r) μ) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hid : ∀ i, IdentDistrib (Y i) (Y 0) μ μ) (hNY : IndepFun N (fun ω i ↦ Y i ω) μ) :
    μ.map (fun ω ↦ marksIn Y A (N ω) ω) = poissonMeasure ((μ (Y 0 ⁻¹' A)).toNNReal * r) ∧
      μ.map (fun ω ↦ marksIn Y Aᶜ (N ω) ω)
        = poissonMeasure ((1 - (μ (Y 0 ⁻¹' A)).toNNReal) * r) ∧
      IndepFun (fun ω ↦ marksIn Y A (N ω) ω) (fun ω ↦ marksIn Y Aᶜ (N ω) ω) μ := by
  set p : ℝ≥0 := (μ (Y 0 ⁻¹' A)).toNNReal
  have hpμ : μ (Y 0 ⁻¹' A) = p := (ENNReal.coe_toNNReal (measure_ne_top _ _)).symm
  have hp1 : p ≤ 1 := by
    have h := prob_le_one (μ := μ) (s := Y 0 ⁻¹' A)
    rw [hpμ] at h
    exact_mod_cast h
  have hYvec : AEMeasurable (fun ω i ↦ Y i ω) μ := .of_eval fun i ↦ (hY i).aemeasurable
  -- the marks in `Aᶜ` are the marks not in `A`, so the two counts add up to the total
  have hsum (n : ℕ) (ω : Ω) : marksIn Y A n ω + marksIn Y Aᶜ n ω = n := by
    have h := card_filter_add_card_filter_not (s := range n) fun i ↦ Y i ω ∈ A
    rw [card_range] at h
    unfold marksIn
    convert h using 3
    ext i
    simp
  have hcount {B : Set α} (hB : MeasurableSet B) :
      AEMeasurable (fun ω ↦ marksIn Y B (N ω) ω) μ :=
    (measurable_marksIn_uncurry hB).comp_aemeasurable (hN.aemeasurable.prodMk hYvec)
  refine thinned_streams₀ (hcount hA) (hcount hA.compl) hp1 fun j k ↦ ?_
  -- the pair of counts is `(j, k)` iff `N = j + k` and `j` of the first `j + k` marks lie in `A`
  have hset : {ω | marksIn Y A (N ω) ω = j ∧ marksIn Y Aᶜ (N ω) ω = k}
      = N ⁻¹' {j + k} ∩ (fun ω i ↦ Y i ω) ⁻¹' {y | marksIn (fun i y ↦ y i) A (j + k) y = j} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    have htot := hsum (N ω) ω
    constructor
    · rintro ⟨h1, h2⟩
      have hN' : N ω = j + k := by omega
      refine ⟨hN', ?_⟩
      rw [← hN']
      exact h1
    · rintro ⟨hN', h1⟩
      have h1' : marksIn Y A (N ω) ω = j := by
        rw [hN']
        exact h1
      exact ⟨h1', by omega⟩
  have hmw : markedWeight r p (j, k) = (rexp (-(r : ℝ)) * (r : ℝ) ^ (j + k) / ((j + k)! : ℝ))
      * ((((j + k).choose j : ℕ) : ℝ) * (p : ℝ) ^ j * (1 - (p : ℝ)) ^ k) := by
    simp only [markedWeight]
    ring
  have hq0 : (0 : ℝ) ≤ 1 - (p : ℝ) := sub_nonneg.2 (by exact_mod_cast hp1)
  rw [hset, hNY.measure_inter_preimage_eq_mul _ _ (measurableSet_singleton (j + k))
      (measurableSet_marksIn_eq (fun i ↦ measurable_pi_apply i) hA (j + k) j),
    ← Measure.map_apply_of_aemeasurable hN.aemeasurable (measurableSet_singleton (j + k)),
    hN.map_eq, poissonMeasure_singleton,
    show (fun ω i ↦ Y i ω) ⁻¹' {y | marksIn (fun i y ↦ y i) A (j + k) y = j}
      = {ω | marksIn Y A (j + k) ω = j} from rfl,
    measure_marksIn_eq hY hind hid hA, hpμ, Nat.add_sub_cancel_left, hmw,
    ENNReal.ofReal_mul (by positivity :
      (0 : ℝ) ≤ rexp (-(r : ℝ)) * (r : ℝ) ^ (j + k) / ((j + k)! : ℝ)),
    ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (((j + k).choose j : ℕ) : ℝ) * (p : ℝ) ^ j),
    ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow (NNReal.coe_nonneg p), ENNReal.ofReal_coe_nnreal, ENNReal.ofReal_pow hq0,
    ENNReal.ofReal_sub _ (NNReal.coe_nonneg p), ENNReal.ofReal_one, ENNReal.ofReal_coe_nnreal]

end IidMarks

end PoissonThinning

end MathFin
