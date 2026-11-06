/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.DirectApplications.NonFringe
public import LeanPool.RareSubtreePatterns.Patterns.Complete
public import LeanPool.RareSubtreePatterns.Cyclic.Markov
public import LeanPool.RareSubtreePatterns.Probability.PoissonTV

/-!
# Vertices of large prescribed outdegree: Proposition `prop:largeoutdegree`

Source lines 1456–1538 (Proposition 3.9 and its proof; inventory P3.9, P07).

`D_n = #{u ∈ 𝒯^n : k_u(𝒯^n) = d_n}` is the marked count `markCount (· .rootDegree = d_n)`.

## Proof route (P07)

* Star patterns: the star `S_d` with root degree `d` is `completeTree d 1`, and for `d ≥ 1`,
  `S_d ≺ T ↔ k_∅(T) = d` (`embeds_star_iff`); hence `P(k_∅(𝒯) = d) = μ_d`
  (`bienayme_real_rootDegree_eq`), and the count is the non-fringe count of `S_{d_n}`.
* Conditional decomposition: `C_d = 1` internal vertex and `L_d = d` leaves (U06,
  `structuralMicroscopic_embeds`), so (S) holds when `d_n = o(a_{M_n})`.
* Uniform descendant pair bound `A_n(ℓ) ≤ μ_{d_n}²` for every `ℓ ≥ 1` by DFS exposure
  (`bienayme_degSeq_pair_le`): the Łukasiewicz path of `𝒯` is a prefix of an i.i.d. walk
  `(X_i)` with `P(X_1 = j - 1) = μ_j`, the outdegree of `u_{i+1}(𝒯)` is `X_{i+1} + 1`, so
  `P(|𝒯| ≥ ℓ+1, k_{u_1} = d, k_{u_{ℓ+1}} = e) ≤ P(X_1 = d-1, X_{ℓ+1} = e-1) = μ_d μ_e`
  (made precise by decomposing according to the first passage time `ζ = |𝒯|`,
  `Cyclic.walkVecLaw_zeta_eq_ofSeq_mem`, and letting the walk length tend to infinity).
* `M_n = o(n)` turns `sup_ℓ A_n(ℓ) ≤ π_n²` into `sup_ℓ A_n(ℓ) = o((n / M_n) π_n²)`, i.e. (C).

## Main statements

* `large_outdegree_of_general`: Proposition 3.9 without the hypotheses `d_n → ∞` and
  "`μ_{d_n} > 0` eventually", which the proof does not use.
* `large_outdegree_of` (**Proposition `prop:largeoutdegree`**, exactly the paper's hypotheses).

The "convergence in distribution to `Po(λ)`" of part (i) is proved in the stronger form
`d_TV(D_n, Po(λ)) → 0`. Conclusion (ii) also contains `D_n → ∞` in probability. As in the
other applications, `d_n = o(a_{M_n})` is assumed along admissible sizes.
-/

@[expose] public section

open MeasureTheory Filter Asymptotics ProbabilityTheory
open scoped Topology ENNReal NNReal

namespace PoissonDeclumping.DirectApplications

open PlaneTree Lukasiewicz

/-! ### Star patterns -/

/-- The star `S_d` (a root with `d` leaf children) is the complete `d`-ary tree of height one;
for `d ≥ 1`, `S_d ≺ T` iff the root of `T` has outdegree `d`. -/
theorem embeds_star_iff {d : ℕ} (hd : 1 ≤ d) (T : PlaneTree) :
    Embeds (completeTree d 1) T ↔ T.rootDegree = d := by
  rw [embeds_completeTree_succ_iff hd 0 T]
  refine ⟨fun h => h.1, fun h => ⟨h, fun U _ => ?_⟩⟩
  rw [completeTree_zero]
  exact Embeds.leaf U

theorem internalCount_star {d : ℕ} (hd : 1 ≤ d) : internalCount (completeTree d 1) = 1 := by
  rw [internalCount_completeTree hd]
  simp

theorem leafCount_star {d : ℕ} (hd : 1 ≤ d) : leafCount (completeTree d 1) = d := by
  rw [leafCount_completeTree hd, pow_one]

/-- `P(k_∅(𝒯) = d) = μ_d` for `d ≥ 1` (source line 1495). -/
theorem bienayme_real_rootDegree_eq {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {d : ℕ}
    (hd : 1 ≤ d) : (bienayme μ).real {T | T.rootDegree = d} = (μ d).toReal := by
  have hset : {T : PlaneTree | T.rootDegree = d} = {T | Embeds (completeTree d 1) T} := by
    ext T
    exact (embeds_star_iff hd T).symm
  rw [hset, measureReal_def, bienayme_embeds_completeTree hc hne hd, internalCount_star hd,
    pow_one]

/-! ### The pair bound by DFS exposure (P07) -/

/-- A coordinate of a walk vector read through a prefix of its list. -/
theorem eq_of_getElem?_take_ofFn {N m i : ℕ} {ω : Fin N → ℤ} {v : ℤ}
    (h : ((List.ofFn ω).take m)[i]? = some v) : ∃ hi : i < N, ω ⟨i, hi⟩ = v := by
  rw [List.getElem?_take] at h
  split_ifs at h with him
  rw [List.getElem?_ofFn] at h
  split_ifs at h with hiN
  exact ⟨hiN, Option.some.inj h⟩

/-- If the walk vector `(X_1, …, X_N)` encodes the tree `T` as its first tree and `T` has outdegree
`d` at its `(i+1)`-st vertex, then `X_{i+1} = d - 1`. -/
theorem coord_eq_of_ofSeq_eq_some {N : ℕ} {ω : Fin N → ℤ} {T : PlaneTree}
    (hT : ofSeq (List.ofFn ω) = some T) {i d : ℕ} (hd : T.degSeq[i]? = some d) :
    ∃ hi : i < N, ω ⟨i, hi⟩ = (d : ℤ) - 1 := by
  obtain ⟨m, -, hm⟩ := ofSeq_eq_some_iff.mp hT
  have h : T.dfsSeq[i]? = some ((d : ℤ) - 1) := by
    rw [dfsSeq, List.getElem?_map, hd]
    rfl
  rw [hm] at h
  exact eq_of_getElem?_take_ofFn h

/-- The product law of `(X_1, …, X_N)` gives `P(X_{i+1} = x, X_{j+1} = y) = P(X = x) P(X = y)` for
distinct coordinates. -/
theorem walkVecLaw_two_coords {μ : PMF ℕ} {N : ℕ} {i j : Fin N} (hij : i ≠ j) (x y : ℤ) :
    walkVecLaw μ N {ω | ω i = x ∧ ω j = y} = stepPMF μ x * stepPMF μ y := by
  classical
  set ν : Measure ℤ := (stepPMF μ).toMeasure with hν
  have hset : {ω : Fin N → ℤ | ω i = x ∧ ω j = y} = Set.univ.pi
      (fun t => if t = i then {x} else if t = j then {y} else Set.univ) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · rintro ⟨hi, hj⟩ t
      split_ifs with h1 h2
      · rw [h1]; exact hi
      · rw [h2]; exact hj
      · exact Set.mem_univ _
    · intro h
      refine ⟨?_, ?_⟩
      · simpa using h i
      · simpa [Ne.symm hij] using h j
  have hfac : ∀ t : Fin N, ν (if t = i then {x} else if t = j then {y} else Set.univ) =
      (if t = i then ν {x} else 1) * (if t = j then ν {y} else 1) := by
    intro t
    by_cases h1 : t = i
    · have h2 : ¬ t = j := fun h => hij (h1 ▸ h)
      rw [ite_eq_left h1, ite_eq_left h1, ite_eq_right h2, mul_one]
    · by_cases h2 : t = j
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right h1, ite_eq_left h2, one_mul]
      · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h1, ite_eq_right h2, mul_one, hν,
          measure_univ]
  rw [hset, walkVecLaw, Measure.pi_pi]
  simp only [← hν]
  rw [Finset.prod_congr rfl fun t _ => hfac t, Finset.prod_mul_distrib, Finset.prod_ite_eq',
    Finset.prod_ite_eq', ite_eq_left (Finset.mem_univ _), ite_eq_left (Finset.mem_univ _), hν,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]

theorem stepPMF_natCast_sub_one (μ : PMF ℕ) (d : ℕ) : stepPMF μ ((d : ℤ) - 1) = μ d := by
  rw [stepPMF_apply, ite_eq_left (by omega)]
  congr
  omega

/-- **Uniform descendant pair bound by DFS exposure** (P07, source lines 1513–1534): for
`ℓ ≥ 1`, `P(|𝒯| ≥ ℓ+1, k_{u_1}(𝒯) = d, k_{u_{ℓ+1}}(𝒯) = e) ≤ μ_d μ_e`. No assumption on `μ` is
needed. -/
theorem bienayme_degSeq_pair_le (μ : PMF ℕ) (d e : ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) :
    bienayme μ {T | T.degSeq[0]? = some d ∧ T.degSeq[ℓ]? = some e} ≤ μ d * μ e := by
  set A : Set PlaneTree := {T | T.degSeq[0]? = some d ∧ T.degSeq[ℓ]? = some e} with hA
  -- truncated sums, through the walk of length `N ≥ ℓ + 1`
  have key : ∀ N : ℕ, ℓ + 1 ≤ N →
      ∑ j ∈ Finset.range (N + 1), bienayme μ (A ∩ {T | T.vertexCount = j}) ≤ μ d * μ e := by
    intro N hN
    have hdisj : Set.PairwiseDisjoint (↑(Finset.range (N + 1))) (fun j =>
        {ω : Fin N → ℤ | zeta (List.ofFn ω) = some j ∧
          ∃ T ∈ A, ofSeq (List.ofFn ω) = some T}) := by
      intro i _ j _ hij
      refine Set.disjoint_left.mpr fun ω hi hj => hij ?_
      have := hi.1.symm.trans hj.1
      exact Option.some.inj this
    have i0 : 0 < N := by omega
    have i1 : ℓ < N := by omega
    have hne : (⟨0, i0⟩ : Fin N) ≠ ⟨ℓ, i1⟩ := by
      intro h
      have := congrArg Fin.val h
      simp only at this
      omega
    calc ∑ j ∈ Finset.range (N + 1), bienayme μ (A ∩ {T | T.vertexCount = j})
        = ∑ j ∈ Finset.range (N + 1), walkVecLaw μ N
            {ω | zeta (List.ofFn ω) = some j ∧ ∃ T ∈ A, ofSeq (List.ofFn ω) = some T} :=
          Finset.sum_congr rfl fun j hj => (Cyclic.walkVecLaw_zeta_eq_ofSeq_mem μ
            (by have := Finset.mem_range.mp hj; omega) A).symm
      _ = walkVecLaw μ N (⋃ j ∈ Finset.range (N + 1),
            {ω | zeta (List.ofFn ω) = some j ∧ ∃ T ∈ A, ofSeq (List.ofFn ω) = some T}) :=
          (measure_biUnion_finset hdisj fun _ _ => (Set.to_countable _).measurableSet).symm
      _ ≤ walkVecLaw μ N {ω | ω ⟨0, i0⟩ = (d : ℤ) - 1 ∧ ω ⟨ℓ, i1⟩ = (e : ℤ) - 1} := by
          refine measure_mono (Set.iUnion₂_subset fun j _ => ?_)
          rintro ω ⟨-, T, ⟨hT0, hTℓ⟩, hT⟩
          obtain ⟨_, h0⟩ := coord_eq_of_ofSeq_eq_some hT hT0
          obtain ⟨_, h1⟩ := coord_eq_of_ofSeq_eq_some hT hTℓ
          exact ⟨h0, h1⟩
      _ = μ d * μ e := by
          rw [walkVecLaw_two_coords hne, stepPMF_natCast_sub_one, stepPMF_natCast_sub_one]
  -- countable additivity over the size
  have hA_eq : A = ⋃ j : ℕ, A ∩ {T | T.vertexCount = j} := by
    ext T
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, exists_eq_right']
  have hdisj' : Pairwise (Function.onFun Disjoint fun j : ℕ => A ∩ {T | T.vertexCount = j}) := by
    intro i j hij
    refine Set.disjoint_left.mpr fun T hi hj => hij ?_
    rw [← hi.2, ← hj.2]
  rw [hA_eq, measure_iUnion hdisj' fun _ => MeasurableSet.of_discrete]
  refine ENNReal.tsum_le_of_sum_range_le fun n => ?_
  refine le_trans ?_ (key (max n (ℓ + 1)) (le_max_right _ _))
  exact Finset.sum_le_sum_of_subset (Finset.range_subset_range.2 (by omega))

/-- The pair probability of the star marks: `A_n(ℓ) ≤ μ_{d_n}²` for every `ℓ ≥ 1`. -/
theorem pairProb_star_le (μ : PMF ℕ) {d : ℕ → ℕ} (hd : ∀ n, 1 ≤ d n) (n : ℕ) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) :
    pairProb μ (fun j T => Embeds (completeTree j 1) T) d n ℓ ≤ (μ (d n)).toReal ^ 2 := by
  have hsub : {T : PlaneTree | ℓ + 1 ≤ T.vertexCount ∧ Embeds (completeTree (d n) 1) T ∧
      ∃ U ∈ T.fringeTrees[ℓ]?, Embeds (completeTree (d n) 1) U} ⊆
      {T | T.degSeq[0]? = some (d n) ∧ T.degSeq[ℓ]? = some (d n)} := by
    rintro T ⟨-, hT, U, hU, hGU⟩
    rw [embeds_star_iff (hd n)] at hT hGU
    refine ⟨?_, ?_⟩
    · cases T with
      | node ts =>
        rw [degSeq, fringeTrees_node]
        simpa using hT
    · rw [degSeq, List.getElem?_map, hU, Option.map_some, hGU]
  rw [pairProb, measureReal_def, sq, ← ENNReal.toReal_mul]
  refine ENNReal.toReal_mono (ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _))
    ((measure_mono hsub).trans (bienayme_degSeq_pair_le μ _ _ hℓ))

/-! ### Proposition 3.9 -/

/-- The star mark `G_d(T) = 1{S_d ≺ T}`. -/
def starMark (d : ℕ) (T : PlaneTree) : Prop := Embeds (completeTree d 1) T

/-- Proposition 3.9 in the generality of its proof (without `d_n → ∞` and without "`μ_{d_n} > 0`
eventually"): for positive integers `d_n` and a cutoff `(M_n)` with `d_n = o(a_{M_n})`,
(i) bounded `n μ_{d_n}` gives `d_TV(D_n, Po(n μ_{d_n})) → 0`, and `n μ_{d_n} → λ ≥ 0` gives
`d_TV(D_n, Po(λ)) → 0`; (ii) `n μ_{d_n} → ∞` gives `D_n / (n μ_{d_n}) → 1` and `D_n → ∞` in
probability, where `D_n = #{u ∈ 𝒯^n : k_u(𝒯^n) = d_n}`. -/
theorem large_outdegree_of_general (h1 : PoissonApproximationStatement) {μ : PMF ℕ} {α : ℝ}
    {a : ℕ → ℝ} (hμ : StableDomain μ α a) {d : ℕ → ℕ} (hdpos : ∀ n, 0 < d n)
    {M : ℕ → ℕ} (hM : IsCutoff M)
    (hdM : (fun n => (d n : ℝ)) =o[admissibleSizes μ] (fun n => a (M n))) :
    ((∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * (μ (d n)).toReal ≤ C) →
      Tendsto (fun n : ℕ => paperTVDist
        ((conditioned μ n).map (markCount (fun T => T.rootDegree = d n)))
        (poissonMeasure (Real.toNNReal ((n : ℝ) * (μ (d n)).toReal))))
        (admissibleSizes μ) (𝓝 0)) ∧
    (∀ lam : ℝ≥0,
      Tendsto (fun n : ℕ => (n : ℝ) * (μ (d n)).toReal) (admissibleSizes μ) (𝓝 (lam : ℝ)) →
      Tendsto (fun n : ℕ => paperTVDist
        ((conditioned μ n).map (markCount (fun T => T.rootDegree = d n))) (poissonMeasure lam))
        (admissibleSizes μ) (𝓝 0)) ∧
    (Tendsto (fun n : ℕ => (n : ℝ) * (μ (d n)).toReal) (admissibleSizes μ) atTop →
      (∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (conditioned μ n).real
        {T | ε < |(markCount (fun T => T.rootDegree = d n) T : ℝ) /
          ((n : ℝ) * (μ (d n)).toReal) - 1|}) (admissibleSizes μ) (𝓝 0)) ∧
      (∀ K : ℕ, Tendsto (fun n : ℕ => (conditioned μ n).real
        {T | markCount (fun T => T.rootDegree = d n) T ≤ K}) (admissibleSizes μ) (𝓝 0))) := by
  have hl : admissibleSizes μ ≤ atTop := inf_le_left
  have hd : ∀ n, 1 ≤ d n := hdpos
  have hGeq : ∀ n, starMark (d n) = fun T => T.rootDegree = d n := fun n =>
    funext fun T => propext (embeds_star_iff (hd n) T)
  have hπ : ∀ n, markProb μ starMark d n = (μ (d n)).toReal := by
    intro n
    unfold markProb
    rw [hGeq n]
    exact bienayme_real_rootDegree_eq hμ.critical hμ.nondegenerate (hd n)
  -- (S): `C_{d_n} = 1 = o(M_n)` and `L_{d_n} = d_n = o(a_{M_n})`
  have hC : (fun n => (internalCount (completeTree (d n) 1) : ℝ)) =o[admissibleSizes μ]
      (fun n => (M n : ℝ)) := by
    have h1' : (fun _ : ℕ => (1 : ℝ)) =o[admissibleSizes μ] (fun n => (M n : ℝ)) := by
      rw [isLittleO_one_left_iff]
      refine (tendsto_natCast_atTop_atTop.comp (hM.tendsto_atTop.mono_left hl)).congr
        fun n => ?_
      simp
    refine h1'.congr' (Eventually.of_forall fun n => ?_) EventuallyEq.rfl
    simp [internalCount_star (hd n)]
  have hL : (fun n => (leafCount (completeTree (d n) 1) : ℝ)) =o[admissibleSizes μ]
      (fun n => a (M n)) :=
    hdM.congr' (Eventually.of_forall fun n => by simp [leafCount_star (hd n)])
      EventuallyEq.rfl
  -- (C): `sup_ℓ A_n(ℓ) ≤ μ_{d_n}² = o((n / M_n) μ_{d_n}²)`
  have hsup : (fun n => ⨆ ℓ : {ℓ : ℕ // 1 ≤ ℓ},
        pairProb μ (fun j T => Embeds (completeTree j 1) T) d n ℓ) =o[admissibleSizes μ]
      (fun n => (n : ℝ) / M n * markProb μ (fun j T => Embeds (completeTree j 1) T) d n ^ 2) := by
    rw [isLittleO_iff]
    intro c hc
    filter_upwards [hl (hM.isLittleO.bound hc), hl (eventually_ge_atTop 1)] with n hn hn1
    have hMpos : (0 : ℝ) < M n := by exact_mod_cast hM.pos n hn1
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [Real.norm_natCast, Real.norm_natCast] at hn
    have hπn : markProb μ (fun j T => Embeds (completeTree j 1) T) d n = (μ (d n)).toReal :=
      hπ n
    have hsup_le : (⨆ ℓ : {ℓ : ℕ // 1 ≤ ℓ},
        pairProb μ (fun j T => Embeds (completeTree j 1) T) d n ℓ) ≤ (μ (d n)).toReal ^ 2 :=
      ciSup_le fun ℓ => pairProb_star_le μ hd n ℓ.2
    have hsup_nonneg : 0 ≤ ⨆ ℓ : {ℓ : ℕ // 1 ≤ ℓ},
        pairProb μ (fun j T => Embeds (completeTree j 1) T) d n ℓ :=
      Real.iSup_nonneg fun ℓ => measureReal_nonneg
    rw [Real.norm_of_nonneg hsup_nonneg, hπn, Real.norm_of_nonneg (by positivity)]
    calc (⨆ ℓ : {ℓ : ℕ // 1 ≤ ℓ},
          pairProb μ (fun j T => Embeds (completeTree j 1) T) d n ℓ)
        ≤ (μ (d n)).toReal ^ 2 := hsup_le
      _ = (M n : ℝ) / n * ((n : ℝ) / M n * (μ (d n)).toReal ^ 2) := by field_simp
      _ ≤ c * ((n : ℝ) / M n * (μ (d n)).toReal ^ 2) := by
          gcongr
          rw [div_le_iff₀ hn0]
          exact hn
  have hconc : PoissonApproximationConclusion μ starMark d :=
    nonfringe_poisson_of_general h1 hμ (fun j => completeTree j 1) hM hC hL hsup
  simp only [PoissonApproximationConclusion, markedCountLaw, hGeq, hπ] at hconc
  obtain ⟨hi, hii⟩ := hconc
  refine ⟨hi, fun lam hlam => ?_, hii⟩
  have hbdd : ∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * (μ (d n)).toReal ≤ C :=
    ⟨lam + 1, Filter.Tendsto.eventually_le_const (show (lam : ℝ) < lam + 1 by linarith) hlam⟩
  refine tendsto_paperTVDist_poissonMeasure_congr _ (hi hbdd) ?_
  have h2 : Tendsto (fun n : ℕ => max ((n : ℝ) * (μ (d n)).toReal) 0) (admissibleSizes μ)
      (𝓝 (max (lam : ℝ) 0)) := hlam.max tendsto_const_nhds
  rw [max_eq_left (NNReal.coe_nonneg lam)] at h2
  have h3 := h2.sub_const (lam : ℝ)
  rw [sub_self] at h3
  refine h3.congr fun n => ?_
  rw [Real.coe_toNNReal']

/-- **Proposition `prop:largeoutdegree`** (source lines 1456–1486), from Theorem 1.1. Let `μ` be
critical in the domain of attraction of an `α`-stable law (normalizing sequence `a`), let
`(d_n)` be positive integers with `d_n → ∞` and `μ_{d_n} > 0` for all large `n`, and let
`(M_n)` be a cutoff sequence with `d_n = o(a_{M_n})`. Let `D_n = #{u ∈ 𝒯^n : k_u(𝒯^n) = d_n}`.
(i) If `(n μ_{d_n})` is bounded, `d_TV(D_n, Po(n μ_{d_n})) → 0`; if `n μ_{d_n} → λ ∈ [0, ∞)`,
then `D_n → Po(λ)` (in total variation, hence in distribution). (ii) If `n μ_{d_n} → ∞`, then
`D_n / (n μ_{d_n}) → 1` in probability (and `D_n → ∞` in probability). -/
theorem large_outdegree_of (h1 : PoissonApproximationStatement) {μ : PMF ℕ} {α : ℝ}
    {a : ℕ → ℝ} (hμ : StableDomain μ α a) {d : ℕ → ℕ} (hdpos : ∀ n, 0 < d n)
    (_hd : Tendsto d atTop atTop) (_hμd : ∀ᶠ n in atTop, 0 < μ (d n))
    {M : ℕ → ℕ} (hM : IsCutoff M)
    (hdM : (fun n => (d n : ℝ)) =o[admissibleSizes μ] (fun n => a (M n))) :
    ((∃ C : ℝ, ∀ᶠ n : ℕ in admissibleSizes μ, (n : ℝ) * (μ (d n)).toReal ≤ C) →
      Tendsto (fun n : ℕ => paperTVDist
        ((conditioned μ n).map (markCount (fun T => T.rootDegree = d n)))
        (poissonMeasure (Real.toNNReal ((n : ℝ) * (μ (d n)).toReal))))
        (admissibleSizes μ) (𝓝 0)) ∧
    (∀ lam : ℝ≥0,
      Tendsto (fun n : ℕ => (n : ℝ) * (μ (d n)).toReal) (admissibleSizes μ) (𝓝 (lam : ℝ)) →
      Tendsto (fun n : ℕ => paperTVDist
        ((conditioned μ n).map (markCount (fun T => T.rootDegree = d n))) (poissonMeasure lam))
        (admissibleSizes μ) (𝓝 0)) ∧
    (Tendsto (fun n : ℕ => (n : ℝ) * (μ (d n)).toReal) (admissibleSizes μ) atTop →
      (∀ ε : ℝ, 0 < ε → Tendsto (fun n : ℕ => (conditioned μ n).real
        {T | ε < |(markCount (fun T => T.rootDegree = d n) T : ℝ) /
          ((n : ℝ) * (μ (d n)).toReal) - 1|}) (admissibleSizes μ) (𝓝 0)) ∧
      (∀ K : ℕ, Tendsto (fun n : ℕ => (conditioned μ n).real
        {T | markCount (fun T => T.rootDegree = d n) T ≤ K}) (admissibleSizes μ) (𝓝 0))) :=
  large_outdegree_of_general h1 hμ hdpos hM hdM

end PoissonDeclumping.DirectApplications
