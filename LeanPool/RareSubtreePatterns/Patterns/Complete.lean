/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Patterns.NonFringe
public import LeanPool.RareSubtreePatterns.LeafHeight.Tree
public import LeanPool.RareSubtreePatterns.Lukasiewicz.Coding

/-!
# Complete `r`-ary patterns, `H_r(T)` and the two-point leaf-height case

Source lines 458–473 (`H_r`, `H_{r,k}`), 827–833 (raw-count characterization of the maximum),
2453–2476 and 2625–2642 (inventory U07), 3031–3042 and 3274–3296 (inventory U09).

* U07: `completeTree r k = H_{r,k}` has `internalCount = k` and `leafCount = 1` for `r = 1`, and
  `internalCount = (r^k - 1)/(r - 1)`, `leafCount = r^k` for `r ≥ 2`
  (`internalCount_completeTree_one`, `internalCount_completeTree_of_two_le`,
  `leafCount_completeTree`); the root occurrence probability is
  `π_k = 𝐏(H_{r,k} ≺ 𝒯) = μ_1^k` (`r = 1`) or `μ_r^{(r^k-1)/(r-1)}` (`r ≥ 2`)
  (`bienayme_embeds_completeTree_one`, `bienayme_embeds_completeTree_of_two_le`, and real forms),
  a specialization of U06 (`bienayme_embeds_eq`).
* `H_r(T) = maxCompleteHeight r T` (for `r ≥ 1`): the set `{k : ∃ u, H_{r,k} ≺ T_u}` contains `0`,
  is downward closed and bounded by `|T|`, so `H_r(T) ≥ k ↔ ∃ u, H_{r,k} ≺ T_u ↔ N_k(T) ≥ 1`
  (`le_maxCompleteHeight_iff`, `le_maxCompleteHeight_iff_markCount_pos`).
* U09, geometric half: if every vertex of `T` has outdegree `0` or `κ` (`κ ≥ 1`), then
  `λ_∅(T) ≥ k ↔ H_{κ,k} ≺ T` (`le_rootLeafHeight_iff_embeds`) and `λ(T) = H_κ(T)`
  (`leafHeight_eq_maxCompleteHeight`). If `c = 1 - κμ_κ = 0`, this holds almost surely for the
  Bienaymé tree and for the size-conditioned trees, and `𝐏(λ_∅(𝒯) ≥ k) = μ_κ^{(κ^k-1)/(κ-1)}`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PoissonDeclumping.PlaneTree

@[simp] theorem completeTree_zero (r : ℕ) : completeTree r 0 = node [] := by
  rw [completeTree]

theorem completeTree_succ (r k : ℕ) :
    completeTree r (k + 1) = node (List.replicate r (completeTree r k)) := by
  rw [completeTree]

private theorem replicate_ne_nil {r : ℕ} (hr : 1 ≤ r) (T : PlaneTree) :
    List.replicate r T ≠ [] := by
  simp only [ne_eq, List.replicate_eq_nil_iff]
  omega

/-! ### U07: counts and root occurrence probability of `H_{r,k}` -/

/-- `H_{r,k}` has `r^k` leaves (`r ≥ 1`). -/
theorem leafCount_completeTree {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    leafCount (completeTree r k) = r ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [completeTree_succ, leafCount_node (replicate_ne_nil hr _), List.map_replicate,
      List.sum_replicate, ih, smul_eq_mul, pow_succ, mul_comm]

/-- `H_{r,k}` has `1 + r + ⋯ + r^{k-1}` internal vertices (`r ≥ 1`). -/
theorem internalCount_completeTree {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    internalCount (completeTree r k) = ∑ j ∈ Finset.range k, r ^ j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [completeTree_succ, internalCount_node (replicate_ne_nil hr _), List.map_replicate,
      List.sum_replicate, ih, smul_eq_mul, Finset.sum_range_succ', Finset.mul_sum]
    simp [pow_succ, mul_comm]

/-- `s_{1,k} = k`. -/
theorem internalCount_completeTree_one (k : ℕ) : internalCount (completeTree 1 k) = k := by
  rw [internalCount_completeTree le_rfl]
  simp

/-- `s_{r,k} = (r^k - 1)/(r - 1)` for `r ≥ 2`. -/
theorem internalCount_completeTree_of_two_le {r : ℕ} (hr : 2 ≤ r) (k : ℕ) :
    internalCount (completeTree r k) = (r ^ k - 1) / (r - 1) := by
  rw [internalCount_completeTree (by omega), Nat.geomSum_eq hr]

/-- `ℓ_{1,k} = 1`. -/
theorem leafCount_completeTree_one (k : ℕ) : leafCount (completeTree 1 k) = 1 := by
  rw [leafCount_completeTree le_rfl, one_pow]

/-- Every internal vertex of `H_{r,k}` has `r` children. -/
theorem patternWeight_completeTree (μ : PMF ℕ) {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    patternWeight μ (completeTree r k) = μ r ^ internalCount (completeTree r k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [completeTree_succ, patternWeight_node μ (replicate_ne_nil hr _),
      internalCount_node (replicate_ne_nil hr _), List.map_replicate, List.prod_replicate,
      List.map_replicate, List.sum_replicate, List.length_replicate, ih, smul_eq_mul, pow_succ,
      ← pow_mul, mul_comm (μ r), mul_comm r]

/-- `π_k = 𝐏(H_{r,k} ≺ 𝒯) = μ_r^{s_{r,k}}` (source lines 2468–2476). -/
theorem bienayme_embeds_completeTree {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {r : ℕ}
    (hr : 1 ≤ r) (k : ℕ) :
    bienayme μ {T | Embeds (completeTree r k) T} = μ r ^ internalCount (completeTree r k) := by
  rw [bienayme_embeds_eq hc hne, patternWeight_completeTree μ hr]

/-- U07, `r = 1`: `π_k = μ_1^k`. -/
theorem bienayme_embeds_completeTree_one {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (k : ℕ) : bienayme μ {T | Embeds (completeTree 1 k) T} = μ 1 ^ k := by
  rw [bienayme_embeds_completeTree hc hne le_rfl, internalCount_completeTree_one]

/-- U07, `r ≥ 2`: `π_k = μ_r^{(r^k-1)/(r-1)}`. -/
theorem bienayme_embeds_completeTree_of_two_le {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {r : ℕ} (hr : 2 ≤ r) (k : ℕ) :
    bienayme μ {T | Embeds (completeTree r k) T} = μ r ^ ((r ^ k - 1) / (r - 1)) := by
  rw [bienayme_embeds_completeTree hc hne (by omega), internalCount_completeTree_of_two_le hr]

theorem bienayme_real_embeds_completeTree_one {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (k : ℕ) : (bienayme μ).real {T | Embeds (completeTree 1 k) T} = (μ 1).toReal ^ k := by
  rw [measureReal_def, bienayme_embeds_completeTree_one hc hne, ENNReal.toReal_pow]

theorem bienayme_real_embeds_completeTree_of_two_le {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) {r : ℕ} (hr : 2 ≤ r) (k : ℕ) :
    (bienayme μ).real {T | Embeds (completeTree r k) T} =
      (μ r).toReal ^ ((r ^ k - 1) / (r - 1)) := by
  rw [measureReal_def, bienayme_embeds_completeTree_of_two_le hc hne hr, ENNReal.toReal_pow]

/-! ### The maximal complete height `H_r(T)` -/

private theorem forall₂_replicate_left_iff {R : PlaneTree → PlaneTree → Prop} {r : ℕ}
    {a : PlaneTree} {l : List PlaneTree} :
    List.Forall₂ R (List.replicate r a) l ↔ l.length = r ∧ ∀ b ∈ l, R a b := by
  induction l generalizing r with
  | nil => cases r <;> simp
  | cons b l ih =>
    cases r with
    | zero => simp
    | succ r =>
      simp only [List.replicate_succ, List.forall₂_cons, ih, List.length_cons,
        Nat.add_right_cancel_iff, List.mem_cons, forall_eq_or_imp]
      tauto

/-- `H_{r,k+1} ≺ T` iff the root has exactly `r` children and `H_{r,k} ≺` each of them. -/
theorem embeds_completeTree_succ_iff {r : ℕ} (hr : 1 ≤ r) (k : ℕ) (T : PlaneTree) :
    Embeds (completeTree r (k + 1)) T ↔
      T.rootDegree = r ∧ ∀ U ∈ T.children, Embeds (completeTree r k) U := by
  rw [completeTree_succ, embeds_node_iff (replicate_ne_nil hr _), forall₂_replicate_left_iff]
  rfl

theorem embeds_completeTree_of_succ {r : ℕ} (hr : 1 ≤ r) {k : ℕ} {T : PlaneTree}
    (h : Embeds (completeTree r (k + 1)) T) : Embeds (completeTree r k) T := by
  induction k generalizing T with
  | zero => simpa using Embeds.leaf T
  | succ k ih =>
    rw [embeds_completeTree_succ_iff hr] at h ⊢
    exact ⟨h.1, fun U hU => ih (h.2 U hU)⟩

/-- `H_{r,k'} ≺ T` and `k ≤ k'` imply `H_{r,k} ≺ T`. -/
theorem embeds_completeTree_mono {r : ℕ} (hr : 1 ≤ r) {k k' : ℕ} (hk : k ≤ k') {T : PlaneTree}
    (h : Embeds (completeTree r k') T) : Embeds (completeTree r k) T := by
  induction hk with
  | refl => exact h
  | step _ ih => exact ih (embeds_completeTree_of_succ hr h)

/-- A pattern has at most as many vertices as the trees it embeds into. -/
theorem vertexCount_le_of_embeds {T' T : PlaneTree} (h : Embeds T' T) :
    T'.vertexCount ≤ T.vertexCount := by
  rw [vertexCount_eq_of_embeds h, ← leafCount_add_internalCount, add_comm]
  gcongr
  rw [← length_leafTrees h, ← List.length_map (f := vertexCount)]
  apply List.length_le_sum_of_one_le
  intro i hi
  obtain ⟨U, -, rfl⟩ := List.mem_map.1 hi
  exact one_le_vertexCount U


private theorem vertexCount_le_of_mem_fringeTrees {T U : PlaneTree} (hU : U ∈ T.fringeTrees) :
    U.vertexCount ≤ T.vertexCount := by
  induction T using induction_children generalizing U with
  | step T ih =>
    cases T with
    | node ts =>
      rw [fringeTrees_node] at hU
      rcases List.mem_cons.1 hU with rfl | hU
      · exact le_rfl
      · obtain ⟨t, ht, hU⟩ := List.mem_flatMap.1 hU
        calc U.vertexCount ≤ t.vertexCount := ih t ht hU
          _ ≤ (ts.map vertexCount).sum := List.le_sum_of_mem (List.mem_map_of_mem ht)
          _ ≤ (node ts).vertexCount := by rw [vertexCount_node]; omega

theorem succ_le_vertexCount_completeTree {r : ℕ} (hr : 1 ≤ r) (k : ℕ) :
    k + 1 ≤ (completeTree r k).vertexCount := by
  induction k with
  | zero => exact one_le_vertexCount _
  | succ k ih =>
    rw [completeTree_succ, vertexCount_node, List.map_replicate, List.sum_replicate, smul_eq_mul]
    have : (completeTree r k).vertexCount ≤ r * (completeTree r k).vertexCount :=
      Nat.le_mul_of_pos_left _ hr
    omega

theorem zero_mem_setOf_embeds_completeTree (r : ℕ) (T : PlaneTree) :
    0 ∈ {k | ∃ U ∈ T.fringeTrees, Embeds (completeTree r k) U} :=
  ⟨T, self_mem_fringeTrees T, by simpa using Embeds.leaf T⟩

theorem lt_vertexCount_of_embeds_completeTree {r : ℕ} (hr : 1 ≤ r) {T : PlaneTree} {k : ℕ}
    (hk : ∃ U ∈ T.fringeTrees, Embeds (completeTree r k) U) : k < T.vertexCount := by
  obtain ⟨U, hU, h⟩ := hk
  have h1 := succ_le_vertexCount_completeTree hr k
  have h2 := vertexCount_le_of_embeds h
  have h3 := vertexCount_le_of_mem_fringeTrees hU
  omega

theorem exists_embeds_completeTree_of_le {r : ℕ} (hr : 1 ≤ r) {T : PlaneTree} {k k' : ℕ}
    (hkk : k ≤ k') (hk' : ∃ U ∈ T.fringeTrees, Embeds (completeTree r k') U) :
    ∃ U ∈ T.fringeTrees, Embeds (completeTree r k) U := by
  obtain ⟨U, hU, h⟩ := hk'
  exact ⟨U, hU, embeds_completeTree_mono hr hkk h⟩

/-- `H_r(T) ≥ k ↔ ∃ u ∈ T, H_{r,k} ≺ T_u`, for `r ≥ 1`. -/
theorem le_maxCompleteHeight_iff {r : ℕ} (hr : 1 ≤ r) (T : PlaneTree) (k : ℕ) :
    k ≤ maxCompleteHeight r T ↔ ∃ U ∈ T.fringeTrees, Embeds (completeTree r k) U := by
  have hbdd : BddAbove {k | ∃ U ∈ T.fringeTrees, Embeds (completeTree r k) U} :=
    ⟨T.vertexCount, fun k hk => (lt_vertexCount_of_embeds_completeTree hr hk).le⟩
  have hne : ({k | ∃ U ∈ T.fringeTrees, Embeds (completeTree r k) U} : Set ℕ).Nonempty :=
    ⟨0, zero_mem_setOf_embeds_completeTree r T⟩
  unfold maxCompleteHeight
  constructor
  · intro hk
    exact exists_embeds_completeTree_of_le hr hk (Nat.sSup_mem hne hbdd)
  · intro hk
    exact le_csSup hbdd hk

/-- `H_r(T) ≥ k ↔ N_k(T) = ∑_{u ∈ T} 1{H_{r,k} ≺ T_u} ≥ 1` (source lines 827–833). -/
theorem le_maxCompleteHeight_iff_markCount_pos {r : ℕ} (hr : 1 ≤ r) (T : PlaneTree) (k : ℕ) :
    k ≤ maxCompleteHeight r T ↔ 0 < markCount (fun U => Embeds (completeTree r k) U) T := by
  rw [le_maxCompleteHeight_iff hr, markCount_pos_iff]

/-- The maximum `H_r(T)` is attained. -/
theorem exists_embeds_maxCompleteHeight {r : ℕ} (hr : 1 ≤ r) (T : PlaneTree) :
    ∃ U ∈ T.fringeTrees, Embeds (completeTree r (maxCompleteHeight r T)) U :=
  (le_maxCompleteHeight_iff hr T _).1 le_rfl

theorem maxCompleteHeight_lt_vertexCount {r : ℕ} (hr : 1 ≤ r) (T : PlaneTree) :
    maxCompleteHeight r T < T.vertexCount :=
  lt_vertexCount_of_embeds_completeTree hr (exists_embeds_maxCompleteHeight hr T)

/-! ### U09: outdegrees in `{0, κ}` -/

/-- If every vertex of `T` has outdegree `0` or `κ ≥ 1`, then
`λ_∅(T) ≥ k ↔ H_{κ,k} ≺ T` (source lines 3040–3042). -/
theorem le_rootLeafHeight_iff_embeds {κ : ℕ} (hκ : 1 ≤ κ) {T : PlaneTree}
    (hT : ∀ V ∈ T.fringeTrees, V.rootDegree = 0 ∨ V.rootDegree = κ) (k : ℕ) :
    k ≤ rootLeafHeight T ↔ Embeds (completeTree κ k) T := by
  induction k generalizing T with
  | zero =>
    simp only [Nat.zero_le, true_iff, completeTree_zero]
    exact Embeds.leaf T
  | succ k ih =>
    rw [succ_le_rootLeafHeight_iff, embeds_completeTree_succ_iff hκ]
    have hchild : ∀ U ∈ T.children, ∀ V ∈ U.fringeTrees, V.rootDegree = 0 ∨ V.rootDegree = κ :=
      fun U hU V hV => hT V (mem_fringeTrees_of_mem_child hU hV)
    have hroot := hT T (self_mem_fringeTrees T)
    constructor
    · rintro ⟨hne, h⟩
      refine ⟨?_, fun U hU => (ih (hchild U hU)).1 (h U hU)⟩
      rcases hroot with h0 | h0
      · exact absurd (List.eq_nil_of_length_eq_zero h0) hne
      · exact h0
    · rintro ⟨hdeg, h⟩
      refine ⟨fun hnil => ?_, fun U hU => (ih (hchild U hU)).2 (h U hU)⟩
      rw [rootDegree, hnil, List.length_nil] at hdeg
      omega

/-- U09: if every vertex of `T` has outdegree `0` or `κ ≥ 1`, then `λ(T) = H_κ(T)`
(source lines 3277–3280). -/
theorem leafHeight_eq_maxCompleteHeight {κ : ℕ} (hκ : 1 ≤ κ) {T : PlaneTree}
    (hT : ∀ V ∈ T.fringeTrees, V.rootDegree = 0 ∨ V.rootDegree = κ) :
    leafHeight T = maxCompleteHeight κ T := by
  have key : ∀ k, k ≤ leafHeight T ↔ k ≤ maxCompleteHeight κ T := by
    intro k
    rw [le_leafHeight_iff, le_maxCompleteHeight_iff hκ]
    constructor
    · rintro ⟨U, hU, h⟩
      exact ⟨U, hU, (le_rootLeafHeight_iff_embeds hκ
        (fun V hV => hT V (mem_fringeTrees_trans hU hV)) k).1 h⟩
    · rintro ⟨U, hU, h⟩
      exact ⟨U, hU, (le_rootLeafHeight_iff_embeds hκ
        (fun V hV => hT V (mem_fringeTrees_trans hU hV)) k).2 h⟩
  exact le_antisymm ((key _).1 le_rfl) ((key _).2 le_rfl)

/-- Almost surely every outdegree of a `μ`-Bienaymé tree lies in the support of `μ`. -/
theorem ae_rootDegree_mem_support (μ : PMF ℕ) :
    ∀ᵐ T ∂bienayme μ, ∀ V ∈ T.fringeTrees, V.rootDegree ∈ μ.support := by
  rw [ae_iff, bienayme_apply]
  refine ENNReal.tsum_eq_zero.2 fun T => ?_
  by_cases hT : T ∈ {T : PlaneTree | ¬∀ V ∈ T.fringeTrees, V.rootDegree ∈ μ.support}
  · rw [Set.indicator_of_mem hT]
    simp only [Set.mem_ofPred_eq, not_forall] at hT
    obtain ⟨V, hV, hd⟩ := hT
    apply List.prod_eq_zero
    exact List.mem_map.2 ⟨V.rootDegree, List.mem_map_of_mem hV, (PMF.apply_eq_zero_iff μ _).2 hd⟩
  · exact Set.indicator_of_notMem hT _

/-- U09: if `c = 1 - κμ_κ = 0` then almost surely `λ(𝒯) = H_κ(𝒯)`. -/
theorem ae_leafHeight_eq_maxCompleteHeight {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hc0 : LeafHeight.cConst μ = 0) :
    ∀ᵐ T ∂bienayme μ, leafHeight T = maxCompleteHeight (LeafHeight.kappa μ) T := by
  have hsupp := LeafHeight.support_subset_of_cConst_eq_zero hc hc0
  have hκ := LeafHeight.one_le_kappa hc hne
  filter_upwards [ae_rootDegree_mem_support μ] with T hT
  exact leafHeight_eq_maxCompleteHeight hκ fun V hV => by simpa using hsupp (hT V hV)

/-- U09 for the size-conditioned tree: if `c = 0` then `λ(𝒯^n) = H_κ(𝒯^n)` almost surely. -/
theorem ae_conditioned_leafHeight_eq_maxCompleteHeight {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hc0 : LeafHeight.cConst μ = 0) (n : ℕ) :
    ∀ᵐ T ∂conditioned μ n, leafHeight T = maxCompleteHeight (LeafHeight.kappa μ) T :=
  ProbabilityTheory.cond_absolutelyContinuous.ae_le (ae_leafHeight_eq_maxCompleteHeight hc hne hc0)

/-- If `c = 0`: `𝐏(λ_∅(𝒯) ≥ k) = 𝐏(H_{κ,k} ≺ 𝒯)`. -/
theorem bienayme_le_rootLeafHeight_eq_embeds {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hc0 : LeafHeight.cConst μ = 0) (k : ℕ) :
    bienayme μ {T | k ≤ rootLeafHeight T} =
      bienayme μ {T | Embeds (completeTree (LeafHeight.kappa μ) k) T} := by
  have hsupp := LeafHeight.support_subset_of_cConst_eq_zero hc hc0
  have hκ := LeafHeight.one_le_kappa hc hne
  refine measure_congr ?_
  filter_upwards [ae_rootDegree_mem_support μ] with T hT
  exact propext (le_rootLeafHeight_iff_embeds hκ (fun V hV => by simpa using hsupp (hT V hV)) k)

/-- If `c = 0`: `π_k = 𝐏(λ_∅(𝒯) ≥ k) = μ_κ^{(κ^k-1)/(κ-1)}` (source line 3283). -/
theorem bienayme_le_rootLeafHeight_of_cConst_eq_zero {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hc0 : LeafHeight.cConst μ = 0) (k : ℕ) :
    bienayme μ {T | k ≤ rootLeafHeight T} =
      μ (LeafHeight.kappa μ) ^ ((LeafHeight.kappa μ ^ k - 1) / (LeafHeight.kappa μ - 1)) := by
  rw [bienayme_le_rootLeafHeight_eq_embeds hc hne hc0,
    bienayme_embeds_completeTree_of_two_le hc hne
      (LeafHeight.two_le_kappa_of_cConst_eq_zero hc hne hc0).1]

end PoissonDeclumping.PlaneTree
