/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Lukasiewicz.Coding
public import LeanPool.RareSubtreePatterns.Bienayme.Basic


/-!
# Cutting and grafting at a DFS position

Source lines 2487–2509 (Section 6.1 of the paper; inventory U08) and the weight computations in
the proof of Lemma `lem:cut_graft`, lines 2557–2580 (inventory P18).

For a finite plane tree `T` with `|T| ≥ ℓ + 1`, the paper's `Cut_ℓ(T)` replaces the fringe
subtree `T_{u_{ℓ+1}(T)}` at the `(ℓ+1)`-st vertex in depth-first order by a single marked leaf
`⋆`; conversely `A[S]` grafts a tree `S` at the marked leaf of a marked tree `A`.

* `PlaneTree.fringeAt T i` is the fringe subtree at the vertex of DFS index `i` (`0`-indexed), so
  `T_{u_{ℓ+1}(T)} = fringeAt T ℓ = T.fringeTrees[ℓ]`.
* `PlaneTree.replaceAt T i S` replaces that fringe subtree by `S`. It is defined through the
  Łukasiewicz coding: its DFS sequence is the DFS sequence of `T` with the block of `T_{u_{i+1}}`
  replaced by the DFS sequence of `S` (`dfsSeq_replaceAt`).
* A `PlaneTree.MarkedTree` is a plane tree together with the DFS position `pos` of a marked leaf
  `⋆`. `MarkedTree.graft A S = A[S]`, `PlaneTree.cut ℓ T = Cut_ℓ(T)`, and
  `PlaneTree.cutFamily ℓ = 𝒜_ℓ = {Cut_ℓ(T) : |T| ≥ ℓ + 1}`.

Main facts (U08): `cut_graft` (`Cut_ℓ(A[S]) = A`), `fringeAt_graft` (the `(ℓ+1)`-st fringe subtree
of `A[S]` is `S`), `graft_cut` (`T = Cut_ℓ(T)[T_{u_{ℓ+1}}]`), `graft_inj` (uniqueness of the
decomposition once the position of the marked leaf is fixed), `cutFamily_eq`
(`𝒜_ℓ` = the marked trees whose marked leaf is the `(ℓ+1)`-st vertex: the DFS position of `⋆` is
preserved), and the bijection `cutEquiv`.

Weights (P18): `MarkedTree.weight μ A = ∏_{v ∈ A, v ≠ ⋆} μ_{k_v(A)}` and the exact factorization
`weight_graft`: `𝐏_μ(A[S]) = w(A) 𝐏_μ(S)`; the sum over cut trees `bienayme_cut_mem`:
`𝐏(|𝒯| ≥ ℓ+1, Cut_ℓ(𝒯) ∈ 𝓡, 𝒯_{u_{ℓ+1}} ∈ F(Cut_ℓ(𝒯))) = ∑_{A ∈ 𝓡} w(A) 𝐏(𝒯 ∈ F(A))`.
These hold for every offspring law `μ` (no criticality is used).
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PoissonDeclumping.PlaneTree

open Lukasiewicz

/-! ### Fringe subtree at a DFS position -/

/-- The fringe subtree `T_{u_{i+1}(T)}` at the vertex of DFS index `i` (`0`-indexed). It is
`T.fringeTrees[i]` when `i < |T|`; for `i ≥ |T|` it is a (never used) leaf. -/
def fringeAt (T : PlaneTree) (i : ℕ) : PlaneTree := T.fringeTrees.getD i (node [])

theorem fringeAt_eq_getElem {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) :
    fringeAt T i = T.fringeTrees[i]'h := by
  rw [fringeAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

theorem getElem?_fringeTrees_eq {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) :
    T.fringeTrees[i]? = some (fringeAt T i) := by
  rw [fringeAt_eq_getElem h, List.getElem?_eq_getElem h]

theorem fringeAt_zero (T : PlaneTree) : fringeAt T 0 = T := by
  cases T with
  | node ts => simp [fringeAt]

@[simp] theorem vertexCount_leaf : (node []).vertexCount = 1 := by simp [vertexCount]

/-- The DFS sequence of `T` splits around the block of the fringe subtree at DFS index `i`. -/
theorem dfsSeq_eq_append_fringeAt (T : PlaneTree) {i : ℕ} (h : i < T.vertexCount) :
    T.dfsSeq = T.dfsSeq.take i ++ (fringeAt T i).dfsSeq ++
      T.dfsSeq.drop (i + (fringeAt T i).vertexCount) := by
  obtain ⟨z, hz⟩ := dfsSeq_fringeTrees_prefix T i h
  rw [← fringeAt_eq_getElem h] at hz
  have hd : T.dfsSeq.drop (i + (fringeAt T i).vertexCount) = z := by
    rw [← List.drop_drop, ← hz, List.drop_left' (length_dfsSeq _)]
  rw [hd, List.append_assoc, hz, List.take_append_drop]

/-! ### Splicing DFS sequences -/

/-- A sequence with increments `≥ -1`, total sum `-1` and nonnegative proper partial sums is a
DFS sequence. -/
theorem exists_dfsSeq_eq_of_excursion {y : List ℤ} (hy : ∀ a ∈ y, -1 ≤ a) (hs : y.sum = -1)
    (hp : ∀ j < y.length, 0 ≤ (y.take j).sum) : ∃ T : PlaneTree, T.dfsSeq = y := by
  have hn : 1 ≤ y.length := by
    rcases y with _ | ⟨a, y⟩
    · simp at hs
    · simp
  exact mem_range_dfsSeq_iff.mpr ⟨hy, (zeta_eq_length_iff hy hn hs).mpr hp⟩

theorem sum_take_append₃ (a m z : List ℤ) (j : ℕ) :
    ((a ++ m ++ z).take j).sum = (a.take j).sum + (m.take (j - a.length)).sum +
      (z.take (j - a.length - m.length)).sum := by
  rw [List.take_append, List.take_append, List.length_append, List.sum_append, List.sum_append,
    Nat.sub_sub]

/-- Replacing a sub-excursion `u` of a DFS sequence `a ++ u ++ z` by another DFS sequence `s`
yields a DFS sequence. -/
theorem exists_dfsSeq_splice {a u z s : List ℤ}
    (hx : ∃ T : PlaneTree, T.dfsSeq = a ++ u ++ z) (hu : ∃ U : PlaneTree, U.dfsSeq = u)
    (hs : ∃ S : PlaneTree, S.dfsSeq = s) : ∃ T₀ : PlaneTree, T₀.dfsSeq = a ++ s ++ z := by
  obtain ⟨T, hT⟩ := hx
  obtain ⟨U, rfl⟩ := hu
  obtain ⟨S, rfl⟩ := hs
  obtain ⟨hxs, hxp⟩ := dfsSeq_excursion T
  obtain ⟨hus, -⟩ := dfsSeq_excursion U
  obtain ⟨hss, hsp⟩ := dfsSeq_excursion S
  have hU1 : 1 ≤ U.dfsSeq.length := by rw [length_dfsSeq]; exact one_le_vertexCount U
  rw [hT] at hxs hxp
  simp only [List.length_append] at hxp
  have ha0 : 0 ≤ a.sum := by
    have := hxp a.length (by omega)
    rw [sum_take_append₃] at this
    simpa using this
  apply exists_dfsSeq_eq_of_excursion
  · intro b hb
    simp only [List.mem_append] at hb
    rcases hb with (hb | hb) | hb
    · exact neg_one_le_of_mem_dfsSeq (by rw [hT]; simp [hb])
    · exact neg_one_le_of_mem_dfsSeq hb
    · exact neg_one_le_of_mem_dfsSeq (by rw [hT]; simp [hb])
  · simp only [List.sum_append] at hxs ⊢
    linarith
  · intro j hj
    simp only [List.length_append] at hj
    rw [sum_take_append₃]
    rcases le_or_gt j a.length with hj1 | hj1
    · have := hxp j (by omega)
      rw [sum_take_append₃] at this
      simpa [Nat.sub_eq_zero_of_le hj1] using this
    · rcases lt_or_ge j (a.length + S.dfsSeq.length) with hj2 | hj2
      · rw [List.take_of_length_le hj1.le,
          Nat.sub_eq_zero_of_le (by omega : j - a.length ≤ S.dfsSeq.length),
          List.take_zero, List.sum_nil, add_zero]
        have := hsp (j - a.length) (by omega)
        linarith
      · have := hxp (a.length + U.dfsSeq.length + (j - a.length - S.dfsSeq.length)) (by omega)
        rw [sum_take_append₃, List.take_of_length_le (by omega),
          List.take_of_length_le (by omega : U.dfsSeq.length ≤ _ - a.length)] at this
        rw [List.take_of_length_le hj1.le, List.take_of_length_le (by omega), hss]
        rw [hus] at this
        have e : a.length + U.dfsSeq.length + (j - a.length - S.dfsSeq.length) - a.length -
            U.dfsSeq.length = j - a.length - S.dfsSeq.length := by omega
        rw [e] at this
        exact this

/-! ### Replacing a fringe subtree -/

/-- `replaceAt T i S`: the tree obtained from `T` by replacing the fringe subtree
`T_{u_{i+1}(T)}` at the vertex of DFS index `i` by `S`. It is the tree whose DFS sequence is
`𝐱(T)` with the block of `T_{u_{i+1}}` replaced by `𝐱(S)` (`dfsSeq_replaceAt`, for `i < |T|`). -/
noncomputable def replaceAt (T : PlaneTree) (i : ℕ) (S : PlaneTree) : PlaneTree :=
  (ofSeq (T.dfsSeq.take i ++ S.dfsSeq ++
    T.dfsSeq.drop (i + (fringeAt T i).vertexCount))).getD T

theorem dfsSeq_replaceAt {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) (S : PlaneTree) :
    (replaceAt T i S).dfsSeq = T.dfsSeq.take i ++ S.dfsSeq ++
      T.dfsSeq.drop (i + (fringeAt T i).vertexCount) := by
  obtain ⟨T₀, hT₀⟩ := exists_dfsSeq_splice ⟨T, dfsSeq_eq_append_fringeAt T h⟩
    ⟨fringeAt T i, rfl⟩ ⟨S, rfl⟩
  rw [replaceAt, ← hT₀, ofSeq_dfsSeq, Option.getD_some]

theorem length_take_dfsSeq {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) :
    (T.dfsSeq.take i).length = i := by
  rw [List.length_take, length_dfsSeq]
  omega

theorem vertexCount_replaceAt {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) (S : PlaneTree) :
    (replaceAt T i S).vertexCount + (fringeAt T i).vertexCount =
      T.vertexCount + S.vertexCount := by
  have h1 := congrArg List.length (dfsSeq_replaceAt h S)
  have h2 := congrArg List.length (dfsSeq_eq_append_fringeAt T h)
  simp only [List.length_append, length_dfsSeq] at h1 h2
  omega

theorem lt_vertexCount_replaceAt {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount)
    (S : PlaneTree) : i < (replaceAt T i S).vertexCount := by
  have h1 := congrArg List.length (dfsSeq_replaceAt h S)
  simp only [List.length_append, length_dfsSeq, length_take_dfsSeq h] at h1
  have := one_le_vertexCount S
  omega

/-- The DFS sequence before position `i` is unchanged: in particular the vertex where `S` is
grafted keeps its DFS position `i`. -/
theorem take_dfsSeq_replaceAt {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount)
    (S : PlaneTree) : (replaceAt T i S).dfsSeq.take i = T.dfsSeq.take i := by
  rw [dfsSeq_replaceAt h, List.append_assoc, List.take_left' (length_take_dfsSeq h)]

theorem drop_dfsSeq_replaceAt {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount)
    (S : PlaneTree) : (replaceAt T i S).dfsSeq.drop (i + S.vertexCount) =
      T.dfsSeq.drop (i + (fringeAt T i).vertexCount) := by
  rw [dfsSeq_replaceAt h, List.drop_left']
  simp [length_take_dfsSeq h, length_dfsSeq]

/-- After replacement, the fringe subtree at DFS index `i` is `S`. -/
theorem fringeAt_replaceAt {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) (S : PlaneTree) :
    fringeAt (replaceAt T i S) i = S := by
  have e1 := dfsSeq_eq_append_fringeAt (replaceAt T i S) (lt_vertexCount_replaceAt h S)
  rw [take_dfsSeq_replaceAt h, dfsSeq_replaceAt h S, List.append_assoc, List.append_assoc] at e1
  exact (dfsSeq_append_inj (List.append_cancel_left e1)).1.symm

theorem replaceAt_replaceAt {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) (S S' : PlaneTree) :
    replaceAt (replaceAt T i S) i S' = replaceAt T i S' := by
  apply dfsSeq_injective
  rw [dfsSeq_replaceAt (lt_vertexCount_replaceAt h S), fringeAt_replaceAt h,
    take_dfsSeq_replaceAt h, drop_dfsSeq_replaceAt h, dfsSeq_replaceAt h]

theorem replaceAt_fringeAt {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) :
    replaceAt T i (fringeAt T i) = T := by
  apply dfsSeq_injective
  rw [dfsSeq_replaceAt h, ← dfsSeq_eq_append_fringeAt T h]

/-- Replacing at the root (DFS index `0`) replaces the whole tree. -/
theorem replaceAt_zero (T S : PlaneTree) : replaceAt T 0 S = S := by
  apply dfsSeq_injective
  rw [dfsSeq_replaceAt (one_le_vertexCount T) S, fringeAt_zero, zero_add,
    List.drop_eq_nil_of_le (by rw [length_dfsSeq]), List.take_zero, List.nil_append,
    List.append_nil]

theorem degSeq_eq_map_dfsSeq (T : PlaneTree) :
    T.degSeq = T.dfsSeq.map fun a => (a + 1).toNat := by
  simp [dfsSeq, List.map_map, Function.comp_def]

theorem degSeq_replaceAt {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) (S : PlaneTree) :
    (replaceAt T i S).degSeq = T.degSeq.take i ++ S.degSeq ++
      T.degSeq.drop (i + (fringeAt T i).vertexCount) := by
  simp only [degSeq_eq_map_dfsSeq, dfsSeq_replaceAt h, List.map_append, List.map_take,
    List.map_drop]

theorem degSeq_eq_append_fringeAt (T : PlaneTree) {i : ℕ} (h : i < T.vertexCount) :
    T.degSeq = T.degSeq.take i ++ (fringeAt T i).degSeq ++
      T.degSeq.drop (i + (fringeAt T i).vertexCount) := by
  have := degSeq_replaceAt h (fringeAt T i)
  rwa [replaceAt_fringeAt h] at this

/-- Bienaymé weights under replacement: `𝐏_μ(T[S/T_{u_{i+1}}]) 𝐏_μ(T_{u_{i+1}}) = 𝐏_μ(T) 𝐏_μ(S)`. -/
theorem weight_replaceAt_mul {T : PlaneTree} {i : ℕ} (h : i < T.vertexCount) (μ : PMF ℕ)
    (S : PlaneTree) :
    weight μ (replaceAt T i S) * weight μ (fringeAt T i) = weight μ T * weight μ S := by
  simp only [weight]
  conv_rhs => rw [degSeq_eq_append_fringeAt T h]
  rw [degSeq_replaceAt h]
  simp only [List.map_append, List.prod_append]
  ring

/-! ### Marked trees, cut and graft -/

/-- A marked tree: a finite plane tree `tree` with a marked leaf `⋆`, recorded by its DFS index
`pos` (`0`-indexed, so `⋆ = u_{pos+1}`). -/
@[ext] structure MarkedTree where
  /-- The underlying plane tree, in which `⋆` is an ordinary leaf. -/
  tree : PlaneTree
  /-- The DFS index of the marked leaf `⋆`. -/
  pos : ℕ
  pos_lt : pos < tree.vertexCount
  fringeAt_pos : fringeAt tree pos = node []

namespace MarkedTree

/-- `A[S]`: graft the tree `S` at the marked leaf of `A`. -/
noncomputable def graft (A : MarkedTree) (S : PlaneTree) : PlaneTree := replaceAt A.tree A.pos S

/-- `w(A) = ∏_{v ∈ A, v ≠ ⋆} μ_{k_v(A)}` (source line 2560): the Bienaymé weight of `A` without
the factor of the marked leaf. -/
noncomputable def weight (μ : PMF ℕ) (A : MarkedTree) : ℝ≥0∞ :=
  ((A.tree.degSeq.eraseIdx A.pos).map μ).prod

theorem pos_lt_vertexCount_graft (A : MarkedTree) (S : PlaneTree) :
    A.pos < (A.graft S).vertexCount := lt_vertexCount_replaceAt A.pos_lt S

/-- The fringe subtree of `A[S]` at the DFS position of `⋆` is `S`. -/
theorem fringeAt_graft (A : MarkedTree) (S : PlaneTree) : fringeAt (A.graft S) A.pos = S :=
  fringeAt_replaceAt A.pos_lt S

theorem vertexCount_graft (A : MarkedTree) (S : PlaneTree) :
    (A.graft S).vertexCount + 1 = A.tree.vertexCount + S.vertexCount := by
  have := vertexCount_replaceAt A.pos_lt S
  rwa [A.fringeAt_pos, vertexCount_leaf] at this

theorem graft_leaf (A : MarkedTree) : A.graft (node []) = A.tree := by
  rw [graft, ← A.fringeAt_pos, replaceAt_fringeAt A.pos_lt]

theorem degSeq_graft (A : MarkedTree) (S : PlaneTree) :
    (A.graft S).degSeq = A.tree.degSeq.take A.pos ++ S.degSeq ++
      A.tree.degSeq.drop (A.pos + 1) := by
  rw [graft, degSeq_replaceAt A.pos_lt, A.fringeAt_pos, vertexCount_leaf]

/-- **Weight factorization** (source line 2562, inventory P18):
`𝐏_μ(𝒯 = A[S]) = w(A) 𝐏_μ(𝒯 = S)`. -/
theorem weight_graft (μ : PMF ℕ) (A : MarkedTree) (S : PlaneTree) :
    PlaneTree.weight μ (A.graft S) = A.weight μ * PlaneTree.weight μ S := by
  simp only [PlaneTree.weight, MarkedTree.weight, degSeq_graft, List.eraseIdx_eq_take_drop_succ,
    List.map_append, List.prod_append]
  ring

/-- `𝐏_μ(𝒯 = A[S]) = w(A) 𝐏_μ(𝒯 = S)`, as point masses of the Bienaymé measure. -/
theorem bienayme_singleton_graft (μ : PMF ℕ) (A : MarkedTree) (S : PlaneTree) :
    bienayme μ {A.graft S} = A.weight μ * bienayme μ {S} := by
  rw [bienayme_apply_singleton, bienayme_apply_singleton, weight_graft]

/-- Consistency check: as an ordinary plane tree, `A` has weight `w(A) μ_0`. -/
theorem weight_tree (μ : PMF ℕ) (A : MarkedTree) :
    PlaneTree.weight μ A.tree = A.weight μ * μ 0 := by
  rw [← graft_leaf, weight_graft]
  simp [PlaneTree.weight, degSeq]

end MarkedTree

open MarkedTree

/-- `Cut_ℓ(T)`: replace the fringe subtree `T_{u_{ℓ+1}(T)}` by a marked leaf `⋆`, which is then
the vertex of DFS index `ℓ`. Only used for `|T| ≥ ℓ + 1` (otherwise a fixed junk value). -/
noncomputable def cut (ℓ : ℕ) (T : PlaneTree) : MarkedTree :=
  if h : ℓ < T.vertexCount then
    ⟨replaceAt T ℓ (node []), ℓ, lt_vertexCount_replaceAt h _, fringeAt_replaceAt h _⟩
  else ⟨node [], 0, by simp, fringeAt_zero _⟩

theorem cut_tree {ℓ : ℕ} {T : PlaneTree} (h : ℓ < T.vertexCount) :
    (cut ℓ T).tree = replaceAt T ℓ (node []) := by
  rw [cut, dite_eq_left h]

/-- The marked leaf of `Cut_ℓ(T)` is its `(ℓ+1)`-st vertex: the DFS position is preserved. -/
theorem cut_pos {ℓ : ℕ} {T : PlaneTree} (h : ℓ < T.vertexCount) : (cut ℓ T).pos = ℓ := by
  rw [cut, dite_eq_left h]

/-- `T = Cut_ℓ(T)[T_{u_{ℓ+1}(T)}]`. -/
theorem graft_cut {ℓ : ℕ} {T : PlaneTree} (h : ℓ < T.vertexCount) :
    (cut ℓ T).graft (fringeAt T ℓ) = T := by
  rw [graft, cut_tree h, cut_pos h, replaceAt_replaceAt h, replaceAt_fringeAt h]

/-- `Cut_ℓ(A[S]) = A` when the marked leaf of `A` is its `(ℓ+1)`-st vertex. -/
theorem cut_graft (A : MarkedTree) (S : PlaneTree) : cut A.pos (A.graft S) = A := by
  have h := A.pos_lt_vertexCount_graft S
  ext
  · rw [cut_tree h, graft, replaceAt_replaceAt A.pos_lt, ← A.fringeAt_pos,
      replaceAt_fringeAt A.pos_lt]
  · rw [cut_pos h]

/-- Uniqueness of the decomposition `T = A[S]` once the position of the marked leaf is fixed. -/
theorem graft_inj {A A' : MarkedTree} {S S' : PlaneTree} (hpos : A.pos = A'.pos)
    (h : A.graft S = A'.graft S') : A = A' ∧ S = S' := by
  constructor
  · rw [← cut_graft A S, ← cut_graft A' S', h, hpos]
  · rw [← A.fringeAt_graft S, ← A'.fringeAt_graft S', h, hpos]

/-- `𝒜_ℓ = {Cut_ℓ(T) : |T| ≥ ℓ + 1}` (source line 2504). -/
def cutFamily (ℓ : ℕ) : Set MarkedTree :=
  {A | ∃ T : PlaneTree, ℓ + 1 ≤ T.vertexCount ∧ cut ℓ T = A}

/-- `𝒜_ℓ` consists exactly of the marked trees whose marked leaf is the `(ℓ+1)`-st vertex. -/
theorem cutFamily_eq (ℓ : ℕ) : cutFamily ℓ = {A | A.pos = ℓ} := by
  ext A
  constructor
  · rintro ⟨T, hT, rfl⟩
    exact cut_pos hT
  · intro hA
    simp only [Set.mem_ofPred_eq] at hA
    refine ⟨A.graft (node []), ?_, ?_⟩
    · have := A.pos_lt_vertexCount_graft (node [])
      omega
    · rw [← hA, cut_graft]

theorem mem_cutFamily_iff {ℓ : ℕ} {A : MarkedTree} : A ∈ cutFamily ℓ ↔ A.pos = ℓ := by
  rw [cutFamily_eq]
  rfl

/-- The cut-and-graft bijection `{T : |T| ≥ ℓ + 1} ≃ 𝒜_ℓ × {plane trees}`,
`T ↦ (Cut_ℓ(T), T_{u_{ℓ+1}(T)})`, with inverse `(A, S) ↦ A[S]`. -/
noncomputable def cutEquiv (ℓ : ℕ) :
    {T : PlaneTree // ℓ + 1 ≤ T.vertexCount} ≃ {A : MarkedTree // A.pos = ℓ} × PlaneTree where
  toFun T := (⟨cut ℓ T.1, cut_pos T.2⟩, fringeAt T.1 ℓ)
  invFun p := ⟨p.1.1.graft p.2, by
    have := p.1.1.pos_lt_vertexCount_graft p.2
    rw [p.1.2] at this
    exact this⟩
  left_inv T := Subtype.ext (graft_cut T.2)
  right_inv p := by
    obtain ⟨⟨A, hA⟩, S⟩ := p
    subst hA
    simp only [cut_graft, fringeAt_graft]

/-- **Sum over cut trees** (inventory P18). For `𝓡 ⊆ 𝒜_ℓ` and target sets `F(A)`,
`𝐏_μ(|𝒯| ≥ ℓ+1, Cut_ℓ(𝒯) ∈ 𝓡, 𝒯_{u_{ℓ+1}(𝒯)} ∈ F(Cut_ℓ(𝒯))) = ∑_{A ∈ 𝓡} w(A) 𝐏_μ(𝒯 ∈ F(A))`,
for every offspring law `μ`. -/
theorem bienayme_cut_mem (μ : PMF ℕ) (ℓ : ℕ) (R : Set MarkedTree) (hR : R ⊆ cutFamily ℓ)
    (F : MarkedTree → Set PlaneTree) :
    bienayme μ {T | ℓ + 1 ≤ T.vertexCount ∧ cut ℓ T ∈ R ∧ fringeAt T ℓ ∈ F (cut ℓ T)} =
      ∑' A, R.indicator (fun A => A.weight μ * bienayme μ (F A)) A := by
  set G := {T : PlaneTree | ℓ + 1 ≤ T.vertexCount ∧ cut ℓ T ∈ R ∧ fringeAt T ℓ ∈ F (cut ℓ T)}
    with hG
  let g : {A : MarkedTree // A.pos = ℓ} × PlaneTree → PlaneTree := fun p => p.1.1.graft p.2
  have hg : Function.Injective g := by
    rintro ⟨⟨A, hA⟩, S⟩ ⟨⟨A', hA'⟩, S'⟩ h
    obtain ⟨rfl, rfl⟩ := graft_inj (hA.trans hA'.symm) h
    rfl
  have hsupp : Function.support (G.indicator (weight μ)) ⊆ Set.range g := by
    intro T hT
    have hTG : T ∈ G := Set.support_indicator_subset hT
    exact ⟨(⟨cut ℓ T, cut_pos hTG.1⟩, fringeAt T ℓ), graft_cut hTG.1⟩
  rw [bienayme_apply, ← hg.tsum_eq hsupp, ENNReal.tsum_prod']
  have key : ∀ A : {A : MarkedTree // A.pos = ℓ}, ∑' S, G.indicator (weight μ) (g (A, S)) =
      R.indicator (fun A => A.weight μ * bienayme μ (F A)) A.1 := by
    rintro ⟨A, hA⟩
    have hmem : ∀ S, g (⟨A, hA⟩, S) ∈ G ↔ A ∈ R ∧ S ∈ F A := by
      intro S
      have h1 := A.pos_lt_vertexCount_graft S
      have hc : cut ℓ (A.graft S) = A := by rw [← hA]; exact cut_graft A S
      have hf : fringeAt (A.graft S) ℓ = S := by rw [← hA]; exact fringeAt_graft A S
      simp only [g, hG, Set.mem_ofPred_eq, hc, hf]
      constructor
      · rintro ⟨-, h⟩
        exact h
      · intro h
        exact ⟨by omega, h⟩
    by_cases hAR : A ∈ R
    · rw [Set.indicator_of_mem hAR, bienayme_apply, ← ENNReal.tsum_mul_left]
      refine tsum_congr fun S => ?_
      by_cases hS : S ∈ F A
      · rw [Set.indicator_of_mem ((hmem S).2 ⟨hAR, hS⟩), Set.indicator_of_mem hS, weight_graft]
      · rw [Set.indicator_of_notMem (fun h => hS ((hmem S).1 h).2), Set.indicator_of_notMem hS,
          mul_zero]
    · rw [Set.indicator_of_notMem hAR]
      exact ENNReal.tsum_eq_zero.2 fun S =>
        Set.indicator_of_notMem (fun h => hAR ((hmem S).1 h).1) _
  simp only [key]
  refine tsum_subtype_eq_of_support_subset (s := {A : MarkedTree | A.pos = ℓ}) ?_
  intro A hA
  exact mem_cutFamily_iff.1 (hR (Set.support_indicator_subset hA))

end PoissonDeclumping.PlaneTree
