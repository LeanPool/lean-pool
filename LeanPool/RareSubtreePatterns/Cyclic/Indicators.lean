/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.Lukasiewicz.Coding


/-!
# Cyclic indicators (Definition `def:indicators`)

Source lines 679–696 (DFS sequence, `ζ`, `eq:fringe`) and 735–764 (Section 2.3).

For a mark `G` (a `{0,1}`-valued function on finite plane trees, here a predicate
`G : PlaneTree → Prop`), a cutoff `M ∈ ℕ ∪ {∞}` (here `M : ℕ∞`) and a finite sequence
`𝐱 = (x_1, …, x_n)` of integers (a `List ℤ`):

* `Cyclic.firstIndicator G M 𝐱 = I_1^{(M)}(𝐱)`: it is `1` iff `ζ(𝐱) ≤ M` (in particular
  `ζ(𝐱) < ∞`) and `G(T(x_1, …, x_{ζ(𝐱)})) = 1`, and `0` otherwise (`Cyclic.FirstMarked`);
* `Cyclic.shiftIndicator G M 𝐱 i = I_{i+1}^{(M)}(𝐱) = I_1^{(M)}(x_{i+1}, …, x_n, x_1, …, x_i)`
  (`0`-based shifts: the paper's `I_i` is our `shiftIndicator … (i - 1)`);
* `Cyclic.cyclicSum G M 𝐱 = ∑_{i=1}^{n} I_i^{(M)}(𝐱)`.

We prove the two cases of the definition (`firstIndicator_of_zeta_eq_none`,
`firstIndicator_of_lt_zeta`, `firstIndicator_of_zeta_le`), the Boolean range, locality in the
first `M` entries (`firstIndicator_take`, `firstIndicator_congr_take`), monotonicity in the
cutoff, the infinite cutoff (`firstIndicator_top`), invariance of the cyclic sum under cyclic
shifts (`cyclicSum_rotate`, part of `B04`), and the counting identity of source lines 758–760:
`∑_i I_i^{(M)}(𝐱(T))` is the number of vertices `v` with `|T_v| ≤ M` and `G(T_v) = 1`
(`cyclicSum_dfsSeq`); for `M ≥ |T|` it is `markCount G T` (`cyclicSum_dfsSeq_of_le`).

We also prove `U05` (source lines 914–920, 960–969): a proper fringe subtree has strictly fewer
vertices (`PlaneTree.vertexCount_fringeTrees_lt`), so two marks forcing the same size cannot hold
at a vertex and at a proper descendant (`PlaneTree.not_forced_size_nested`).
-/

@[expose] public section

namespace PoissonDeclumping

open Lukasiewicz

namespace Lukasiewicz

/-- `ζ(x_1, …, x_M) = m` iff `ζ(𝐱) = m ≤ M`: the first passage time is local. -/
theorem zeta_take_eq_some_iff {x : List ℤ} {M m : ℕ} :
    zeta (x.take M) = some m ↔ zeta x = some m ∧ m ≤ M := by
  simp only [zeta_eq_some_iff, List.length_take, List.take_take]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    have hmM : m ≤ M := le_trans h2 (min_le_left _ _)
    refine ⟨⟨h1, le_trans h2 (min_le_right _ _), ?_, fun j hj1 hjm => ?_⟩, hmM⟩
    · rwa [min_eq_left hmM] at h3
    · have := h4 j hj1 hjm
      rwa [min_eq_left (by omega)] at this
  · rintro ⟨⟨h1, h2, h3, h4⟩, hmM⟩
    refine ⟨h1, le_min hmM h2, by rwa [min_eq_left hmM], fun j hj1 hjm => ?_⟩
    rw [min_eq_left (by omega)]
    exact h4 j hj1 hjm

end Lukasiewicz

namespace PlaneTree

/-- If `T(𝐱) = T`, then `ζ(𝐱) = |T|`. -/
theorem zeta_eq_of_ofSeq_eq_some {x : List ℤ} {T : PlaneTree} (h : ofSeq x = some T) :
    zeta x = some T.vertexCount := by
  obtain ⟨m, hz, hT⟩ := ofSeq_eq_some_iff.mp h
  have hm := (zeta_eq_some_iff.mp hz).2.1
  have : T.vertexCount = m := by
    rw [← length_dfsSeq, hT, List.length_take, min_eq_left hm]
  rw [this, hz]

/-- `T(x_1, …, x_M) = T(𝐱)` as soon as `ζ(𝐱) ≤ M`. -/
theorem ofSeq_take_of_zeta_eq {x : List ℤ} {m M : ℕ} (hz : zeta x = some m) (hm : m ≤ M) :
    ofSeq (x.take M) = ofSeq x := by
  have hz' : zeta (x.take M) = some m := zeta_take_eq_some_iff.mpr ⟨hz, hm⟩
  apply Option.ext
  intro T
  simp only [ofSeq_eq_some_iff, hz', hz, Option.some.injEq, exists_eq_left',
    List.take_take, min_eq_left hm]

end PlaneTree

namespace PlaneTree

/-- The fringe subtree at the `i`-th vertex (DFS order, `0`-indexed) has at most `|T| - i`
vertices. -/
theorem vertexCount_fringeTrees_add_le (T : PlaneTree) (i : ℕ) (hi : i < T.fringeTrees.length) :
    (T.fringeTrees[i]).vertexCount + i ≤ T.vertexCount := by
  have h := (dfsSeq_fringeTrees_prefix T i hi).length_le
  rw [length_dfsSeq, List.length_drop, length_dfsSeq] at h
  have : i < T.vertexCount := hi
  omega

/-- `U05`: a proper fringe subtree (at a vertex `u_{i+1}` with `i ≥ 1`, i.e. not the root) has
strictly fewer vertices than the tree. -/
theorem vertexCount_fringeTrees_lt (T : PlaneTree) {i : ℕ} (hi : i < T.fringeTrees.length)
    (h1 : 1 ≤ i) : (T.fringeTrees[i]).vertexCount < T.vertexCount := by
  have := vertexCount_fringeTrees_add_le T i hi
  omega

theorem vertexCount_le_of_mem_fringeTrees {T U : PlaneTree} (hU : U ∈ T.fringeTrees) :
    U.vertexCount ≤ T.vertexCount := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hU
  have := vertexCount_fringeTrees_add_le T i hi
  omega

/-- The fringe subtree at the root is the tree itself. -/
theorem fringeTrees_getElem_zero (T : PlaneTree) (h : 0 < T.fringeTrees.length) :
    T.fringeTrees[0] = T := by
  cases T with
  | node ts => simp

/-- `U05`: two nested marks forcing the same size cannot both hold at the root and at a
proper fringe subtree. -/
theorem not_forced_size_nested {G₁ G₂ : PlaneTree → Prop} {k : ℕ}
    (h₁ : ∀ T, G₁ T → T.vertexCount = k) (h₂ : ∀ T, G₂ T → T.vertexCount = k)
    (T : PlaneTree) {i : ℕ} (hi : i < T.fringeTrees.length) (h1 : 1 ≤ i) :
    ¬(G₁ T ∧ G₂ (T.fringeTrees[i])) := by
  rintro ⟨hT, hU⟩
  have := vertexCount_fringeTrees_lt T hi h1
  rw [h₁ T hT, h₂ _ hU] at this
  exact lt_irrefl _ this

end PlaneTree

namespace Cyclic

open PlaneTree

/-- Definition `def:indicators`: `I_1^{(M)}(𝐱) = 1` iff `ζ(𝐱) ≤ M` (in particular
`ζ(𝐱) < ∞`) and `G(T(x_1, …, x_{ζ(𝐱)})) = 1`. -/
def FirstMarked (G : PlaneTree → Prop) (M : ℕ∞) (x : List ℤ) : Prop :=
  ∃ m : ℕ, zeta x = some m ∧ (m : ℕ∞) ≤ M ∧ ∃ T, ofSeq x = some T ∧ G T

/-- Definition `def:indicators`: the truncated indicator `I_1^{(M)}(𝐱) ∈ {0, 1}`. -/
noncomputable def firstIndicator (G : PlaneTree → Prop) (M : ℕ∞) (x : List ℤ) : ℕ := by
  classical
  exact if FirstMarked G M x then 1 else 0

/-- Definition `def:indicators`: the cyclically shifted indicator. With `0`-based shifts,
`shiftIndicator G M 𝐱 i = I_{i+1}^{(M)}(𝐱) = I_1^{(M)}(x_{i+1}, …, x_n, x_1, …, x_i)`. -/
noncomputable def shiftIndicator (G : PlaneTree → Prop) (M : ℕ∞) (x : List ℤ) (i : ℕ) : ℕ :=
  firstIndicator G M (x.rotate i)

/-- `∑_{i=1}^{n} I_i^{(M)}(𝐱)` for a sequence `𝐱` of length `n`. -/
noncomputable def cyclicSum (G : PlaneTree → Prop) (M : ℕ∞) (x : List ℤ) : ℕ :=
  ∑ i ∈ Finset.range x.length, shiftIndicator G M x i

variable {G : PlaneTree → Prop} {M M' : ℕ∞} {x y : List ℤ}

theorem firstIndicator_eq_one_iff : firstIndicator G M x = 1 ↔ FirstMarked G M x := by
  classical
  unfold firstIndicator
  split_ifs with h <;> simp [h]

theorem firstIndicator_eq_zero_iff : firstIndicator G M x = 0 ↔ ¬FirstMarked G M x := by
  classical
  unfold firstIndicator
  split_ifs with h <;> simp [h]

/-- Boolean range of `I_1^{(M)}`. -/
theorem firstIndicator_eq_zero_or_eq_one (G : PlaneTree → Prop) (M : ℕ∞) (x : List ℤ) :
    firstIndicator G M x = 0 ∨ firstIndicator G M x = 1 := by
  classical
  unfold firstIndicator
  split_ifs <;> simp

theorem firstIndicator_le_one (G : PlaneTree → Prop) (M : ℕ∞) (x : List ℤ) :
    firstIndicator G M x ≤ 1 := by
  rcases firstIndicator_eq_zero_or_eq_one G M x with h | h <;> omega

/-- Boolean range of `I_i^{(M)}`. -/
theorem shiftIndicator_eq_zero_or_eq_one (G : PlaneTree → Prop) (M : ℕ∞) (x : List ℤ) (i : ℕ) :
    shiftIndicator G M x i = 0 ∨ shiftIndicator G M x i = 1 :=
  firstIndicator_eq_zero_or_eq_one G M _

/-- First case of Definition `def:indicators`: `ζ(𝐱) = ∞`. -/
theorem firstIndicator_of_zeta_eq_none (h : zeta x = none) : firstIndicator G M x = 0 := by
  rw [firstIndicator_eq_zero_iff]
  rintro ⟨m, hm, -⟩
  simp [h] at hm

/-- First case of Definition `def:indicators`: `ζ(𝐱) > M`. -/
theorem firstIndicator_of_lt_zeta {m : ℕ} (h : zeta x = some m) (hM : M < m) :
    firstIndicator G M x = 0 := by
  rw [firstIndicator_eq_zero_iff]
  rintro ⟨m', hm', hle, -⟩
  rw [h, Option.some.injEq] at hm'
  subst hm'
  exact absurd hle (not_le.mpr hM)

/-- Second case of Definition `def:indicators`: if `ζ(𝐱) = m ≤ M` and `T` is the tree whose DFS
sequence is `(x_1, …, x_m)`, then `I_1^{(M)}(𝐱) = G(T)`. -/
theorem firstIndicator_of_zeta_le {m : ℕ} {T : PlaneTree} [Decidable (G T)] (h : zeta x = some m)
    (hM : (m : ℕ∞) ≤ M) (hT : T.dfsSeq = x.take m) :
    firstIndicator G M x = if G T then 1 else 0 := by
  have hx : ofSeq x = some T := ofSeq_eq_some_iff.mpr ⟨m, h, hT⟩
  by_cases hG : G T
  · rw [ite_eq_left hG, firstIndicator_eq_one_iff]
    exact ⟨m, h, hM, T, hx, hG⟩
  · rw [ite_eq_right hG, firstIndicator_eq_zero_iff]
    rintro ⟨m', -, -, T', hT', hG'⟩
    rw [hx, Option.some.injEq] at hT'
    exact hG (hT' ▸ hG')

/-- `I_1^{(M)}(𝐱) = 1` iff the tree `T(𝐱)` is defined, has at most `M` vertices and is marked. -/
theorem firstMarked_iff :
    FirstMarked G M x ↔ ∃ T, ofSeq x = some T ∧ (T.vertexCount : ℕ∞) ≤ M ∧ G T := by
  constructor
  · rintro ⟨m, hz, hm, T, hT, hG⟩
    have := zeta_eq_of_ofSeq_eq_some hT
    rw [hz, Option.some.injEq] at this
    exact ⟨T, hT, this ▸ hm, hG⟩
  · rintro ⟨T, hT, hm, hG⟩
    exact ⟨T.vertexCount, zeta_eq_of_ofSeq_eq_some hT, hm, T, hT, hG⟩

/-- Monotonicity of `I_1^{(M)}` in the cutoff. -/
theorem FirstMarked.mono (h : FirstMarked G M x) (hMM' : M ≤ M') : FirstMarked G M' x := by
  obtain ⟨m, hz, hm, hT⟩ := h
  exact ⟨m, hz, hm.trans hMM', hT⟩

theorem firstIndicator_mono (hMM' : M ≤ M') : firstIndicator G M x ≤ firstIndicator G M' x := by
  rcases firstIndicator_eq_zero_or_eq_one G M x with h | h
  · rw [h]; exact Nat.zero_le _
  · rw [h, (firstIndicator_eq_one_iff.mpr ((firstIndicator_eq_one_iff.mp h).mono hMM'))]

theorem monotone_firstIndicator (G : PlaneTree → Prop) (x : List ℤ) :
    Monotone fun M : ℕ∞ => firstIndicator G M x := fun _ _ h => firstIndicator_mono h

theorem shiftIndicator_mono (hMM' : M ≤ M') (i : ℕ) :
    shiftIndicator G M x i ≤ shiftIndicator G M' x i :=
  firstIndicator_mono hMM'

theorem cyclicSum_mono (hMM' : M ≤ M') : cyclicSum G M x ≤ cyclicSum G M' x :=
  Finset.sum_le_sum fun i _ => shiftIndicator_mono hMM' i

/-- Locality: `I_1^{(M)}(𝐱)` only depends on `x_1, …, x_M`. -/
theorem firstMarked_take_iff {M : ℕ} : FirstMarked G M (x.take M) ↔ FirstMarked G M x := by
  constructor
  · rintro ⟨m, hz, hm, T, hT, hG⟩
    obtain ⟨hz', hmM⟩ := zeta_take_eq_some_iff.mp hz
    exact ⟨m, hz', hm, T, by rwa [← ofSeq_take_of_zeta_eq hz' hmM], hG⟩
  · rintro ⟨m, hz, hm, T, hT, hG⟩
    have hmM : m ≤ M := by exact_mod_cast hm
    exact ⟨m, zeta_take_eq_some_iff.mpr ⟨hz, hmM⟩, hm, T,
      by rwa [ofSeq_take_of_zeta_eq hz hmM], hG⟩

theorem firstIndicator_take (G : PlaneTree → Prop) (M : ℕ) (x : List ℤ) :
    firstIndicator G M (x.take M) = firstIndicator G M x := by
  classical
  unfold firstIndicator
  simp only [firstMarked_take_iff]

/-- Locality: two sequences with the same first `M` entries have the same `I_1^{(M)}`. -/
theorem firstIndicator_congr_take {M : ℕ} (h : x.take M = y.take M) :
    firstIndicator G M x = firstIndicator G M y := by
  rw [← firstIndicator_take, h, firstIndicator_take]

/-- With the infinite cutoff, `I_1^{(∞)}(𝐱) = G(T(𝐱))` (and `0` if `ζ(𝐱) = ∞`). -/
theorem firstMarked_top_iff : FirstMarked G ⊤ x ↔ ∃ T, ofSeq x = some T ∧ G T := by
  rw [firstMarked_iff]
  simp

theorem firstIndicator_top (G : PlaneTree → Prop) (x : List ℤ) [Decidable (∃ T, ofSeq x = some T ∧
  G T)] :
    firstIndicator G ⊤ x = if ∃ T, ofSeq x = some T ∧ G T then 1 else 0 := by
  split_ifs with h
  · exact firstIndicator_eq_one_iff.mpr (firstMarked_top_iff.mpr h)
  · exact firstIndicator_eq_zero_iff.mpr fun h' => h (firstMarked_top_iff.mp h')

/-- A cutoff at least the length of the sequence is no cutoff. -/
theorem firstMarked_iff_top_of_length_le (h : (x.length : ℕ∞) ≤ M) :
    FirstMarked G M x ↔ FirstMarked G ⊤ x := by
  refine ⟨fun h' => h'.mono le_top, ?_⟩
  rintro ⟨m, hz, -, hT⟩
  have hm := (zeta_eq_some_iff.mp hz).2.1
  exact ⟨m, hz, le_trans (by exact_mod_cast hm) h, hT⟩

theorem firstIndicator_of_length_le (h : (x.length : ℕ∞) ≤ M) :
    firstIndicator G M x = firstIndicator G ⊤ x := by
  classical
  unfold firstIndicator
  simp only [firstMarked_iff_top_of_length_le h]

/-! ### Cyclic shifts of a DFS sequence -/

/-- The `i`-th cyclic indicator of `𝐱(T)` tests the fringe subtree at the `i`-th vertex
(`eq:fringe`). -/
theorem shiftIndicator_dfsSeq_eq_one_iff (G : PlaneTree → Prop) (M : ℕ∞) (T : PlaneTree) (i : ℕ)
    (hi : i < T.vertexCount) :
    shiftIndicator G M T.dfsSeq i = 1 ↔
      ((T.fringeTrees[i]'(lt_length_fringeTrees hi)).vertexCount : ℕ∞) ≤ M ∧
        G (T.fringeTrees[i]'(lt_length_fringeTrees hi)) := by
  unfold shiftIndicator
  rw [firstIndicator_eq_one_iff, firstMarked_iff]
  constructor
  · rintro ⟨U, hU, hUM, hG⟩
    rw [ofSeq_rotate_dfsSeq T i hi, Option.some.injEq] at hU
    exact hU ▸ ⟨hUM, hG⟩
  · intro h
    exact ⟨_, ofSeq_rotate_dfsSeq T i hi, h⟩

theorem countP_eq_sum_range {α : Type*} (p : α → Bool) :
    ∀ l : List α, l.countP p =
      ∑ i ∈ Finset.range l.length, if h : i < l.length then (if p l[i] then 1 else 0) else 0
  | [] => by simp
  | a :: l => by
    rw [List.countP_cons, countP_eq_sum_range p l]
    change _ = ∑ i ∈ Finset.range (l.length + 1),
      if h : i < l.length + 1 then (if p ((a :: l)[i]'h) then 1 else 0) else 0
    rw [Finset.sum_range_succ']
    simp only [Nat.add_lt_add_iff_right, List.getElem_cons_succ, Nat.zero_lt_succ,
      ↓reduceDIte, List.getElem_cons_zero]

/-- The counting identity of Section 2.3: `∑_{i=1}^{n} I_i^{(M)}(𝐱(T))` is the number of
vertices `v` of `T` whose fringe subtree `T_v` has at most `M` vertices and is marked. -/
theorem cyclicSum_dfsSeq (G : PlaneTree → Prop) (M : ℕ∞) (T : PlaneTree) :
    cyclicSum G M T.dfsSeq = markCount (fun U => (U.vertexCount : ℕ∞) ≤ M ∧ G U) T := by
  classical
  unfold cyclicSum markCount
  rw [length_dfsSeq, countP_eq_sum_range]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < T.vertexCount := Finset.mem_range.mp hi
  have hi'' : i < T.fringeTrees.length := hi'
  simp only [hi'', ↓reduceDIte]
  split_ifs with h
  · simp only [decide_eq_true_eq] at h
    exact (shiftIndicator_dfsSeq_eq_one_iff G M T i hi').mpr h
  · simp only [decide_eq_true_eq] at h
    rcases shiftIndicator_eq_zero_or_eq_one G M T.dfsSeq i with h' | h'
    · exact h'
    · exact absurd ((shiftIndicator_dfsSeq_eq_one_iff G M T i hi').mp h') h

/-- With a cutoff `M ≥ |T|`, the cyclic sum counts all marked vertices (`markCount G T`). -/
theorem cyclicSum_dfsSeq_of_le (G : PlaneTree → Prop) {M : ℕ∞} {T : PlaneTree}
    (hM : (T.vertexCount : ℕ∞) ≤ M) : cyclicSum G M T.dfsSeq = markCount G T := by
  classical
  rw [cyclicSum_dfsSeq]
  unfold markCount
  refine List.countP_congr fun U hU => ?_
  simp only [decide_eq_true_eq, and_iff_right_iff_imp]
  exact fun _ => le_trans (by exact_mod_cast vertexCount_le_of_mem_fringeTrees hU) hM

theorem cyclicSum_dfsSeq_top (G : PlaneTree → Prop) (T : PlaneTree) :
    cyclicSum G ⊤ T.dfsSeq = markCount G T :=
  cyclicSum_dfsSeq_of_le G le_top

/-- The cyclic sum is invariant under one rotation. -/
theorem cyclicSum_rotate_one (G : PlaneTree → Prop) (M : ℕ∞) (x : List ℤ) :
    cyclicSum G M (x.rotate 1) = cyclicSum G M x := by
  unfold cyclicSum shiftIndicator
  rw [List.length_rotate]
  simp_rw [List.rotate_rotate]
  have h1 := Finset.sum_range_succ' (fun i => firstIndicator G M (x.rotate i)) x.length
  have h2 := Finset.sum_range_succ (fun i => firstIndicator G M (x.rotate i)) x.length
  rw [List.rotate_length] at h2
  simp only [List.rotate_zero] at h1
  simp_rw [add_comm 1]
  omega

/-- `B04`: the sum of the cyclic indicators is invariant under cyclic shifts. -/
theorem cyclicSum_rotate (G : PlaneTree → Prop) (M : ℕ∞) (x : List ℤ) (k : ℕ) :
    cyclicSum G M (x.rotate k) = cyclicSum G M x := by
  induction k with
  | zero => rw [List.rotate_zero]
  | succ k ih => rw [← List.rotate_rotate, cyclicSum_rotate_one, ih]

/-- The cyclic sum of a vector `(x_1, …, x_n)`, as a sum over `Fin n`. -/
theorem cyclicSum_ofFn {n : ℕ} (G : PlaneTree → Prop) (M : ℕ∞) (ω : Fin n → ℤ) :
    cyclicSum G M (List.ofFn ω) = ∑ i : Fin n, shiftIndicator G M (List.ofFn ω) i := by
  rw [cyclicSum, List.length_ofFn, Finset.sum_range]

end Cyclic

end PoissonDeclumping
