/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/

module

public import LeanPool.RareSubtreePatterns.PlaneTree.Countable
public import LeanPool.RareSubtreePatterns.Lukasiewicz.FirstPassage


/-!
# The Łukasiewicz coding of plane trees

Section 2.1 of the paper (source lines 683–696) and Section 2.3 (source lines 735–736).

* `PlaneTree.dfsSeq T` is the DFS sequence `𝐱(T) = (k_{u_1}(T) - 1, …, k_{u_n}(T) - 1)`.
* Its partial sums are nonnegative before time `n = |T|` and equal `-1` at time `n`, so
  `ζ(𝐱(T) ++ 𝐲) = |T|` for every continuation `𝐲` (`zeta_dfsSeq_append`).
* The coding is injective and even prefix-free (`dfsSeq_append_inj`), and its range is exactly
  the set of sequences with increments `≥ -1` whose first passage time to `-1` is their length
  (`mem_range_dfsSeq_iff`).
* `PlaneTree.ofSeq 𝐱` is the paper's `T(𝐱)`: the tree whose DFS sequence is
  `(x_1, …, x_{ζ(𝐱)})`.
* `eq:fringe`: the `i`-th cyclic shift of `𝐱(T)`, stopped at its first passage time to `-1`,
  is the DFS sequence of the fringe subtree at the `i`-th vertex (`ofSeq_rotate_dfsSeq`).

Forests (lists of trees) are coded by concatenation (`PlaneTree.forestSeq`); a forest of `k`
trees corresponds to a sequence with first passage to `-k` at its end.
-/

@[expose] public section

namespace PoissonDeclumping.PlaneTree

open Lukasiewicz

/-- The DFS sequence `𝐱(T) = (k_{u_1}(T) - 1, …, k_{u_n}(T) - 1)` of a plane tree. -/
def dfsSeq (T : PlaneTree) : List ℤ := T.degSeq.map fun d : ℕ => (d : ℤ) - 1

/-- The DFS sequence of a forest: the concatenation of the DFS sequences of its trees. -/
def forestSeq (ts : List PlaneTree) : List ℤ := ts.flatMap dfsSeq

@[simp] theorem forestSeq_nil : forestSeq [] = [] := rfl

@[simp] theorem forestSeq_cons (t : PlaneTree) (ts : List PlaneTree) :
    forestSeq (t :: ts) = t.dfsSeq ++ forestSeq ts := by
  simp [forestSeq]

theorem forestSeq_append (ts us : List PlaneTree) :
    forestSeq (ts ++ us) = forestSeq ts ++ forestSeq us := by
  simp [forestSeq]

theorem dfsSeq_node (ts : List PlaneTree) :
    (node ts).dfsSeq = ((ts.length : ℤ) - 1) :: forestSeq ts := by
  simp only [dfsSeq, degSeq_node, List.map_cons, List.map_flatMap, forestSeq]
  rfl

theorem length_dfsSeq (T : PlaneTree) : T.dfsSeq.length = T.vertexCount := by
  simp [dfsSeq, length_degSeq]

theorem one_le_vertexCount (T : PlaneTree) : 1 ≤ T.vertexCount := by
  cases T with
  | node ts => simp [vertexCount]

/-- Every entry of a DFS sequence is at least `-1`. -/
theorem neg_one_le_of_mem_dfsSeq {T : PlaneTree} {a : ℤ} (ha : a ∈ T.dfsSeq) : -1 ≤ a := by
  simp only [dfsSeq, List.mem_map] at ha
  obtain ⟨d, -, rfl⟩ := ha
  have h0 : (0 : ℤ) ≤ d := Int.natCast_nonneg d
  linarith

/-- Excursion property of forests, given the excursion property of every tree. -/
theorem forestSeq_excursion {ts : List PlaneTree}
    (h : ∀ t ∈ ts, t.dfsSeq.sum = -1 ∧ ∀ j < t.dfsSeq.length, 0 ≤ (t.dfsSeq.take j).sum) :
    (forestSeq ts).sum = -(ts.length : ℤ) ∧
      ∀ j < (forestSeq ts).length, -(ts.length : ℤ) < ((forestSeq ts).take j).sum := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    obtain ⟨hs, hp⟩ := ih (fun u hu => h u (by simp [hu]))
    obtain ⟨hts, htp⟩ := h t (by simp)
    simp only [forestSeq_cons, List.sum_append, List.length_cons, hs, hts, List.length_append]
    refine ⟨by push_cast; omega, fun j hj => ?_⟩
    rw [List.take_append, List.sum_append]
    rcases lt_or_ge j t.dfsSeq.length with hjt | hjt
    · have h1 := htp j hjt
      rw [Nat.sub_eq_zero_of_le hjt.le]
      simp only [List.take_zero, List.sum_nil]
      push_cast
      linarith
    · rw [List.take_of_length_le hjt, hts]
      have h2 := hp (j - t.dfsSeq.length) (by omega)
      push_cast
      linarith

/-- **Łukasiewicz excursion property.** The DFS sequence of a tree sums to `-1`, and all its
proper partial sums are nonnegative. -/
theorem dfsSeq_excursion (T : PlaneTree) :
    T.dfsSeq.sum = -1 ∧ ∀ j < T.dfsSeq.length, 0 ≤ (T.dfsSeq.take j).sum := by
  induction T using induction_children with
  | step T ih =>
    cases T with
    | node ts =>
      obtain ⟨hs, hp⟩ := forestSeq_excursion (ts := ts) (fun t ht => ih t (by simpa using ht))
      rw [dfsSeq_node]
      refine ⟨by rw [List.sum_cons, hs]; omega, fun j hj => ?_⟩
      cases j with
      | zero => simp
      | succ j =>
        simp only [List.take_succ_cons, List.sum_cons]
        have := hp j (by simpa using hj)
        linarith

theorem sum_dfsSeq (T : PlaneTree) : T.dfsSeq.sum = -1 := (dfsSeq_excursion T).1

/-- All proper partial sums of a DFS sequence are nonnegative (before `ζ`). -/
theorem sum_take_dfsSeq_nonneg (T : PlaneTree) {j : ℕ} (hj : j < T.vertexCount) :
    0 ≤ (T.dfsSeq.take j).sum :=
  (dfsSeq_excursion T).2 j (by rwa [length_dfsSeq])

theorem sum_forestSeq (ts : List PlaneTree) : (forestSeq ts).sum = -(ts.length : ℤ) :=
  (forestSeq_excursion fun t _ => dfsSeq_excursion t).1

/-- **Łukasiewicz coding (`B02`).** For every tree `T` and every continuation `𝐲`,
`ζ(𝐱(T) 𝐲) = |T|`. -/
theorem zeta_dfsSeq_append (T : PlaneTree) (y : List ℤ) :
    zeta (T.dfsSeq ++ y) = some T.vertexCount := by
  rw [zeta_eq_some_iff]
  have hl := length_dfsSeq T
  refine ⟨one_le_vertexCount T, by simp [hl], ?_, fun j _ hj => ?_⟩
  · rw [List.take_left' hl, sum_dfsSeq]
  · rw [List.take_append_of_le_length (by omega)]
    have := sum_take_dfsSeq_nonneg T hj
    omega

theorem zeta_dfsSeq (T : PlaneTree) : zeta T.dfsSeq = some T.vertexCount := by
  simpa using zeta_dfsSeq_append T []

private theorem forestSeq_append_inj {ts us : List PlaneTree}
    (ih : ∀ t ∈ ts, ∀ (U : PlaneTree) (y z : List ℤ), t.dfsSeq ++ y = U.dfsSeq ++ z →
      t = U ∧ y = z)
    (hl : ts.length = us.length) {y z : List ℤ} (h : forestSeq ts ++ y = forestSeq us ++ z) :
    ts = us ∧ y = z := by
  induction ts generalizing us with
  | nil =>
    cases us with
    | nil => simpa using h
    | cons u us => simp at hl
  | cons t ts ihl =>
    cases us with
    | nil => simp at hl
    | cons u us =>
      simp only [forestSeq_cons, List.append_assoc] at h
      obtain ⟨rfl, h'⟩ := ih t (by simp) u _ _ h
      obtain ⟨rfl, rfl⟩ := ihl (fun v hv => ih v (by simp [hv])) (by simpa using hl) h'
      exact ⟨rfl, rfl⟩

/-- The coding is prefix-free: a DFS sequence determines its tree even when followed by an
arbitrary continuation. -/
theorem dfsSeq_append_inj {T U : PlaneTree} {y z : List ℤ}
    (h : T.dfsSeq ++ y = U.dfsSeq ++ z) : T = U ∧ y = z := by
  induction T using induction_children generalizing U y z with
  | step T ih =>
    cases T with
    | node ts =>
      cases U with
      | node us =>
        simp only [dfsSeq_node, List.cons_append, List.cons.injEq] at h
        obtain ⟨hl, h⟩ := h
        have hl' : ts.length = us.length := by omega
        obtain ⟨rfl, rfl⟩ :=
          forestSeq_append_inj (fun t ht U y z h => ih t (by simpa using ht) h) hl' h
        exact ⟨rfl, rfl⟩

/-- The DFS sequence determines the tree. -/
theorem dfsSeq_injective : Function.Injective dfsSeq := fun T U h =>
  (dfsSeq_append_inj (y := []) (z := []) (by simpa using h)).1

/-- The outdegree sequence in DFS order determines the tree. -/
theorem degSeq_injective : Function.Injective degSeq := fun T U h =>
  dfsSeq_injective (by simp only [dfsSeq, h])

/-- Every sequence with increments `≥ -1` and first passage to `-k` exactly at its end is the
DFS sequence of a forest of `k` trees. -/
theorem exists_forestSeq_eq (x : List ℤ) (hx : ∀ a ∈ x, -1 ≤ a) (k : ℕ)
    (hs : x.sum = -(k : ℤ)) (hp : ∀ j < x.length, -(k : ℤ) < (x.take j).sum) :
    ∃ ts : List PlaneTree, ts.length = k ∧ forestSeq ts = x := by
  induction x generalizing k with
  | nil =>
    simp only [List.sum_nil] at hs
    exact ⟨[], by simp; omega, rfl⟩
  | cons a x ih =>
    have ha : -1 ≤ a := hx a (by simp)
    have hk : 1 ≤ k := by
      have := hp 0 (by simp)
      simp only [List.take_zero, List.sum_nil] at this
      omega
    obtain ⟨c, hc⟩ : ∃ c : ℕ, (c : ℤ) = a + 1 := ⟨(a + 1).toNat, by omega⟩
    simp only [List.sum_cons] at hs
    obtain ⟨ts, hlen, hts⟩ := ih (fun b hb => hx b (by simp [hb])) (k - 1 + c)
      (by push_cast [hk]; omega)
      (fun j hj => by
        have := hp (j + 1) (by simpa using hj)
        simp only [List.take_succ_cons, List.sum_cons] at this
        push_cast [hk]
        omega)
    refine ⟨node (ts.take c) :: ts.drop c, ?_, ?_⟩
    · simp only [List.length_cons, List.length_drop, hlen]
      omega
    · rw [forestSeq_cons, dfsSeq_node, List.cons_append, ← forestSeq_append,
        List.take_append_drop, hts, List.length_take, min_eq_left (by omega)]
      congr 1
      omega

/-- **Łukasiewicz coding, surjectivity (`B02`).** If `𝐱` has increments `≥ -1` and
`ζ(𝐱) = m < ∞`, then `(x_1, …, x_m)` is the DFS sequence of a tree (with `m` vertices). -/
theorem exists_dfsSeq_eq_take {x : List ℤ} (hx : ∀ a ∈ x, -1 ≤ a) {m : ℕ}
    (hz : zeta x = some m) : ∃ T : PlaneTree, T.dfsSeq = x.take m ∧ T.vertexCount = m := by
  obtain ⟨h1, h2, h3, h4⟩ := zeta_eq_some_iff.mp hz
  have hnn := sum_take_nonneg_of_ne hx h4
  have hlen : (x.take m).length = m := by simp [h2]
  obtain ⟨ts, hl, hts⟩ := exists_forestSeq_eq (x.take m)
    (fun a ha => hx a (List.mem_of_mem_take ha)) 1 (by simpa using h3) (fun j hj => by
      rw [List.take_take, min_eq_left (by omega)]
      have := hnn j (by omega)
      push_cast
      omega)
  match ts, hl with
  | [T], _ =>
    simp only [forestSeq_cons, forestSeq_nil, List.append_nil] at hts
    exact ⟨T, hts, by rw [← length_dfsSeq, hts, hlen]⟩

/-- The paper's `T(𝐱)`: the tree whose DFS sequence is `(x_1, …, x_{ζ(𝐱)})`, if `ζ(𝐱) < ∞`
and this prefix is a DFS sequence (which holds whenever all increments are `≥ -1`), and `none`
otherwise. -/
noncomputable def ofSeq (x : List ℤ) : Option PlaneTree := by
  classical
  exact if h : ∃ T : PlaneTree, ∃ m, zeta x = some m ∧ T.dfsSeq = x.take m
    then some h.choose else none

/-- Characterization of `T(𝐱)`. -/
theorem ofSeq_eq_some_iff {x : List ℤ} {T : PlaneTree} :
    ofSeq x = some T ↔ ∃ m, zeta x = some m ∧ T.dfsSeq = x.take m := by
  classical
  unfold ofSeq
  split_ifs with h
  · rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact h.choose_spec
    · rintro ⟨m, hm, hT⟩
      obtain ⟨m', hm', hT'⟩ := h.choose_spec
      rw [hm, Option.some.injEq] at hm'
      subst hm'
      exact dfsSeq_injective (hT'.trans hT.symm)
  · simp only [false_iff]
    intro h'
    exact h ⟨T, h'⟩

/-- `T(𝐱(T) 𝐲) = T` for every continuation `𝐲`. -/
theorem ofSeq_dfsSeq_append (T : PlaneTree) (y : List ℤ) : ofSeq (T.dfsSeq ++ y) = some T :=
  ofSeq_eq_some_iff.mpr ⟨T.vertexCount, zeta_dfsSeq_append T y,
    (List.take_left' (length_dfsSeq T)).symm⟩

theorem ofSeq_dfsSeq (T : PlaneTree) : ofSeq T.dfsSeq = some T := by
  simpa using ofSeq_dfsSeq_append T []

/-- If `𝐱` has increments `≥ -1` and `ζ(𝐱) = m < ∞`, then `T(𝐱)` is defined, has `m` vertices,
and its DFS sequence is `(x_1, …, x_m)`. -/
theorem exists_ofSeq_eq_some {x : List ℤ} (hx : ∀ a ∈ x, -1 ≤ a) {m : ℕ}
    (hz : zeta x = some m) :
    ∃ T : PlaneTree, ofSeq x = some T ∧ T.dfsSeq = x.take m ∧ T.vertexCount = m := by
  obtain ⟨T, hT, hn⟩ := exists_dfsSeq_eq_take hx hz
  exact ⟨T, ofSeq_eq_some_iff.mpr ⟨m, hz, hT⟩, hT, hn⟩

/-- For sequences with increments `≥ -1`, `T(𝐱)` is defined exactly when `ζ(𝐱) < ∞`. -/
theorem isSome_ofSeq_iff {x : List ℤ} (hx : ∀ a ∈ x, -1 ≤ a) :
    (ofSeq x).isSome ↔ (zeta x).isSome := by
  constructor
  · intro h
    obtain ⟨T, hT⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨m, hm, -⟩ := ofSeq_eq_some_iff.mp hT
    simp [hm]
  · intro h
    obtain ⟨m, hm⟩ := Option.isSome_iff_exists.mp h
    obtain ⟨T, hT, -⟩ := exists_ofSeq_eq_some hx hm
    simp [hT]

/-- The range of the coding: a finite sequence is a DFS sequence iff its increments are `≥ -1`
and its first passage time to `-1` is its length. -/
theorem mem_range_dfsSeq_iff {x : List ℤ} :
    x ∈ Set.range dfsSeq ↔ (∀ a ∈ x, -1 ≤ a) ∧ zeta x = some x.length := by
  constructor
  · rintro ⟨T, rfl⟩
    exact ⟨fun a ha => neg_one_le_of_mem_dfsSeq ha, by rw [zeta_dfsSeq, length_dfsSeq]⟩
  · rintro ⟨hx, hz⟩
    obtain ⟨T, hT, -⟩ := exists_dfsSeq_eq_take hx hz
    exact ⟨T, by rw [hT, List.take_length]⟩

/-! ### Fringe subtrees and cyclic shifts (`eq:fringe`) -/

private theorem forest_fringe_prefix {ts : List PlaneTree}
    (ih : ∀ t ∈ ts, ∀ (i : ℕ) (hi : i < t.fringeTrees.length),
      (t.fringeTrees[i]).dfsSeq <+: t.dfsSeq.drop i)
    (i : ℕ) (hi : i < (ts.flatMap fringeTrees).length) :
    ((ts.flatMap fringeTrees)[i]).dfsSeq <+: (forestSeq ts).drop i := by
  induction ts generalizing i with
  | nil => simp at hi
  | cons t ts ihl =>
    have hlt : t.dfsSeq.length = t.fringeTrees.length := length_dfsSeq t
    simp only [List.flatMap_cons, forestSeq_cons] at hi ⊢
    rcases lt_or_ge i t.fringeTrees.length with hit | hit
    · rw [List.getElem_append_left hit, List.drop_append_of_le_length (by omega)]
      exact (ih t (by simp) i hit).trans (List.prefix_append _ _)
    · rw [List.getElem_append_right hit, List.drop_append, List.drop_eq_nil_of_le (by omega),
        List.nil_append, hlt]
      exact ihl (fun u hu => ih u (by simp [hu])) _ _

/-- The DFS sequence of the fringe subtree at the `i`-th vertex (in DFS order, `0`-indexed) is a
contiguous block of `𝐱(T)` starting at position `i`. -/
theorem dfsSeq_fringeTrees_prefix (T : PlaneTree) (i : ℕ) (hi : i < T.fringeTrees.length) :
    (T.fringeTrees[i]).dfsSeq <+: T.dfsSeq.drop i := by
  induction T using induction_children generalizing i with
  | step T ih =>
    cases T with
    | node ts =>
      cases i with
      | zero => simp
      | succ i =>
        simp only [fringeTrees_node, List.getElem_cons_succ, dfsSeq_node, List.drop_succ_cons]
        simp only [fringeTrees_node, List.length_cons] at hi
        exact forest_fringe_prefix (fun t ht => ih t (by simpa using ht)) i (by omega)

/-- Index bound transfer: `|T|` is the length of the list of fringe trees. -/
theorem lt_length_fringeTrees {T : PlaneTree} {i : ℕ} (hi : i < T.vertexCount) :
    i < T.fringeTrees.length := hi

/-- The `i`-th cyclic shift of `𝐱(T)` starts with the DFS sequence of the fringe subtree at the
`i`-th vertex. -/
theorem exists_rotate_dfsSeq_eq (T : PlaneTree) (i : ℕ) (hi : i < T.vertexCount) :
    ∃ y : List ℤ,
      T.dfsSeq.rotate i = (T.fringeTrees[i]'(lt_length_fringeTrees hi)).dfsSeq ++ y := by
  obtain ⟨y, hy⟩ := dfsSeq_fringeTrees_prefix T i (lt_length_fringeTrees hi)
  refine ⟨y ++ T.dfsSeq.take i, ?_⟩
  rw [List.rotate_eq_drop_append_take (by rw [length_dfsSeq]; exact hi.le), ← hy,
    List.append_assoc]

/-- **`eq:fringe`.** The `i`-th cyclic shift of `𝐱(T)` first hits `-1` at the size of the
fringe subtree `T_{u_i}` at the `i`-th vertex. -/
theorem zeta_rotate_dfsSeq (T : PlaneTree) (i : ℕ) (hi : i < T.vertexCount) :
    zeta (T.dfsSeq.rotate i) = some (T.fringeTrees[i]'(lt_length_fringeTrees hi)).vertexCount := by
  obtain ⟨y, hy⟩ := exists_rotate_dfsSeq_eq T i hi
  rw [hy, zeta_dfsSeq_append]

/-- **`eq:fringe`.** The `i`-th cyclic shift of `𝐱(T)`, up to its first passage time to `-1`, is
the DFS sequence of the fringe subtree `T_{u_i}`. -/
theorem take_rotate_dfsSeq (T : PlaneTree) (i : ℕ) (hi : i < T.vertexCount) :
    (T.dfsSeq.rotate i).take (T.fringeTrees[i]'(lt_length_fringeTrees hi)).vertexCount =
      (T.fringeTrees[i]'(lt_length_fringeTrees hi)).dfsSeq := by
  obtain ⟨y, hy⟩ := exists_rotate_dfsSeq_eq T i hi
  rw [hy, List.take_left' (length_dfsSeq _)]

/-- **`eq:fringe`.** `T(𝐱^{(i)}(T)) = T_{u_i}`. -/
theorem ofSeq_rotate_dfsSeq (T : PlaneTree) (i : ℕ) (hi : i < T.vertexCount) :
    ofSeq (T.dfsSeq.rotate i) = some (T.fringeTrees[i]'(lt_length_fringeTrees hi)) := by
  obtain ⟨y, hy⟩ := exists_rotate_dfsSeq_eq T i hi
  rw [hy, ofSeq_dfsSeq_append]

end PoissonDeclumping.PlaneTree
