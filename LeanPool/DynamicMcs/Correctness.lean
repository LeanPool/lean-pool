/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import Mathlib.Order.Interval.Finset.Nat
public import LeanPool.DynamicMcs.EdgeUpdate

/-!
# Correctness and locality of the dynamic updates (on the `Challenge` definitions)

* correctness of `initOrder`, `insertUpdate`, `deleteUpdate`, `greedySuffix`;
* uniqueness of the canonical MCS ordering, hence: each update returns exactly
  the from-scratch canonical ordering of the new graph;
* locality: after a flip of `{u, v}`, positions up to `earlierPos` and after
  `laterPos` stay legal; after a deletion, positions strictly between the
  endpoints stay legal too, so only `laterPos` can break;
* null updates: the ordering is returned unchanged exactly when it is still
  the canonical ordering of the new graph.
-/

@[expose] public section

noncomputable section

namespace DynamicMcs
namespace Proofs

open UGraph

variable {n : ℕ} {G G' : UGraph n}

theorem IsMCSNext.toAny {S : Finset (Vert n)} {w : Vert n} (h : IsMCSNext G S w) :
    IsMCSNextAny G S w :=
  ⟨h.1, h.2.1⟩

theorem IsMCSOrdering.toAny {order : List (Vert n)} (h : IsMCSOrdering G order) :
    IsMCSOrderingAny G order :=
  ⟨h.1, h.2.1, fun i hi => IsMCSNext.toAny (h.2.2 i hi)⟩

/-! ## Correctness -/

theorem init_valid (G : UGraph n) : IsMCSOrdering G (initOrder G) :=
  UGraph.init_valid G

theorem order_toFinset_univ {order : List (Vert n)} (h : IsMCSOrdering G order) :
    order.toFinset = (Finset.univ : Finset (Vert n)) :=
  Greedy.Update.order_toFinset_univ order h

theorem greedySuffix_full (H : UGraph n) (order : List (Vert n))
    (h : order.toFinset = (Finset.univ : Finset (Vert n))) :
    greedySuffix H order = order :=
  Greedy.Update.greedySuffix_full H order h

theorem update_from_prefix (order : List (Vert n)) (k : ℕ)
    (hvalid : IsMCSOrdering G order)
    (hsteps : ∀ i (hi : i < order.length), i < k →
      IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩)) :
    IsMCSOrdering G' (greedySuffix G' (order.take k)) :=
  Greedy.Update.update_from_prefix order k hvalid hsteps

/-- The insertion update is correct for every flip of `{u, v}` (the proof does
not need the edge to be absent before). -/
theorem insert_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (insertUpdate G' order u v) :=
  Greedy.Update.insert_update_valid u v order hflip hvalid

theorem delete_update_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (deleteUpdate G' order u v) :=
  Greedy.Update.delete_update_valid u v order hflip hdel hdel' hvalid

/-! ## Each update returns exactly the from-scratch canonical ordering -/

theorem insert_update_eq_initOrder (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    insertUpdate G' order u v = initOrder G' :=
  IsMCSOrdering_unique (insert_update_valid u v order hflip hvalid) (init_valid G')

theorem delete_update_eq_initOrder (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    deleteUpdate G' order u v = initOrder G' :=
  IsMCSOrdering_unique (delete_update_valid u v order hflip hdel hdel' hvalid) (init_valid G')

/-! ## Locality -/

/-- Positions up to the earlier endpoint stay legal after any flip. -/
theorem legal_upto_earlierPos (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length) (hle : i ≤ earlierPos order u v) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) :=
  UGraph.prefix_preserved order u v hflip hvalid i hle hi

/-- Positions after the later endpoint stay legal after any flip. -/
theorem legal_after_laterPos (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length) (hgt : laterPos order u v < i) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) :=
  Greedy.Update.legal_after_laterPos order u v hflip hvalid i hi hgt

/-- After a deletion, positions strictly between the endpoints stay legal. -/
theorem delete_legal_between (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi : i < order.length)
    (hgt : earlierPos order u v < i) (hlt : i < laterPos order u v) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) :=
  Greedy.Update.legal_middle_delete order u v hflip hdel hdel' hvalid i hi hgt hlt

/-- Inside the insertion window, the old choice breaks exactly when the later
endpoint now beats it: strictly larger cardinality, or equal cardinality and a
smaller index. -/
theorem insert_break_iff (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (k : ℕ) (hk : k < order.length)
    (hgt : earlierPos order u v < k) (hle : k ≤ laterPos order u v) :
    ¬ IsMCSNext G' (order.take k).toFinset (order.get ⟨k, hk⟩) ↔
      G'.neigh (order.take k).toFinset (laterVert order u v) >
          G'.neigh (order.take k).toFinset (order.get ⟨k, hk⟩) ∨
        (G'.neigh (order.take k).toFinset (laterVert order u v) =
            G'.neigh (order.take k).toFinset (order.get ⟨k, hk⟩) ∧
          laterVert order u v < order.get ⟨k, hk⟩) :=
  Greedy.Update.insert_break_iff order u v hflip hins hins' hvalid k hk hgt hle

/-! ## Insertion window: the later endpoint is never a break

For an insertion flip, at the exact position `laterPos` the probe examines the
later endpoint itself as the old choice; that choice is always legal on the
post-insertion graph.  Hence the window can be shrunk by one at the right end,
and strictly inside the open window the break test is the *old-graph* comparison
of the later endpoint against the old choice. -/

/-- A valid MCS ordering contains every vertex. -/
lemma mem_of_IsMCSOrdering (order : List (Vert n)) (hvalid : IsMCSOrdering G order) :
    ∀ z : Vert n, z ∈ order :=
  UGraph.mem_of_IsMCSOrdering order hvalid

/-- The earlier position is strictly below the later position. -/
lemma earlierPos_lt_laterPos (order : List (Vert n)) (u v : Vert n)
    (huv : u ≠ v) (hmu : u ∈ order) (hmv : v ∈ order) :
    earlierPos order u v < laterPos order u v :=
  Greedy.Update.earlierPos_lt_laterPos order u v huv hmu hmv

/-- Inserting the edge increases the later endpoint’s count by one. -/
lemma neigh_flip_insert (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (s : Finset (Vert n)) (a w : Vert n) (ha : a ∈ s) (hw : w ∉ s)
    (haw : a ≠ w) (hae : a = u ∨ a = v) (hwe : w = u ∨ w = v) :
    (∀ x ∈ s, G'.neigh s x = G.neigh s x) ∧
      G'.neigh s w = G.neigh s w + 1 ∧
      (∀ y, y ∉ s → y ≠ w → G'.neigh s y = G.neigh s y) :=
  Greedy.Update.neigh_flip_insert hflip hins hins' s a w ha hw haw hae hwe

/-- Arithmetic normalization of the insertion break condition, using that the
old choice is a maximum (its cardinality `c` is at least the later endpoint's
`d` on the old graph). -/
lemma neigh_arith (d c : ℕ) (w x : Vert n) (hle : d ≤ c) :
    (d + 1 > c ∨ ((d + 1 = c) ∧ w < x)) ↔
      (d = c ∨ ((d = c - 1) ∧ w < x)) := by
  constructor
  · rintro (h1 | ⟨h2, hp⟩)
    · have : d = c := by omega
      exact Or.inl this
    · have h3 : d = c - 1 := by omega
      exact Or.inr ⟨h3, hp⟩
  · rintro (h1 | ⟨h2, hp⟩)
    · have h3 : d + 1 > c := by omega
      exact Or.inl h3
    · by_cases hc : c = 0
      · have h3 : d + 1 > c := by omega
        exact Or.inl h3
      · have h3 : d + 1 = c := by omega
        exact Or.inr ⟨h3, hp⟩

/-- M5(i): for an insertion flip, the old pick at the exact position `laterPos`
is not a break on `G'`. -/
theorem no_break_at_laterPos (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (hk : laterPos order u v < order.length) :
    IsMCSNext G' (order.take (laterPos order u v)).toFinset
      (order.get ⟨laterPos order u v, hk⟩) := by
  classical
  have hmem : u ∈ order := mem_of_IsMCSOrdering order hvalid u
  have hmv : v ∈ order := mem_of_IsMCSOrdering order hvalid v
  have hget := Greedy.Update.laterVert_get order u v hk
  have hlt := earlierPos_lt_laterPos order u v hflip.1 hmem hmv
  have hiff := insert_break_iff u v order hflip hins hins' hvalid (laterPos order u v) hk hlt le_rfl
  rw [hget] at hiff
  simp only [lt_irrefl, and_false, or_false] at hiff
  rw [hget]
  by_contra hn
  exact hiff.mp hn

/-- Inside the insertion window, the old choice is invalid exactly when the later
endpoint previously tied it on the neighbor count, or trailed by one and has the
smaller index. -/
theorem insert_break_iff_old (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (hvalid : IsMCSOrdering G order)
    (k : ℕ) (hk : k < order.length)
    (hgt : earlierPos order u v < k) (hlt : k < laterPos order u v) :
    ¬ IsMCSNext G' (order.take k).toFinset (order.get ⟨k, hk⟩) ↔
      G.neigh (order.take k).toFinset (laterVert order u v) =
          G.neigh (order.take k).toFinset (order.get ⟨k, hk⟩) ∨
        (G.neigh (order.take k).toFinset (laterVert order u v) =
            G.neigh (order.take k).toFinset (order.get ⟨k, hk⟩) - 1 ∧
          laterVert order u v < order.get ⟨k, hk⟩) := by
  classical
  let chosen := (order.take k).toFinset
  let x := order.get ⟨k, hk⟩
  let w := laterVert order u v
  let a := Greedy.Update.earlierVert order u v
  have huv := hflip.1
  have hnodup := hvalid.1
  have hmu : u ∈ order := mem_of_IsMCSOrdering order hvalid u
  have hmv : v ∈ order := mem_of_IsMCSOrdering order hvalid v
  have hwe : w = u ∨ w = v := by
    simp only [w]
    exact Greedy.Update.laterVert_eq order u v
  have hae : a = u ∨ a = v := Greedy.Update.earlierVert_eq order u v
  have haw : a ≠ w := by
    have h := Greedy.Update.earlier_ne_later order u v huv
    simp only [w]
    exact h
  have hw_mem : w ∈ order := by
    rcases hwe with h | h
    · rw [h]; exact hmu
    · rw [h]; exact hmv
  have ha_mem : a ∈ order := by
    rcases hae with h | h
    · rw [h]; exact hmu
    · rw [h]; exact hmv
  have hidx_a : List.idxOf a order = earlierPos order u v := by
    rw [Greedy.Update.idxOf_earlierVert]
  have hidx_w : List.idxOf w order = laterPos order u v := by
    simp only [w]
    rw [Greedy.Update.idxOf_laterVert]
  have haC : a ∈ chosen := by
    have hmem : a ∈ order.take k := by
      rw [List.mem_take_iff_idxOf_lt ha_mem, hidx_a]
      exact hgt
    exact List.mem_toFinset.mpr hmem
  have hwN : w ∉ chosen := by
    rw [List.mem_toFinset]
    intro hwmem
    have hwi : List.idxOf w order < k := (List.mem_take_iff_idxOf_lt hw_mem).mp hwmem
    rw [hidx_w] at hwi
    omega
  have hxN : x ∉ chosen := by
    rw [List.mem_toFinset]
    intro hxmem
    have hxi : List.idxOf x order < k :=
      (List.mem_take_iff_idxOf_lt (List.get_mem order ⟨k, hk⟩)).mp hxmem
    have hxpos : List.idxOf x order = k := List.get_idxOf hnodup ⟨k, hk⟩
    rw [hxpos] at hxi
    omega
  have hxU : x ∈ (Finset.univ : Finset (Vert n)) \ chosen :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxN⟩
  have hwU : w ∈ (Finset.univ : Finset (Vert n)) \ chosen :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ w, hwN⟩
  have hxw : x ≠ w := by
    intro hxw
    have hxpos : List.idxOf x order = k := List.get_idxOf hnodup ⟨k, hk⟩
    rw [hxw, hidx_w] at hxpos
    omega
  have hnextG : IsMCSNext G chosen x := hvalid.2.2 k hk
  have hxmax : ∀ y, y ∈ (Finset.univ : Finset (Vert n)) \ chosen →
      G.neigh chosen y ≤ G.neigh chosen x := hnextG.2.1
  have hAw := neigh_flip_insert hflip hins hins' chosen a w haC hwN haw hae hwe
  have hB : G'.neigh chosen w = G.neigh chosen w + 1 := hAw.2.1
  have hC := hAw.2.2
  have hxC_eq : G'.neigh chosen x = G.neigh chosen x := hC x hxN hxw
  have hbridge : ¬ IsMCSNext G' chosen x ↔
      (G'.neigh chosen w > G'.neigh chosen x ∨
        (G'.neigh chosen w = G'.neigh chosen x ∧ w < x)) := by
    have hle : k ≤ laterPos order u v := le_of_lt hlt
    have hiff := insert_break_iff u v order hflip hins hins' hvalid k hk hgt hle
    simpa only [chosen, x, w] using hiff
  rw [hbridge, hB, hxC_eq]
  exact neigh_arith (G.neigh chosen w) (G.neigh chosen x) w x (hxmax w hwU)

/-- The insertion probe can drop the right window bound by one: since the old
pick at the exact position `laterPos` is never a break, stopping the scan one
step earlier loses nothing. -/
theorem insert_window_open (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hins : ¬ G.adj u v) (hins' : G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    firstBreakWindow G' order (earlierPos order u v + 1) (laterPos order u v)
      = firstBreakWindow G' order (earlierPos order u v + 1) (laterPos order u v - 1) := by
  classical
  have hmem : u ∈ order := mem_of_IsMCSOrdering order hvalid u
  have hmv : v ∈ order := mem_of_IsMCSOrdering order hvalid v
  have hk : laterPos order u v < order.length := by
    unfold laterPos
    have h1 := List.idxOf_lt_length_of_mem hmem
    have h2 := List.idxOf_lt_length_of_mem hmv
    omega
  have hlegal_hk : IsMCSNext G' (order.take (laterPos order u v)).toFinset
      (order.get ⟨laterPos order u v, hk⟩) :=
    no_break_at_laterPos u v order hflip hins hins' hvalid hk
  rw [Greedy.Update.firstBreakWindow_eq_scan, Greedy.Update.firstBreakWindow_eq_scan]
  cases hs : firstBreak G' order (earlierPos order u v + 1) with
  | none => rfl
  | some j =>
      rcases (Greedy.Update.firstBreak_some G' order (earlierPos order u v + 1) j).mp hs with
        ⟨hjlen, _, hbad, _⟩
      have hjle : j ≤ laterPos order u v := by
        by_contra h
        have hgt : laterPos order u v < j := lt_of_not_ge h
        have hleg : IsMCSNext G' (order.take j).toFinset (order.get ⟨j, hjlen⟩) :=
          legal_after_laterPos u v order hflip hvalid j hjlen hgt
        exact hbad hleg
      have hjnlt : j ≠ laterPos order u v := by
        intro hjeq
        subst hjeq
        exact hbad hlegal_hk
      have hiff : (j ≤ laterPos order u v) ↔ (j ≤ laterPos order u v - 1) := by omega
      simp only [Option.filter, decide_eq_true_eq, hiff]

/-! ## Null updates -/

/-- The insertion update returns `order` unchanged exactly when `order` is
still the canonical MCS ordering of the new graph. -/
theorem insert_update_eq_self_iff (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    insertUpdate G' order u v = order ↔ IsMCSOrdering G' order := by
  constructor
  · intro h
    rw [← h]
    exact insert_update_valid u v order hflip hvalid
  · intro h'
    exact IsMCSOrdering_unique (insert_update_valid u v order hflip hvalid) h'

/-- The deletion update returns `order` unchanged exactly when `order` is
still the canonical MCS ordering of the new graph. -/
theorem delete_update_eq_self_iff (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hdel : G.adj u v) (hdel' : ¬ G'.adj u v)
    (hvalid : IsMCSOrdering G order) :
    deleteUpdate G' order u v = order ↔ IsMCSOrdering G' order := by
  constructor
  · intro h
    rw [← h]
    exact delete_update_valid u v order hflip hdel hdel' hvalid
  · intro h'
    exact IsMCSOrdering_unique (delete_update_valid u v order hflip hdel hdel' hvalid) h'

/-- If the window probe finds no break, the insertion update returns `order`
itself (no regreedy). -/
theorem insert_update_of_no_break (u v : Vert n) (order : List (Vert n))
    (hvalid : IsMCSOrdering G order)
    (h : firstBreakWindow G' order (earlierPos order u v + 1) (laterPos order u v) = none) :
    insertUpdate G' order u v = order := by
  simp only [insertUpdate, h, Option.getD_none, List.take_length]
  exact greedySuffix_full G' order (order_toFinset_univ hvalid)

/-- If the deletion probe does not fire, the deletion update returns `order`
itself (no regreedy). -/
theorem delete_update_of_no_break (u v : Vert n) (order : List (Vert n))
    (h : deletionBreaks G' order u v = false) :
    deleteUpdate G' order u v = order := by
  unfold deleteUpdate
  rw [h]
  rfl

end Proofs
end DynamicMcs

/-! ## The step-function probe lemma

`neigh_take_succ` is the structural fact behind the sublinear window probe:
the running count `c_v(j) = G.neigh (order.take j).toFinset v` changes by at
most one per step, and increments exactly when the newly added vertex is a
neighbour of `v`.  The corollary `neigh_take_sub_eq_count` extends this over an
arbitrary window `[j, k)`: the net change is exactly the number of neighbour
positions in the window, hence (a) `c_v` is monotone and (b) over a window
containing `m` neighbour positions, `c_v` takes at most `m + 1` distinct values
(`neigh_take_image_card_le`), which is the combinatorial heart of the
`O((deg+1) log n)` probe.

Note: the one-step identity requires `order.Nodup`.  Without it the statement is
false: if `order` revisits an already-chosen vertex, `(order.take (j+1)).toFinset`
still equals `(order.take j).toFinset` while the indicator can be `1`. -/

noncomputable section

namespace DynamicMcs
namespace Proofs

open UGraph

variable {n : ℕ}

open Classical in
/-- One-step cardinality update for `neigh` when a fresh vertex is added. -/
lemma neigh_insert_aux (G : UGraph n) (s : Finset (Vert n)) (x v : Vert n) (hx : x ∉ s) :
    G.neigh (insert x s) v = G.neigh s v + (if G.adj v x then 1 else 0) := by
  classical
  unfold UGraph.neigh
  have hle : (s.filter (fun y => ¬ G.adj v y)).card ≤ s.card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  rw [Finset.card_insert_of_notMem hx, Finset.filter_insert]
  by_cases h : G.adj v x
  · simp only [h, not_true, ↓reduceIte]
    omega
  · simp only [h, not_false_eq_true, ↓reduceIte]
    have hx' : x ∉ s.filter (fun y => ¬ G.adj v y) :=
      fun hx2 => hx (Finset.filter_subset _ _ hx2)
    rw [Finset.card_insert_of_notMem hx']
    omega

open Classical in
/-- The step-function identity: `c_v` increases by exactly the indicator that
the newly added vertex is a neighbour of `v`. -/
lemma neigh_take_succ (G : UGraph n) (order : List (Vert n)) (hnodup : order.Nodup)
    (v : Vert n) (j : ℕ) (hj : j < order.length) :
    G.neigh (order.take (j+1)).toFinset v =
      G.neigh (order.take j).toFinset v +
        (if G.adj v (order.get ⟨j, hj⟩) then 1 else 0) := by
  classical
  let x := order.get ⟨j, hj⟩
  have htake : order.take (j+1) = order.take j ++ [x] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hj]
    simp [x]
  have hxN : x ∉ (order.take j).toFinset := by
    rw [List.mem_toFinset]
    intro hx
    have h1 := (List.mem_take_iff_idxOf_lt (List.get_mem order ⟨j, hj⟩)).mp hx
    have h2 : List.idxOf (order.get ⟨j, hj⟩) order = j := List.get_idxOf hnodup ⟨j, hj⟩
    rw [h2] at h1
    exact absurd h1 (lt_irrefl j)
  rw [htake, List.toFinset_append]
  have hsing : ([x] : List (Vert n)).toFinset = {x} := by simp
  rw [hsing, Finset.union_singleton]
  exact neigh_insert_aux G (order.take j).toFinset x v hxN

open Classical in
/-- `neigh S v` counts exactly the `S`-vertices adjacent to `v`. -/
lemma neigh_eq_filter_adj_card (G : UGraph n) (s : Finset (Vert n)) (v : Vert n) :
    G.neigh s v = (s.filter (fun w => G.adj v w)).card := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := s) (p := fun w => G.adj v w)
  unfold UGraph.neigh
  omega

open Classical in
/-- Filtering a nodup list by adjacency and counting equals filtering its
finset. -/
lemma toFinset_filter_card (G : UGraph n) (l : List (Vert n)) (hl : l.Nodup) (v : Vert n) :
    (l.toFinset.filter (fun w => G.adj v w)).card =
      (l.filter (fun w => G.adj v w)).length := by
  classical
  rw [← List.toFinset_card_of_nodup (hl.filter _)]
  congr 1
  ext x
  simp only [Finset.mem_filter, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]

open Classical in
/-- Window form of the step-function identity: the net change of `c_v` over
`[j, k)` is exactly the number of neighbour positions in the window. -/
theorem neigh_take_sub_eq_count (G : UGraph n) (order : List (Vert n)) (hnodup : order.Nodup)
    (v : Vert n) (j k : ℕ) (hjk : j ≤ k) :
    G.neigh (order.take k).toFinset v =
      G.neigh (order.take j).toFinset v +
        (List.filter (fun w => G.adj v w) ((order.drop j).take (k - j))).length := by
  classical
  rw [neigh_eq_filter_adj_card, neigh_eq_filter_adj_card]
  rw [toFinset_filter_card _ _ ((List.take_sublist k order).nodup hnodup) v,
    toFinset_filter_card _ _ ((List.take_sublist j order).nodup hnodup) v]
  have hsplit : order.take k = order.take j ++ (order.drop j).take (k - j) := by
    have h := List.take_add (l := order) (i := j) (j := k - j)
    rw [Nat.add_sub_cancel' hjk] at h
    exact h
  rw [hsplit, List.filter_append, List.length_append]

open Classical in
/-- The increment over a window is bounded by the number of adjacent vertices added. -/
theorem neigh_take_sub_le_count (G : UGraph n) (order : List (Vert n)) (hnodup : order.Nodup)
    (v : Vert n) (j k : ℕ) (hjk : j ≤ k) :
    G.neigh (order.take k).toFinset v - G.neigh (order.take j).toFinset v ≤
      (List.filter (fun w => G.adj v w) ((order.drop j).take (k - j))).length := by
  rw [neigh_take_sub_eq_count G order hnodup v j k hjk]
  omega

/-- `c_v` is monotone along `order`. -/
lemma neigh_take_mono (G : UGraph n) (order : List (Vert n)) (hnodup : order.Nodup) (v : Vert n)
    {j k : ℕ} (hjk : j ≤ k) :
    G.neigh (order.take j).toFinset v ≤ G.neigh (order.take k).toFinset v := by
  rw [neigh_take_sub_eq_count G order hnodup v j k hjk]
  omega

open Classical in
/-- The number of distinct values of `c_v(t)` as `t` ranges over `[j, k]` is at
most the number of neighbour positions in the window plus one. -/
theorem neigh_take_image_card_le (G : UGraph n) (order : List (Vert n)) (hnodup : order.Nodup)
    (v : Vert n) (j k : ℕ) (hjk : j ≤ k) :
    (Finset.image (fun t => G.neigh (order.take t).toFinset v) (Finset.Icc j k)).card ≤
      (List.filter (fun w => G.adj v w) ((order.drop j).take (k - j))).length + 1 := by
  classical
  have hmono : ∀ t, j ≤ t → t ≤ k → G.neigh (order.take j).toFinset v ≤
      G.neigh (order.take t).toFinset v :=
    fun t h1 _ => neigh_take_mono G order hnodup v h1
  have hsub : Finset.image (fun t => G.neigh (order.take t).toFinset v) (Finset.Icc j k)
      ⊆ Finset.Icc (G.neigh (order.take j).toFinset v) (G.neigh (order.take k).toFinset v) := by
    intro y hy
    rcases Finset.mem_image.mp hy with ⟨t, ht, rfl⟩
    rw [Finset.mem_Icc] at ht ⊢
    exact ⟨hmono t ht.1 ht.2,
      neigh_take_mono G order hnodup v ht.2⟩
  calc (Finset.image (fun t => G.neigh (order.take t).toFinset v) (Finset.Icc j k)).card
      ≤ (Finset.Icc (G.neigh (order.take j).toFinset v) (G.neigh (order.take k).toFinset v)).card :=
        Finset.card_le_card hsub
    _ = (List.filter (fun w => G.adj v w) ((order.drop j).take (k - j))).length + 1 := by
        rw [Nat.card_Icc, neigh_take_sub_eq_count G order hnodup v j k hjk]
        omega

end Proofs
end DynamicMcs
