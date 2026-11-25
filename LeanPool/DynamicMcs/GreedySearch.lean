/-
Copyright (c) 2026 Md Thoriqul Islam Thonmay and Gregory Morse. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Md Thoriqul Islam Thonmay, Gregory Morse
-/

-- Modified for Lean Pool.

module

public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.List.TakeDrop

/-!
# Dynamic MCS ordering: candidate `gen001_c01`

Problem.  Maximum Cardinality Search (MCS) ordering on an undirected,
loop-free graph.  Starting with no vertex chosen, MCS repeatedly chooses an
unchosen vertex with the maximum number of already-chosen neighbors, ties
being broken by the lowest vertex index.  The chosen order is a *valid MCS
ordering* of the graph.

Candidate invariant.  The candidate maintains the current valid MCS ordering
under single edge flips (insert or delete of one edge).  Its update is
dynamic: an edge `{u, v}` changes a vertex's cardinality only once one of its
endpoints is chosen, so the greedy prefix up to and including the earlier of
`u` and `v` (in the current ordering) is unchanged by the flip; only the
suffix after that endpoint is recomputed greedily on the post-update graph.

This module fixes the formal definitions and *states* the theorems.  The
central theorem asserts that `init`, `insert_edge`, and `delete_edge` each
preserve the MCS-ordering invariant for every finite graph and every legal
edge update.  Proofs are developed in later stages.

We model a graph as a symmetric, loop-free adjacency relation on vertices
`Fin n`, and a candidate `state` as the maintained MCS ordering (a `List
(Fin n)`).  `IsMCSOrdering G order` is the invariant: `order` lists every
vertex exactly once and, at each position, the vertex chosen is the legal MCS
pick (maximum cardinality, ties broken by lowest index) given the vertices
chosen before position `i`.
-/

@[expose] public section

noncomputable section

namespace DynamicMcs

namespace Greedy

/-- Vertices of an `n`-vertex undirected graph. -/
abbrev Vert (n : ℕ) := Fin n

/-- A finite undirected, loop-free graph on the vertices `Fin n`. -/
structure UGraph (n : ℕ) where
  /-- Adjacency of a pair of vertices. -/
  adj : Vert n → Vert n → Prop
  symm : ∀ {x y : Vert n}, adj x y → adj y x
  loopless : ∀ (x : Vert n), ¬ adj x x

namespace UGraph

variable {n : ℕ} {G G' : UGraph n}

/-- Cardinality of `w` measured against the already-chosen set `chosen`,
i.e. the number of neighbors of `w` lying in `chosen`. -/
def neigh (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : ℕ := by
  classical
  exact chosen.card - (chosen.filter (fun x => ¬ G.adj w x)).card

/-- `w` is a legal MCS step given `chosen`: `w` is unchosen, its cardinality
is maximal among the unchosen vertices, and it is the least-index vertex
achieving that maximum (the candidate's lowest-index tie-breaking rule). -/
def IsMCSNext (G : UGraph n) (chosen : Finset (Vert n)) (w : Vert n) : Prop :=
  w ∈ (Finset.univ : Finset (Vert n)) \ chosen ∧
  (∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x ≤ G.neigh chosen w) ∧
  (∀ x : Vert n, x ∈ (Finset.univ : Finset (Vert n)) \ chosen →
    G.neigh chosen x = G.neigh chosen w → w ≤ x)

/-- `order` is a valid MCS ordering of `G`: it lists every vertex exactly
once and, at every position `i`, the vertex `order[i]` is the legal MCS pick
given the vertices chosen before position `i`. -/
def IsMCSOrdering (G : UGraph n) (order : List (Vert n)) : Prop :=
  order.Nodup ∧ order.length = n ∧
  ∀ (i : ℕ) (hi : i < order.length),
    IsMCSNext G (order.take i).toFinset (order.get ⟨i, hi⟩)

/-- The candidate's validity predicate on a state: the maintained ordering is
a valid MCS ordering of the current graph. -/
def ValidMCSState (G : UGraph n) (order : List (Vert n)) : Prop :=
  IsMCSOrdering G order

/-- `G'` differs from `G` only by flipping the undirected edge `{u, v}`:
outside the two ordered pairs `(u, v)` and `(v, u)` the adjacency is
unchanged, and `u ≠ v`. -/
def FlipOf (G G' : UGraph n) (u v : Vert n) : Prop :=
  u ≠ v ∧
  ∀ (x y : Vert n),
    G'.adj x y = G.adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u)

/-- The unchosen vertices of maximum cardinality exist whenever some vertex is
unchosen. -/
theorem maxUnchosen_nonempty (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) :
    (((Finset.univ : Finset (Vert n)) \ chosen).filter (fun x =>
      G.neigh chosen x =
          ((Finset.univ : Finset (Vert n)) \ chosen).sup (G.neigh chosen))).Nonempty := by
  have hU : ((Finset.univ : Finset (Vert n)) \ chosen).Nonempty :=
    Finset.sdiff_nonempty.2 (fun hs => h (Finset.univ_subset_iff.1 hs))
  obtain ⟨w, hw, hsup⟩ := Finset.exists_mem_eq_sup _ hU (G.neigh chosen)
  exact ⟨w, Finset.mem_filter.2 ⟨hw, hsup.symm⟩⟩

/-- The canonical MCS pick: the least-index unchosen vertex of maximum
cardinality. -/
def mcsPick (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) : Vert n :=
  (((Finset.univ : Finset (Vert n)) \ chosen).filter (fun x =>
    G.neigh chosen x = ((Finset.univ : Finset (Vert n)) \ chosen).sup (G.neigh chosen))).min'
    (maxUnchosen_nonempty G chosen h)

/-- The canonical pick is a legal MCS step. -/
theorem mcsPick_isMCSNext (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) :
    IsMCSNext G chosen (mcsPick G chosen h) := by
  have hmem := Finset.min'_mem _ (maxUnchosen_nonempty G chosen h)
  rw [Finset.mem_filter] at hmem
  refine ⟨hmem.1, fun x hx => hmem.2 ▸ Finset.le_sup hx, fun x hx hx' => ?_⟩
  exact Finset.min'_le _ x (Finset.mem_filter.2 ⟨hx, hx'.trans hmem.2⟩)

/-- The canonical pick, carried with its legality proof. -/
def greedyPick (G : UGraph n) (chosen : Finset (Vert n))
    (h : chosen ≠ (Finset.univ : Finset (Vert n))) : { w : Vert n // IsMCSNext G chosen w } :=
  ⟨mcsPick G chosen h, mcsPick_isMCSNext G chosen h⟩

/-- Repeatedly extend `chosen` with the MCS pick until every vertex is
chosen, with one step per unit of the counter `k`.  The invariant
`chosen.card + k = n` certifies that `k` further MCS steps suffice. -/
noncomputable def mcsLoop (G : UGraph n) (chosen : Finset (Vert n)) (k : ℕ)
    (hk : chosen.card + k = n) : List (Vert n) :=
  match k with
  | 0 => []
  | km + 1 =>
      have hchosen : chosen ≠ (Finset.univ : Finset (Vert n)) := by
        intro hc
        have hcard : chosen.card = n := by simp [hc]
        omega
      let p := (greedyPick G chosen hchosen).1
      have hp : p ∉ chosen := by
        exact (Finset.mem_sdiff.mp (greedyPick G chosen hchosen).2.1).2
      have hins : (insert p chosen).card = chosen.card + 1 := by
        exact Finset.card_insert_of_notMem hp
      p :: mcsLoop G (insert p chosen) km (by omega)
termination_by k
decreasing_by
  simp_wf

/-- MCS continuation: greedily extend the already-chosen set `chosen` to a
full ordering suffix. -/
noncomputable def mcsRemainder (G : UGraph n) (chosen : Finset (Vert n)) : List (Vert n) :=
  mcsLoop G chosen (n - chosen.card) (by
    have hcard : chosen.card ≤ n := by
      simpa using (Finset.card_le_univ chosen)
    omega)

/-- Greedy continuation of an MCS prefix `pref`: the fixed prefix followed by
the deterministically recomputed suffix. -/
noncomputable def greedySuffix (G : UGraph n) (pref : List (Vert n)) : List (Vert n) :=
  pref ++ mcsRemainder G pref.toFinset

/-- Position (in `order`) of the earlier of the endpoints `u` and `v`. -/
def earlierPos (order : List (Vert n)) (u v : Vert n) : ℕ :=
  min (List.idxOf u order) (List.idxOf v order)

/-- The candidate's dynamic update for an edge flip: keep the prefix of the
current ordering up to and including the earlier of the two endpoints, and
recompute the suffix greedily on the post-update graph `G`. -/
noncomputable def mcsUpdate (G : UGraph n) (u v : Vert n)
    (order : List (Vert n)) : List (Vert n) :=
  if _h : u = v then order
  else greedySuffix G (order.take (earlierPos order u v + 1))

/-! ## Lemmas -/

/-- `earlierPos` is at most the position of each endpoint. -/
lemma le_idxOf_of_le_earlierPos (u v : Vert n) (order : List (Vert n))
    {i : ℕ} (hi : i ≤ earlierPos order u v) :
    i ≤ List.idxOf u order ∧ i ≤ List.idxOf v order := by
  unfold earlierPos at hi
  constructor
  · exact le_trans hi (Nat.min_le_left _ _)
  · exact le_trans hi (Nat.min_le_right _ _)

/-- Before the earlier endpoint is chosen, neither endpoint is in the prefix. -/
lemma endpoints_not_in_prefix (order : List (Vert n)) (u v : Vert n)
    (hmu : u ∈ order) (hmv : v ∈ order) {i : ℕ} (hi : i ≤ earlierPos order u v) :
    u ∉ order.take i ∧ v ∉ order.take i := by
  rcases le_idxOf_of_le_earlierPos u v order hi with ⟨hu, hv⟩
  constructor
  · rw [List.mem_take_iff_idxOf_lt hmu]
    omega
  · rw [List.mem_take_iff_idxOf_lt hmv]
    omega

/-- A valid MCS ordering contains every vertex. -/
lemma mem_of_IsMCSOrdering (order : List (Vert n)) (hvalid : IsMCSOrdering G order) :
    ∀ z : Vert n, z ∈ order := by
  classical
  intro z
  rcases hvalid with ⟨hnodup, hlen, hstep⟩
  have hcard : order.toFinset.card = Fintype.card (Vert n) := by
    rw [List.toFinset_card_of_nodup hnodup]
    rw [hlen]
    simp
  have htofinset : order.toFinset = (Finset.univ : Finset (Vert n)) :=
    Finset.eq_univ_of_card order.toFinset hcard
  have hz : z ∈ order.toFinset := by
    rw [htofinset]
    exact Finset.mem_univ z
  exact List.mem_toFinset.mp hz

/-- An edge flip does not change any vertex's cardinality as long as neither
endpoint has been chosen yet. -/
lemma neigh_eq_of_flip (chosen : Finset (Vert n)) (u v : Vert n)
    (hflip : FlipOf G G' u v) (hu : u ∉ chosen) (hv : v ∉ chosen) :
    ∀ z : Vert n, G.neigh chosen z = G'.neigh chosen z := by
  classical
  intro z
  unfold neigh
  have hfilter : chosen.filter (fun x => ¬ G.adj z x) =
      chosen.filter (fun x => ¬ G'.adj z x) := by
    apply Finset.filter_congr
    intro x hxchosen
    constructor
    · intro hnot hadj
      apply hnot
      rcases hflip with ⟨huv, hflipadj⟩
      have heq : G.adj z x = G'.adj z x := by
        rcases hflipadj z x with h | h' | h'
        · exact h.symm
        · rcases h' with ⟨rfl, rfl⟩
          exfalso; exact hv hxchosen
        · rcases h' with ⟨rfl, rfl⟩
          exfalso; exact hu hxchosen
      exact heq ▸ hadj
    · intro hnot hadj
      apply hnot
      rcases hflip with ⟨huv, hflipadj⟩
      have heq : G'.adj z x = G.adj z x := by
        rcases hflipadj z x with h | h' | h'
        · exact h
        · rcases h' with ⟨rfl, rfl⟩
          exfalso; exact hv hxchosen
        · rcases h' with ⟨rfl, rfl⟩
          exfalso; exact hu hxchosen
      exact heq ▸ hadj
  rw [hfilter]

/-- If all cardinalities agree on every unchosen vertex, the MCS-next
predicate is transferred unchanged across the flip. -/
lemma IsMCSNext_of_eq_neigh (chosen : Finset (Vert n)) (w : Vert n)
    (hneigh : ∀ z : Vert n, G.neigh chosen z = G'.neigh chosen z)
    (hnext : IsMCSNext G chosen w) : IsMCSNext G' chosen w := by
  classical
  rcases hnext with ⟨hwU, hwmax, hwmin⟩
  unfold IsMCSNext
  constructor
  · exact hwU
  constructor
  · intro x hx
    rw [← hneigh x]
    rw [← hneigh w]
    exact hwmax x hx
  · intro x hx hc
    have hcw : G.neigh chosen x = G.neigh chosen w := by
      rw [hneigh x, hneigh w, hc]
    exact hwmin x hx hcw

/-- The greedy prefix up to and including the earlier of the endpoints `u`,
`v` of the flipped edge is unchanged: every position up to `earlierPos` still
picks the same vertex on the post-update graph. -/
lemma prefix_preserved (order : List (Vert n)) (u v : Vert n)
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order)
    (i : ℕ) (hi0 : i ≤ earlierPos order u v) (hi : i < order.length) :
    IsMCSNext G' (order.take i).toFinset (order.get ⟨i, hi⟩) := by
  classical
  rcases hvalid with ⟨hnodup, hlen, hstep⟩
  have hmu : u ∈ order := mem_of_IsMCSOrdering order ⟨hnodup, hlen, hstep⟩ u
  have hmv : v ∈ order := mem_of_IsMCSOrdering order ⟨hnodup, hlen, hstep⟩ v
  rcases endpoints_not_in_prefix order u v hmu hmv hi0 with ⟨hu, hv⟩
  have huF : u ∉ (order.take i).toFinset := by
    intro h
    exact hu (List.mem_toFinset.mp h)
  have hvF : v ∉ (order.take i).toFinset := by
    intro h
    exact hv (List.mem_toFinset.mp h)
  have hneigh : ∀ z : Vert n, G.neigh (order.take i).toFinset z =
      G'.neigh (order.take i).toFinset z := by
    intro z
    exact neigh_eq_of_flip (order.take i).toFinset u v hflip huF hvF z
  have hnext : IsMCSNext G (order.take i).toFinset (order.get ⟨i, hi⟩) := hstep i hi
  exact IsMCSNext_of_eq_neigh (order.take i).toFinset (order.get ⟨i, hi⟩) hneigh hnext

/-- Extending a valid MCS prefix by one legal pick yields a valid prefix. -/
lemma prefix_valid_append (pref : List (Vert n)) (p : Vert n)
    (hpref : ∀ (i : ℕ) (hi : i < pref.length),
      IsMCSNext G (pref.take i).toFinset (pref.get ⟨i, hi⟩))
    (hp : IsMCSNext G pref.toFinset p) :
    ∀ (i : ℕ) (hi : i < (pref ++ [p]).length),
      IsMCSNext G ((pref ++ [p]).take i).toFinset ((pref ++ [p]).get ⟨i, hi⟩) := by
  intro i hi
  by_cases hlt : i < pref.length
  · have htake : (pref ++ [p]).take i = pref.take i := by
      rw [List.take_append]
      have h0 : i - pref.length = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
      simp [h0]
    have hget : (pref ++ [p]).get ⟨i, hi⟩ = pref.get ⟨i, hlt⟩ := by
      apply List.getElem_append_left
    rw [htake, hget]
    exact hpref i hlt
  · have hi_eq : i = pref.length := by
      have hle : pref.length ≤ i := le_of_not_gt hlt
      have hlt2 : i < pref.length + 1 := by
        have : (pref ++ [p]).length = pref.length + 1 := by simp
        rwa [this] at hi
      omega
    subst i
    have htake : (pref ++ [p]).take pref.length = pref := by
      rw [List.take_append]
      simp
    have hget : (pref ++ [p]).get ⟨pref.length, hi⟩ = p := by
      simp [List.get_eq_getElem, List.getElem_append_right (le_refl pref.length)]
    rw [htake, hget]
    exact hp

/-- Loop invariant: if `pref` is a valid MCS prefix whose chosen set is `chosen`,
then `pref ++ mcsLoop G chosen k hk` is a valid MCS ordering. Prove by induction
on k (revert hk first since it depends on k; generalize chosen).
- zero: mcsLoop = []; pref ++ [] = pref; hk gives chosen.card = n so
  pref.toFinset = univ, pref.length = n, Nodup, steps = hpref.
- succ km: the loop step is `p :: mcsLoop G (insert p chosen) km _` where
  `p := (greedyPick G chosen hchosen).1`. p is a legal step (IsMCSNext) and
  p ∉ chosen, so pref ++ [p] is a valid prefix (prefix_valid_append) whose
  chosen set is insert p chosen. Apply the IH with chosen := insert p chosen,
  pref := pref ++ [p]. Reconcile the recursive mcsLoop hk proof with the IH's
  via proof_irrel, and rewrite pref ++ (p :: rest) = (pref ++ [p]) ++ rest.
NOTE: mcsLoop is @[irreducible]; unfold it with `show`/`change` (defeq), not simp. -/
lemma mcsLoop_valid (chosen : Finset (Vert n)) (k : ℕ) (hk : chosen.card + k = n) :
    ∀ (pref : List (Vert n)), pref.toFinset = chosen → pref.Nodup →
      (∀ (i : ℕ) (hi : i < pref.length),
        IsMCSNext G (pref.take i).toFinset (pref.get ⟨i, hi⟩)) →
      IsMCSOrdering G (pref ++ mcsLoop G chosen k hk) := by
  revert hk
  induction k generalizing chosen with
  | zero =>
      intro hk pref hprefF hprefNodup hpref
      unfold mcsLoop
      rw [List.append_nil]
      refine ⟨hprefNodup, ?_, hpref⟩
      have hcard : chosen.card = n := by
        rw [add_zero] at hk
        exact hk
      calc pref.length = pref.toFinset.card := (List.toFinset_card_of_nodup hprefNodup).symm
        _ = chosen.card := by rw [hprefF]
        _ = n := hcard
  | succ km ih =>
      intro hk pref hprefF hprefNodup hpref
      have hchosen : chosen ≠ (Finset.univ : Finset (Vert n)) := by
        intro hc
        have hcard : chosen.card = n := by simp [hc]
        omega
      set p := (greedyPick G chosen hchosen).1 with hpdef
      have hp : p ∉ chosen :=
        (Finset.mem_sdiff.mp (greedyPick G chosen hchosen).2.1).2
      have hrec : (insert p chosen).card + km = n := by
        have hins : (insert p chosen).card = chosen.card + 1 :=
          Finset.card_insert_of_notMem hp
        omega
      -- The loop step: unfold one iteration via the equation lemma, then
      -- `p :: rest = [p] ++ rest` and reassociate.  The proof arguments of
      -- `mcsLoop` (internal vs. ours) are equal by proof irrelevance, so the
      -- final equality holds by `rfl`.
      have hstep : pref ++ mcsLoop G chosen (km + 1) hk
          = (pref ++ [p]) ++ mcsLoop G (insert p chosen) km hrec := by
        rw [mcsLoop.eq_2, ← List.singleton_append, ← List.append_assoc]
      rw [hstep]
      refine ih (insert p chosen) hrec (pref ++ [p]) ?F ?N ?S
      · apply Finset.ext
        intro x
        rw [List.mem_toFinset, List.mem_append, List.mem_singleton, Finset.mem_insert,
          ← hprefF, ← List.mem_toFinset]
        apply Iff.intro
        · intro h; exact h.elim Or.inr Or.inl
        · intro h; exact h.elim Or.inr Or.inl
      · rw [List.nodup_append]
        refine ⟨hprefNodup, List.nodup_singleton p, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        intro heq
        exact hp (by rw [← hprefF]; exact List.mem_toFinset.mpr (heq ▸ ha))
      · refine prefix_valid_append pref p hpref ?_
        rw [hprefF]
        exact (greedyPick G chosen hchosen).2

/-- Recombining a valid MCS prefix with the greedy suffix yields a valid MCS
ordering of the same graph. -/
lemma greedySuffix_valid (G : UGraph n) (pref : List (Vert n)) (hnodup : pref.Nodup)
    (hstep : ∀ (i : ℕ) (hi : i < pref.length),
      IsMCSNext G (pref.take i).toFinset (pref.get ⟨i, hi⟩)) :
    IsMCSOrdering G (greedySuffix G pref) := by
  unfold greedySuffix mcsRemainder
  -- `mcsRemainder G pref.toFinset` is `mcsLoop G pref.toFinset (n - card) _`;
  -- the loop's proof argument unifies with the one inside `mcsRemainder` by
  -- proof irrelevance, so the refinement below closes the goal.
  refine mcsLoop_valid pref.toFinset (n - pref.toFinset.card) ?_ pref rfl hnodup hstep

/-! ## Theorems -/

/-- The dynamic update preserves the MCS-ordering invariant under every
single edge flip: for all finite graphs `G`, `G'` differing only by the edge
`{u, v}`, if `order` is a valid MCS ordering of `G`, then the updated ordering
is a valid MCS ordering of `G'`. -/
theorem mcsUpdate_preserves_invariant (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    IsMCSOrdering G' (mcsUpdate G' u v order) := by
  classical
  have huv : u ≠ v := hflip.1
  have hnodup := hvalid.1
  have hmemu : u ∈ order := mem_of_IsMCSOrdering order hvalid u
  rw [mcsUpdate, dite_eq_right huv]
  have hbound : earlierPos order u v + 1 ≤ order.length := by
    unfold earlierPos
    have hpos : List.idxOf u order < order.length := List.idxOf_lt_length_of_mem hmemu
    have : min (List.idxOf u order) (List.idxOf v order) ≤ List.idxOf u order :=
      Nat.min_le_left _ _
    omega
  refine greedySuffix_valid G' (order.take (earlierPos order u v + 1)) ?N ?S
  · exact List.Pairwise.take hnodup
  · intro i hi
    have hlt : i < order.length :=
      Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hi (List.length_take_le _ _)) hbound
    have hi0 : i ≤ earlierPos order u v :=
      Nat.lt_succ_iff.mp (Nat.lt_of_lt_of_le hi (List.length_take_le _ _))
    have htake : (order.take (earlierPos order u v + 1)).take i = order.take i := by
      rw [List.take_take, Nat.min_eq_left (Nat.le_succ_of_le hi0)]
    have hget : (order.take (earlierPos order u v + 1)).get ⟨i, hi⟩
        = order.get ⟨i, hlt⟩ := by
      rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_take]
    rw [htake, hget]
    exact prefix_preserved order u v hflip hvalid i hi0 hlt

/-- `insert_edge` preserves the invariant: inserting an edge yields a valid
MCS ordering of the resulting graph. -/
theorem insert_edge_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    ValidMCSState G' (mcsUpdate G' u v order) := by
  exact mcsUpdate_preserves_invariant u v order hflip hvalid

/-- `delete_edge` preserves the invariant: deleting an edge yields a valid
MCS ordering of the resulting graph. -/
theorem delete_edge_valid (u v : Vert n) (order : List (Vert n))
    (hflip : FlipOf G G' u v) (hvalid : IsMCSOrdering G order) :
    ValidMCSState G' (mcsUpdate G' u v order) := by
  exact mcsUpdate_preserves_invariant u v order hflip hvalid

/-- `init` produces a valid MCS ordering of the given graph. -/
theorem init_valid (G : UGraph n) : ValidMCSState G (greedySuffix G []) := by
  unfold ValidMCSState
  refine greedySuffix_valid G [] List.nodup_nil ?_
  intro i hi
  rw [List.length_nil] at hi
  exact absurd hi (Nat.not_lt_zero i)

end UGraph
end Greedy
end DynamicMcs
