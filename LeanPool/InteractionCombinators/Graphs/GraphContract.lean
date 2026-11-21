/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Graphs.GraphRaw

/-!
# Contraction, and the graph of a net

Facts about `Graph.Contract`, the erasure of a name that ends two wires (Lafont 1997, Section 1.1,
page 71), and the existence of a graph: every linear net has a graph, and that graph is well
formed.

Linearity is not used: a name that occurs three times leaves, after one contraction, a single
end, which is a free port. For a text that is not linear the graph is then not unique
(`Checks/Core/GraphReview.lean`, `threeText`); uniqueness is where linearity matters.

Contents, in the order of the file:

1. One contraction: `Contract.cells_eq`, `Contract.ends_eq`, `Contract.ends_le`,
   `Contract.card_ends`, `Contract.count_port`. One contraction keeps the cells and removes two
   ends of one name from the ends of the wires, so the counts of the ports do not change.
2. Sequences of contractions: `contracts_cells_eq`, `contracts_ends_le`, `contracts_count_port`,
   `contracts_count_name_le`, `contracts_wf`. No name gains an end, and the fields `nodup`,
   `port` and `cell` of `Graph.WF` are kept.
3. Progress and termination: `exists_wire_of_mem`, `exists_contract` (a name that ends two wires
   can be erased), `exists_contracts` (from any graph a sequence of contractions reaches a graph
   where every name ends at most one wire; the number of ends decreases by two at each step).
4. Main results, the graph of a net: `raw_contracts_wf`, `Net.exists_ofList`, `Net.HasGraph.wf`
   (every graph of a text is well formed), `Net.exists_graph`, `Net.Linear.exists_graph`
   (every linear net has a well formed graph).
-/

@[expose] public section

namespace INet

variable {S : Signature} {ν : Type}

namespace Graph

-- ============================================================================================
-- 1. One contraction
-- ============================================================================================

/-- **A contraction keeps the cells** (Lafont 1997, page 71). -/
theorem Contract.cells_eq
    -- a contraction from `G` to `H`
    {G H : Graph S ν}
    (h : Contract G H) :
    H.cells = G.cells := by
  cases h <;> rfl

/-- **A contraction removes two ends of one name** (Lafont 1997, page 71): the ends of the wires
of `G` are those of `H` and twice the erased name. This holds for the joining of two wires and
for the closing of a cyclic wire. -/
theorem Contract.ends_eq
    -- a contraction from `G` to `H`
    {G H : Graph S ν}
    (h : Contract G H) :
    -- some name `x` is the difference: the ends of `G` are `x` twice and the ends of `H`
    ∃ x, G.ends = .name x ::ₘ .name x ::ₘ H.ends := by
  cases h with
  | join x p q C W n =>
    refine ⟨x, ?_⟩
    simp only [ends_eq_bind, Multiset.cons_bind, wireEnds_mk, Multiset.insert_eq_cons,
      Multiset.cons_add, Multiset.singleton_add]
    exact congrArg (End.name x ::ₘ ·) (Multiset.cons_swap _ _ _)
  | loop x C W n =>
    refine ⟨x, ?_⟩
    simp only [ends_eq_bind, Multiset.cons_bind, wireEnds_mk, Multiset.insert_eq_cons,
      Multiset.cons_add, Multiset.singleton_add]

/-- A contraction removes ends and adds none (Lafont 1997, page 71). -/
theorem Contract.ends_le
    -- a contraction from `G` to `H`
    {G H : Graph S ν}
    (h : Contract G H) :
    H.ends ≤ G.ends := by
  obtain ⟨x, hx⟩ := h.ends_eq
  rw [hx]
  exact (Multiset.le_cons_self _ _).trans (Multiset.le_cons_self _ _)

/-- **A contraction removes exactly two ends** (Lafont 1997, page 71). -/
theorem Contract.card_ends
    -- a contraction from `G` to `H`
    {G H : Graph S ν}
    (h : Contract G H) :
    Multiset.card G.ends = Multiset.card H.ends + 2 := by
  obtain ⟨x, hx⟩ := h.ends_eq
  rw [hx, Multiset.card_cons, Multiset.card_cons]

/-- A contraction does not change how many wires a port ends (Lafont 1997, page 71). -/
theorem Contract.count_port
    [DecidableEq ν]
    -- a contraction from `G` to `H`
    {G H : Graph S ν}
    (h : Contract G H)
    -- the port `i` of the cell numbered `c`
    (c i : ℕ) :
    H.ends.count (.port c i) = G.ends.count (.port c i) := by
  obtain ⟨x, hx⟩ := h.ends_eq
  rw [hx, Multiset.count_cons_of_ne (by simp), Multiset.count_cons_of_ne (by simp)]

-- ============================================================================================
-- 2. Sequences of contractions
-- ============================================================================================

/-- **Contractions keep the cells** (Lafont 1997, page 71). -/
theorem contracts_cells_eq
    -- a sequence of contractions from `G` to `H`
    {G H : Graph S ν}
    (h : Relation.ReflTransGen Contract G H) :
    H.cells = G.cells := by
  induction h with
  | refl => rfl
  | tail _ h ih => rw [h.cells_eq, ih]

/-- Contractions remove ends and add none (Lafont 1997, page 71). -/
theorem contracts_ends_le
    -- a sequence of contractions from `G` to `H`
    {G H : Graph S ν}
    (h : Relation.ReflTransGen Contract G H) :
    H.ends ≤ G.ends := by
  induction h with
  | refl => exact le_rfl
  | tail _ h ih => exact h.ends_le.trans ih

/-- **Contractions do not change how many wires a port ends** (Lafont 1997, page 71). -/
theorem contracts_count_port
    [DecidableEq ν]
    -- a sequence of contractions from `G` to `H`
    {G H : Graph S ν}
    (h : Relation.ReflTransGen Contract G H)
    -- the port `i` of the cell numbered `c`
    (c i : ℕ) :
    H.ends.count (.port c i) = G.ends.count (.port c i) := by
  induction h with
  | refl => rfl
  | tail _ h ih => rw [h.count_port, ih]

/-- **Contractions give no name a new end** (Lafont 1997, page 71): a name ends at most as many
wires after them as before. -/
theorem contracts_count_name_le
    [DecidableEq ν]
    -- a sequence of contractions from `G` to `H`
    {G H : Graph S ν}
    (h : Relation.ReflTransGen Contract G H)
    -- a name
    (x : ν) :
    H.ends.count (.name x) ≤ G.ends.count (.name x) :=
  Multiset.count_le_of_le _ (contracts_ends_le h)

/-- **Contractions keep the fields `nodup`, `port` and `cell` of `Graph.WF`** (Lafont 1997,
page 71): if the cells of `G` have distinct numbers, every port of a cell of `G` ends exactly one
wire and every port that is an end is a port of a cell, then the same holds of `H`. -/
theorem contracts_wf
    [DecidableEq ν]
    -- a sequence of contractions from `G` to `H`
    {G H : Graph S ν}
    (h : Relation.ReflTransGen Contract G H)
    -- the cells of `G` have distinct numbers
    (hn : (G.cells.map Prod.fst).Nodup)
    -- every port of a cell of `G` ends exactly one wire of `G`
    (hp : ∀ c α, (c, α) ∈ G.cells → ∀ i ≤ S.arity α, G.ends.count (.port c i) = 1)
    -- every port that ends a wire of `G` is a port of a cell of `G`
    (hc : ∀ c i, End.port c i ∈ G.ends → ∃ α, (c, α) ∈ G.cells ∧ i ≤ S.arity α)
    -- in `H`, every name ends at most one wire
    (hx : ∀ x, H.ends.count (.name x) ≤ 1) :
    H.WF where
  nodup := by rw [contracts_cells_eq h]; exact hn
  port c α hα i hi := by rw [contracts_count_port h]; exact hp c α (contracts_cells_eq h ▸ hα) i hi
  cell c i hm := by
    obtain ⟨α, hα, hi⟩ := hc c i (Multiset.mem_of_le (contracts_ends_le h) hm)
    exact ⟨α, contracts_cells_eq h ▸ hα, hi⟩
  name := hx

-- ============================================================================================
-- 3. Progress and termination
-- ============================================================================================

/-- A name that is an end of one of the wires: the wires are that wire and the others. -/
private theorem exists_wire_of_mem
    -- the wires, and a name that ends one of them
    {W : Multiset (Sym2 (End ν))}
    {x : ν}
    (h : End.name x ∈ W.bind wireEnds) :
    -- the wires are a wire from `x` to some end `p`, and the others `W'`
    ∃ p W', W = s(.name x, p) ::ₘ W' := by
  obtain ⟨w, hw, hxw⟩ := Multiset.mem_bind.1 h
  obtain ⟨W', rfl⟩ := Multiset.exists_cons_of_mem hw
  induction w using Sym2.ind with
  | _ a b =>
    simp only [wireEnds_mk, Multiset.insert_eq_cons, Multiset.mem_cons,
      Multiset.mem_singleton] at hxw
    rcases hxw with rfl | rfl
    · exact ⟨b, W', rfl⟩
    · exact ⟨a, W', by rw [Sym2.eq_swap]⟩

/-- **A name that ends two wires can be erased** (Lafont 1997, page 71): either it ends both
sides of one wire, which becomes cyclic, or it ends two different wires, which are joined. -/
theorem exists_contract
    [DecidableEq ν]
    -- the graph
    (G : Graph S ν)
    -- a name that ends at least two wires of it
    (x : ν)
    (hx : 2 ≤ G.ends.count (.name x)) :
    -- some contraction starts from `G`
    ∃ H, Contract G H := by
  obtain ⟨C, W, n⟩ := G
  change 2 ≤ (W.bind wireEnds).count (.name x) at hx
  have h1 : 0 < (W.bind wireEnds).count (.name x) := by omega
  obtain ⟨p, W', rfl⟩ := exists_wire_of_mem (Multiset.count_pos.1 h1)
  by_cases hp : p = .name x
  · subst hp
    exact ⟨_, .loop x C W' n⟩
  · rw [Multiset.cons_bind, Multiset.count_add, wireEnds_mk, Multiset.insert_eq_cons,
      Multiset.count_cons_self, Multiset.count_singleton] at hx
    simp only [Ne.symm hp, ite_false] at hx
    have h2 : 0 < (W'.bind wireEnds).count (.name x) := by omega
    obtain ⟨q, W'', rfl⟩ := exists_wire_of_mem (Multiset.count_pos.1 h2)
    exact ⟨_, .join x p q C W'' n⟩

/-- **Contraction terminates** (Lafont 1997, page 71): from any graph, a sequence of contractions
reaches a graph in which every name ends at most one wire. Each contraction removes two ends. -/
theorem exists_contracts
    [DecidableEq ν]
    -- the graph
    (G : Graph S ν) :
    -- there is a graph `H` such that
    ∃ H,
      -- a sequence of contractions leads from `G` to `H`,
      Relation.ReflTransGen Contract G H ∧
      -- and in `H` every name ends at most one wire
      ∀ x, H.ends.count (.name x) ≤ 1 := by
  suffices ∀ m, ∀ G : Graph S ν, Multiset.card G.ends = m →
      ∃ H, Relation.ReflTransGen Contract G H ∧ ∀ x, H.ends.count (.name x) ≤ 1 from
    this _ G rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro G hG
    by_cases h : ∃ x, 2 ≤ G.ends.count (.name x)
    · obtain ⟨x, hx⟩ := h
      obtain ⟨H, hH⟩ := exists_contract G x hx
      obtain ⟨K, hK, hK1⟩ := ih _ (by rw [← hG, hH.card_ends]; omega) H rfl
      exact ⟨K, .head hH hK, hK1⟩
    · push Not at h
      exact ⟨G, .refl, fun x => by have := h x; omega⟩

-- ============================================================================================
-- 4. Main results: the graph of a net
-- ============================================================================================

/-- **Every graph of a text is well formed** (Lafont 1997, page 71): contract the raw graph of a
list of equations, with cells numbered from any `k`, until every name ends at most one wire; the
result is `WF`. -/
theorem raw_contracts_wf
    [DecidableEq ν]
    -- the first number given to a cell, and the list of equations
    (k : ℕ)
    (L : List (Term S ν × Term S ν))
    -- a sequence of contractions from the raw graph of the list to `G`
    {G : Graph S ν}
    (h : Relation.ReflTransGen Contract (raw k L) G)
    -- in `G`, every name ends at most one wire
    (hx : ∀ x, G.ends.count (.name x) ≤ 1) :
    G.WF :=
  contracts_wf h (raw_nodup k L) (raw_port k L) (raw_cell k L) hx

end Graph

/-- Every net is the text of a list of equations: some list `L` has `N` as its multiset of
equations. -/
theorem Net.exists_ofList
    -- the net
    (N : Net S ν) :
    ∃ L, N = Net.ofList L := by
  induction N using Multiset.induction_on with
  | empty => exact ⟨[], rfl⟩
  | cons e N ih =>
    obtain ⟨L, rfl⟩ := ih
    induction e using Sym2.ind with
    | _ a b => exact ⟨(a, b) :: L, rfl⟩

/-- **Every graph of a net is well formed** (Lafont 1997, page 71). -/
theorem Net.HasGraph.wf
    [DecidableEq ν]
    -- a net and one of its graphs
    {N : Net S ν}
    {G : Graph S ν}
    (h : N.HasGraph G) :
    G.WF := by
  obtain ⟨L, k, -, hG, hx⟩ := h
  exact Graph.raw_contracts_wf k L hG hx

/-- Every net has a graph, and it is well formed (Lafont 1997, page 71). -/
theorem Net.exists_graph
    [DecidableEq ν]
    -- the net
    (N : Net S ν) :
    -- there is a graph `G` such that
    ∃ G,
      -- `G` is a graph of `N`,
      N.HasGraph G ∧
      -- and `G` is well formed
      G.WF := by
  obtain ⟨L, rfl⟩ := Net.exists_ofList N
  obtain ⟨G, hG, hx⟩ := Graph.exists_contracts (Graph.raw 0 L)
  exact ⟨G, ⟨L, 0, rfl, hG, hx⟩, Graph.raw_contracts_wf 0 L hG hx⟩

/-- **Every linear net has a graph, and that graph is well formed** (Lafont 1997, page 71).
Linearity is not needed for this statement (`Net.exists_graph`); it is needed for the uniqueness
of the graph. -/
theorem Net.Linear.exists_graph
    [DecidableEq ν]
    -- a linear net
    {N : Net S ν}
    (_h : N.Linear) :
    -- there is a graph `G` such that
    ∃ G,
      -- `G` is a graph of `N`,
      N.HasGraph G ∧
      -- and `G` is well formed
      G.WF :=
  N.exists_graph

end INet
