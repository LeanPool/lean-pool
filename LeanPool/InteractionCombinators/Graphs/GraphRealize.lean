/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Graphs.GraphIsoEquiv

/-!
# Every well-formed graph is the graph of a linear net

Lafont 1997, Section 1.1, page 71: a net is a graph, and every graph can be written down as a
text. This file proves that a well-formed graph `G` is, up to `Iso`, the graph of a linear net,
the flat text of `G` (`Graph.flat`), whose free ports are the free ports of `G`.

The ports of the cells are named `pn c i = B + 2 ⟨c, i⟩` and the cyclic wires `ln j = B + 2 j + 1`,
where `B` bounds the free ports of `G`. The raw graph of the flat text is isomorphic to the graph
with the cells of `G`, a *stub* `pn c i — port c i` for each port, a wire between names for each
wire of `G` and a wire `ln j — ln j` for each cyclic wire. Erasing each `pn c i` joins its stub
to its wire, and gives back the wires of `G`; erasing each `ln j` gives back its cyclic wires.

Contents, in the order of the file:

1. Erasing many names: `Graph.bind_wireEnds_map`, `Graph.substName_eq_name`,
   `Graph.count_map_substName`; `Graph.contracts_stubs` (erasing the names of stubs plugs their
   ports into the other wires), `Graph.contracts_loops` (erasing the names of wires `z — z` makes
   cyclic wires).
2. The stubs of some cells: `Graph.mem_bind_cellPorts`, `Graph.name_notMem_bind_cellPorts`,
   `Graph.nodup_bind_cellPorts`; the definitions `Graph.cellGraph` (the stubs) and
   `Graph.cellPair` (the equation of a cell); `Graph.cellGraph_portsIn`, the private
   `range_succ_map''`, `Graph.cellGraph_single_iso`, `Graph.cellGraph_iso` (the raw graph of the
   equations of some cells is isomorphic to their stubs).
3. Equations between names: `Graph.raw_names`, the private `exists_list_sym2`.
4. Fresh names for the ports and the cyclic wires: `Graph.freeBound`, `Graph.mem_free`,
   `Graph.lt_freeBound`; the names `Graph.realPn`, `Graph.realLn`; `Graph.unflat` (reading a
   name back as an end) and its lemmas; the private `count_map_of_leftInv`,
   `Graph.vars_flatLoops`.
5. The names of the flat text of a well-formed graph: `Graph.flatB`, `Graph.count_vars_flatB`,
   `Graph.linear_flatB`, `Graph.count_vars_flatB_eq_one`.
6. Main results: `Graph.WF.hasGraph_flatB` (the flat text of `G` has a graph isomorphic to `G`),
   `Graph.WF.exists_net_free` (the theorem, with the free ports), `Graph.WF.exists_net`.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

namespace Graph

-- ============================================================================================
-- 1. Erasing many names
-- ============================================================================================

/-- The ends of renamed wires are the renamed ends. -/
theorem bind_wireEnds_map
    -- the renaming of the ends, and the wires
    (f : End ℕ → End ℕ)
    (W : Multiset (Sym2 (End ℕ))) :
    (W.map (Sym2.map f)).bind wireEnds = (W.bind wireEnds).map f := by
  rw [Multiset.bind_map, Multiset.map_bind]
  congr 1
  funext e
  induction e using Sym2.ind with
  | _ p q => simp [Multiset.insert_eq_cons]

/-- If replacing the name `x` by a port gives the name `y`, the end was already `y`, and `y` is not
`x` (Lafont 1997, page 71). -/
theorem substName_eq_name
    -- the erased name `x`, and the name `y` obtained
    {x y : ℕ}
    -- what replaces `x`: an end that is not a name
    {r : End ℕ}
    (hr : ∀ w, r ≠ .name w)
    -- an end that becomes `y` once `x` is replaced by `r`
    {z : End ℕ}
    (h : End.substName x r z = .name y) :
    -- the end was `y`
    z = .name y ∧
    -- and `y` is not `x`
    y ≠ x := by
  cases z with
  | port c i => cases h
  | name w =>
    by_cases hw : w = x
    · subst hw
      rw [End.substName_self] at h
      exact absurd h (hr y)
    · rw [End.substName_of_ne r (fun e => hw (End.name.inj e))] at h
      exact ⟨h, fun e => hw (End.name.inj (h.trans (e ▸ rfl)))⟩

/-- Replacing the name `x` by a port keeps the number of occurrences of the other names. -/
theorem count_map_substName
    -- the erased name `x`, and another name `y`
    {x y : ℕ}
    (hxy : y ≠ x)
    -- what replaces `x`: an end that is not a name
    {r : End ℕ}
    (hr : ∀ w, r ≠ .name w)
    -- the ends
    (M : Multiset (End ℕ)) :
    (M.map (End.substName x r)).count (.name y) = M.count (.name y) := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro z _
  constructor
  · intro h
    exact (substName_eq_name hr h.symm).1.symm
  · rintro rfl
    exact (End.substName_of_ne r fun e => hxy (End.name.inj e)).symm

/-- **Erasing the names of stubs** (Lafont 1997, page 71). A stub is a wire `h e — e` from a name
to a port `e`. If each name `h e` of a stub ends exactly one other wire of `W`, erasing all these
names plugs the ports `e` into the wires of `W`: the result is `W` with each `h e` replaced by
`e`, which is `W` renamed by any `g` that undoes `h` on the ports of the stubs and keeps every
other end of `W`. -/
theorem contracts_stubs
    -- the cells, and the number of cyclic wires
    (C : Multiset (ℕ × S.Sym))
    (n : ℕ)
    -- the names `h e` of the stubs
    (h : End ℕ → ℕ)
    -- the renaming `g`, which keeps every port
    (g : End ℕ → End ℕ)
    (hgp : ∀ c i, g (.port c i) = .port c i) :
    ∀ (P : Multiset (End ℕ)) (W : Multiset (Sym2 (End ℕ))),
      -- for ports `P`, the ends of the stubs
      (∀ e ∈ P, ∃ c i, e = .port c i) →
      -- whose stubs have distinct names
      (P.map h).Nodup →
      -- `g` undoes `h` on these ports
      (∀ e ∈ P, g (.name (h e)) = e) →
      -- the name of each stub ends exactly one wire of `W`
      (∀ e ∈ P, (W.bind wireEnds).count (.name (h e)) = 1) →
      -- `g` keeps every other name at an end of `W`
      (∀ y, .name y ∈ W.bind wireEnds → g (.name y) ≠ .name y → ∃ e ∈ P, h e = y) →
      -- the stubs with the wires `W` contract to the wires `W` renamed by `g`
      Relation.ReflTransGen Contract
        ⟨C, P.map (fun e => s(.name (h e), e)) + W, n⟩
        ⟨C, W.map (Sym2.map g), n⟩ := by
  intro P
  induction P using Multiset.induction_on with
  | empty =>
    intro W _ _ _ _ h0
    have hW : W.map (Sym2.map g) = W := by
      conv_rhs => rw [← Multiset.map_id W]
      refine Multiset.map_congr rfl fun w hw => ?_
      induction w using Sym2.ind with
      | _ p q =>
        have key : ∀ r ∈ ({p, q} : Multiset (End ℕ)), g r = r := by
          intro r hr
          cases r with
          | port c i => exact hgp c i
          | name y =>
            by_contra hne
            obtain ⟨e, he, -⟩ := h0 y (Multiset.mem_bind.2 ⟨_, hw, by rwa [wireEnds_mk]⟩) hne
            simp at he
        simp only [Sym2.map_mk, id]
        rw [key p (by simp), key q (by simp)]
    rw [Multiset.map_zero, zero_add, hW]
  | cons e P ih =>
    intro W hP hnd hg h1 h0
    obtain ⟨c, i, rfl⟩ := hP _ (Multiset.mem_cons_self _ _)
    rw [Multiset.map_cons, Multiset.nodup_cons] at hnd
    have hport : ∀ w, (End.port c i : End ℕ) ≠ .name w := fun w e => by cases e
    -- the other stubs do not end at the name of this one
    have hs0 : ((P.map fun e => s(End.name (h e), e)).bind wireEnds).count
        (.name (h (.port c i))) = 0 := by
      refine Multiset.count_eq_zero.2 fun hm => ?_
      obtain ⟨w, hw, hm⟩ := Multiset.mem_bind.1 hm
      obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hw
      rw [wireEnds_mk] at hm
      simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
      rcases hm with hm | hm
      · exact hnd.1 (Multiset.mem_map.2 ⟨e, he, (End.name.inj hm).symm⟩)
      · obtain ⟨d, j, rfl⟩ := hP e (Multiset.mem_cons_of_mem he)
        cases hm
    have hc : (((P.map fun e => s(End.name (h e), e)) + W).bind wireEnds).count
        (.name (h (.port c i))) = 1 := by
      rw [Multiset.add_bind, Multiset.count_add, hs0, zero_add]
      exact h1 _ (Multiset.mem_cons_self _ _)
    have step := contract_substName C _ n _ (.port c i) hc
    rw [Multiset.map_add, map_substName_of_count _ hs0] at step
    have hgs : g ∘ End.substName (h (.port c i)) (.port c i) = g := by
      funext z
      by_cases hz : z = .name (h (.port c i))
      · subst hz
        rw [Function.comp_apply, End.substName_self, hgp, hg _ (Multiset.mem_cons_self _ _)]
      · rw [Function.comp_apply, End.substName_of_ne _ hz]
    have hfin : (W.map (Sym2.map (End.substName (h (.port c i)) (.port c i)))).map (Sym2.map g) =
        W.map (Sym2.map g) := by
      rw [Multiset.map_map]
      congr 1
      funext w
      rw [Function.comp_apply, Sym2.map_map, hgs]
    rw [Multiset.map_cons, Multiset.cons_add]
    refine Relation.ReflTransGen.head step ?_
    rw [← hfin]
    have hW' := bind_wireEnds_map (End.substName (h (.port c i)) (.port c i)) W
    refine ih _ (fun e he => hP e (Multiset.mem_cons_of_mem he)) hnd.2
      (fun e he => hg e (Multiset.mem_cons_of_mem he)) ?_ ?_
    · intro e he
      have hne : h e ≠ h (.port c i) := fun h' => hnd.1 (h' ▸ Multiset.mem_map_of_mem _ he)
      rw [hW', count_map_substName hne hport, h1 _ (Multiset.mem_cons_of_mem he)]
    · intro y hy hgy
      rw [hW'] at hy
      obtain ⟨z, hz, hzy⟩ := Multiset.mem_map.1 hy
      obtain ⟨rfl, hyx⟩ := substName_eq_name hport hzy
      obtain ⟨e, he, rfl⟩ := h0 _ hz hgy
      rcases Multiset.mem_cons.1 he with rfl | he
      · exact absurd rfl hyx
      · exact ⟨e, he, rfl⟩

/-- **Erasing the names of wires `z — z`** (Lafont 1997, page 71): each becomes a cyclic wire. -/
theorem contracts_loops
    -- the cells, and the names `ln j` of the wires `z — z`
    (C : Multiset (ℕ × S.Sym))
    (ln : ℕ → ℕ) :
    -- for `m` wires `ln j — ln j`, `n` cyclic wires and other wires `W`,
    -- erasing the `m` names leaves `W` and `n + m` cyclic wires
    ∀ (m n : ℕ) (W : Multiset (Sym2 (End ℕ))),
      Relation.ReflTransGen Contract
        ⟨C, (Multiset.range m).map (fun j => s(.name (ln j), .name (ln j))) + W, n⟩
        ⟨C, W, n + m⟩
  | 0, n, W => by simpa using Relation.ReflTransGen.refl
  | m + 1, n, W => by
    rw [Multiset.range_succ, Multiset.map_cons, Multiset.cons_add]
    have := contracts_loops C ln m (n + 1) W
    rw [show n + 1 + m = n + (m + 1) by omega] at this
    exact Relation.ReflTransGen.head (Contract.loop _ C _ n) this

-- ============================================================================================
-- 2. The stubs of some cells
-- ============================================================================================

/-- The ports of some cells. -/
theorem mem_bind_cellPorts
    -- the cells, and a port `i` of the cell numbered `c`
    {C : Multiset (ℕ × S.Sym)}
    {c i : ℕ} :
    -- it is a port of the cells iff `c` is a cell of symbol `α` and `i ≤ arity α`
    (End.port c i : End ℕ) ∈ C.bind cellPorts ↔ ∃ α, (c, α) ∈ C ∧ i ≤ S.arity α := by
  constructor
  · intro hm
    obtain ⟨p, hp, hm⟩ := Multiset.mem_bind.1 hm
    obtain ⟨j, e, hj⟩ := mem_cellPorts hm
    obtain ⟨rfl, rfl⟩ := End.port.inj e
    exact ⟨p.2, hp, hj⟩
  · rintro ⟨α, hα, hi⟩
    refine Multiset.mem_bind.2 ⟨(c, α), hα, ?_⟩
    simp only [cellPorts, Multiset.mem_map, Multiset.mem_range]
    exact ⟨i, by omega, rfl⟩

/-- A name is not a port of a cell (Lafont 1997, page 71). -/
theorem name_notMem_bind_cellPorts
    -- the cells, and a name
    (C : Multiset (ℕ × S.Sym))
    (x : ℕ) :
    (End.name x : End ℕ) ∉ C.bind cellPorts := by
  intro hm
  obtain ⟨p, -, hm⟩ := Multiset.mem_bind.1 hm
  obtain ⟨j, e, -⟩ := mem_cellPorts hm
  cases e

/-- The ports of cells with distinct numbers are distinct. -/
theorem nodup_bind_cellPorts
    -- the cells, with distinct numbers
    {C : Multiset (ℕ × S.Sym)}
    (h : (C.map Prod.fst).Nodup) :
    (C.bind cellPorts : Multiset (End ℕ)).Nodup := by
  induction C using Multiset.induction_on with
  | empty => simp
  | cons p C ih =>
    rw [Multiset.map_cons, Multiset.nodup_cons] at h
    rw [Multiset.cons_bind, Multiset.nodup_add]
    refine ⟨?_, ih h.2, Multiset.disjoint_left.2 fun hm hm' => ?_⟩
    · exact (Multiset.nodup_range _).map fun a b e => (End.port.inj e).2
    · obtain ⟨j, rfl, -⟩ := mem_cellPorts hm
      obtain ⟨α, hα, -⟩ := mem_bind_cellPorts.1 hm'
      exact h.1 (Multiset.mem_map.2 ⟨_, hα, rfl⟩)

/-- The graph of the stubs of some cells: the cells, and a wire `pn c i — port c i` for each
port of each cell. -/
def cellGraph
    -- the names of the ports, and the cells
    (pn : ℕ → ℕ → ℕ)
    (C : Multiset (ℕ × S.Sym)) :
    Graph S ℕ :=
  ⟨C, (C.bind cellPorts).map (fun e => s(.name (e.flatName pn), e)), 0⟩

/-- The equation of a cell in the flat text, as a pair of trees. -/
def cellPair
    -- the names of the ports, and a cell: its number and its symbol
    (pn : ℕ → ℕ → ℕ)
    (p : ℕ × S.Sym) :
    Term S ℕ × Term S ℕ :=
  (var (pn p.1 0), app p.2 fun i => var (pn p.1 ((i : ℕ) + 1)))

/-- Every port at an end of a wire of the stubs of some cells is a port of one of these cells
(Lafont 1997, page 71). -/
theorem cellGraph_portsIn
    -- the names of the ports, and the cells
    (pn : ℕ → ℕ → ℕ)
    (C : Multiset (ℕ × S.Sym))
    -- a port at an end of a wire of the stubs
    (c i : ℕ)
    (hm : End.port c i ∈ (cellGraph pn C).ends) :
    -- its cell is one of the cells
    c ∈ (cellGraph pn C).cells.map Prod.fst := by
  rw [ends_eq_bind] at hm
  obtain ⟨w, hw, hm⟩ := Multiset.mem_bind.1 hm
  obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hw
  rw [wireEnds_mk] at hm
  simp only [Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton] at hm
  rcases hm with hm | rfl
  · cases hm
  · obtain ⟨α, hα, -⟩ := mem_bind_cellPorts.1 he
    exact Multiset.mem_map.2 ⟨_, hα, rfl⟩

/-- The values of `f` on `0, …, n`: `f 0`, then the others as a sum over `Fin n`. -/
private theorem range_succ_map''
    {β : Type}
    (f : ℕ → β)
    (n : ℕ) :
    (Multiset.range (n + 1)).map f = f 0 ::ₘ ∑ i : Fin n, {f ((i : ℕ) + 1)} := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.range_succ, Multiset.map_cons, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [Multiset.cons_swap, ← Multiset.singleton_add, ← Multiset.singleton_add,
      ← Multiset.singleton_add]
    abel

/-- The raw graph of the equation of one cell is isomorphic to its stubs. -/
theorem cellGraph_single_iso
    -- the names of the ports, a cell, and the number given to the cell in the raw graph
    (pn : ℕ → ℕ → ℕ)
    (p : ℕ × S.Sym)
    (k : ℕ) :
    (cellGraph pn {p}).Iso (raw k [cellPair pn p]) := by
  refine ⟨fun _ => k, ?_, ?_, ?_, rfl⟩
  · intro a ha b hb _
    simp only [cellGraph, Multiset.map_singleton, Multiset.mem_singleton] at ha hb
    rw [ha, hb]
  · simp [cellGraph, raw, cellPair, rawCells, size]
    rfl
  · simp only [cellGraph, Multiset.singleton_bind, cellPorts, Multiset.map_map]
    rw [range_succ_map'']
    simp [raw, cellPair, rawWires, rootEnd, size, End.mapCell, Sym2.eq_swap]

/-- **The raw graph of the equations of some cells is isomorphic to their stubs** (Lafont 1997,
page 71), when the cells have distinct numbers. -/
theorem cellGraph_iso
    -- the names of the ports
    (pn : ℕ → ℕ → ℕ) :
    -- for a list of cells with distinct numbers, and the first number `k` of the raw graph,
    ∀ (cl : List (ℕ × S.Sym)) (k : ℕ),
      (cl.map Prod.fst).Nodup →
      -- the stubs of the cells are isomorphic to the raw graph of their equations
      (cellGraph pn (cl : Multiset (ℕ × S.Sym))).Iso
        (raw k (cl.map (cellPair pn)))
  | [], k, _ => by
    have : cellGraph pn ((([] : List (ℕ × S.Sym)) : Multiset (ℕ × S.Sym))) = raw k [] := by
      simp [cellGraph, raw]
    rw [List.map_nil, this]
    exact Iso.refl _
  | p :: cl, k, hnd => by
    have e1 : cellGraph pn ((p :: cl : List (ℕ × S.Sym)) : Multiset (ℕ × S.Sym)) =
        (cellGraph pn {p}).union (cellGraph pn cl) := by
      simp [cellGraph, union, ← Multiset.cons_coe, Multiset.cons_bind]
    have hs : rawSize [cellPair pn p] = 1 := by simp [rawSize, cellPair, size]
    have e2 : raw k ((p :: cl).map (cellPair pn)) =
        (raw k [cellPair pn p]).union (raw (k + 1) (cl.map (cellPair pn))) := by
      rw [List.map_cons, show cellPair pn p :: cl.map (cellPair pn) =
        [cellPair pn p] ++ cl.map (cellPair pn) from rfl, raw_append, hs]
    rw [e1, e2]
    rw [List.map_cons, List.nodup_cons] at hnd
    refine (cellGraph_single_iso pn p k).union (cellGraph_iso pn cl (k + 1) hnd.2)
      (cellGraph_portsIn pn _) (cellGraph_portsIn pn _) ?_ ?_
    · intro c hc hc'
      simp only [cellGraph, Multiset.map_singleton, Multiset.mem_singleton] at hc
      subst hc
      exact hnd.1 (by simpa [cellGraph] using hc')
    · intro c hc hc'
      rw [mem_raw_fst, hs] at hc
      rw [mem_raw_fst] at hc'
      omega

-- ============================================================================================
-- 3. Equations between names
-- ============================================================================================

/-- The raw graph of equations between names: one wire between names for each equation. -/
theorem raw_names :
    -- for the first number `k` of the raw graph and a list `l` of pairs of names,
    -- the raw graph of the equations `x = y` has no cell, a wire `x — y` for each pair,
    -- and no cyclic wire
    ∀ (k : ℕ) (l : List (ℕ × ℕ)),
      raw k (l.map fun q => ((var q.1 : Term S ℕ), (var q.2 : Term S ℕ))) =
        ⟨0,
          ((l.map fun q => s(End.name q.1, End.name q.2) : List (Sym2 (End ℕ))) :
            Multiset (Sym2 (End ℕ))),
          0⟩
  | _, [] => rfl
  | k, q :: l => by
    have ih : raw k (l.map fun q => ((var q.1 : Term S ℕ), (var q.2 : Term S ℕ))) = _ :=
      raw_names k l
    simp only [List.map_cons, raw, size, add_zero, ih, rawCells, rawWires, rootEnd]
    simp

/-- Every multiset of unordered pairs is a list of ordered pairs. -/
private theorem exists_list_sym2
    -- a multiset of unordered pairs
    {α : Type}
    (M : Multiset (Sym2 α)) :
    -- it is the image of a list of ordered pairs
    ∃ l : List (α × α),
      ((l.map fun q => s(q.1, q.2) : List (Sym2 α)) : Multiset (Sym2 α)) = M := by
  induction M using Multiset.induction_on with
  | empty => exact ⟨[], rfl⟩
  | cons e M ih =>
    obtain ⟨l, rfl⟩ := ih
    induction e using Sym2.ind with
    | _ a b => exact ⟨(a, b) :: l, rfl⟩

-- ============================================================================================
-- 4. Fresh names for the ports and the cyclic wires
-- ============================================================================================

/-- A bound above the free ports of a graph. -/
def freeBound
    (G : Graph S ℕ) :
    ℕ :=
  G.free.sup + 1

/-- The free ports are the names at the ends of the wires. -/
theorem mem_free
    -- a graph, and a name
    {G : Graph S ℕ}
    {x : ℕ} :
    x ∈ G.free ↔ End.name x ∈ G.ends := by
  simp only [free, Multiset.mem_filterMap]
  constructor
  · rintro ⟨e, he, hx⟩
    cases e with
    | name y =>
      simp only [Option.some.injEq] at hx
      exact hx ▸ he
    | port _ _ => simp at hx
  · intro h
    exact ⟨_, h, rfl⟩

/-- Every free port of a graph is below `freeBound` (Lafont 1997, page 71). -/
theorem lt_freeBound
    -- a graph, and a name at an end of one of its wires
    {G : Graph S ℕ}
    {x : ℕ}
    (h : End.name x ∈ G.ends) :
    x < freeBound G :=
  Nat.lt_succ_of_le (Multiset.le_sup (mem_free.2 h))

/-- The name of the port `i` of the cell `c` in the flat text: `B + 2 ⟨c, i⟩`. -/
def realPn
    -- the bound, and the port `i` of the cell `c`
    (B : ℕ)
    (c i : ℕ) :
    ℕ :=
  B + 2 * Nat.pair c i

/-- The name of the `j`-th cyclic wire in the flat text: `B + 2 j + 1`. -/
def realLn
    -- the bound, and the number of the cyclic wire
    (B : ℕ)
    (j : ℕ) :
    ℕ :=
  B + 2 * j + 1

/-- Distinct cyclic wires get distinct names (Lafont 1997, page 71). -/
theorem realLn_injective
    (B : ℕ) :
    Function.Injective (realLn B) := fun a b e => by
  simp only [realLn] at e
  omega

/-- Reading a name of the flat text back as an end: `B + 2 ⟨c, i⟩` is the port `i` of `c`, and
every other name is itself. -/
def unflat
    (B : ℕ) :
    End ℕ → End ℕ
  | .port c i => .port c i
  | .name y => if B ≤ y ∧ (y - B) % 2 = 0 then
      .port (Nat.unpair ((y - B) / 2)).1 (Nat.unpair ((y - B) / 2)).2 else .name y

/-- `unflat` reads the name of a port back as that port (Lafont 1997, page 71). -/
theorem unflat_pn
    -- the bound, and the port `i` of the cell `c`
    (B c i : ℕ) :
    unflat B (.name (realPn B c i)) = .port c i := by
  have h : B + 2 * Nat.pair c i - B = 2 * Nat.pair c i := by omega
  simp [unflat, realPn, h]

/-- `unflat` keeps a name below the bound (Lafont 1997, page 71). -/
theorem unflat_low
    -- the bound, and a name below it
    {B y : ℕ}
    (h : y < B) :
    unflat B (.name y) = .name y := by
  simp only [unflat]
  split_ifs with h'
  · omega
  · rfl

/-- `unflat` keeps the name of a cyclic wire (Lafont 1997, page 71). -/
theorem unflat_ln
    -- the bound, and the number of the cyclic wire
    (B j : ℕ) :
    unflat B (.name (realLn B j)) = .name (realLn B j) := by
  have h : ¬(B ≤ realLn B j ∧ (realLn B j - B) % 2 = 0) := by
    simp only [realLn]
    omega
  exact ite_eq_right_of_eq_false _ _ (eq_false h)

/-- `unflat` undoes the naming of the flat text on the ends whose names are below `B`. -/
theorem unflat_flatName
    -- the bound, and an end whose name, if it is a name, is below it
    {B : ℕ}
    {e : End ℕ}
    (he : ∀ x, e = .name x → x < B) :
    unflat B (.name (e.flatName (realPn B))) = e := by
  cases e with
  | port c i => exact unflat_pn B c i
  | name x => exact unflat_low (he x rfl)

/-- A map with a left inverse on a multiset keeps the number of occurrences. -/
private theorem count_map_of_leftInv
    -- two types with decidable equality
    {α β : Type}
    [DecidableEq α]
    [DecidableEq β]
    -- a map `f`, and a left inverse `g` of it on the multiset `E`
    {f : α → β}
    {g : β → α}
    {E : Multiset α}
    (hE : ∀ a ∈ E, g (f a) = a)
    -- an element on which `g` is also a left inverse of `f`
    {a : α}
    (ha : g (f a) = a) :
    -- `f a` occurs in the image as often as `a` in `E`
    (E.map f).count (f a) = E.count a := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro b hb
  constructor
  · intro h
    rw [← ha, h, hE b hb]
  · rintro rfl
    rfl

/-- The names of the cyclic wires of the flat text, each twice. -/
theorem vars_flatLoops
    -- the names of the cyclic wires, and their number
    (ln : ℕ → ℕ)
    (n : ℕ) :
    (flatLoops (S := S) ln n).vars
      = (Multiset.range n).map ln + (Multiset.range n).map ln := by
  induction n with
  | zero => simp [flatLoops]
  | succ n ih =>
    simp only [flatLoops] at ih ⊢
    rw [Multiset.range_succ, Multiset.map_cons, Net.vars_cons, ih, Multiset.map_cons]
    simp only [eqVars_mk, vars_var, Multiset.cons_add, Multiset.add_cons, Multiset.singleton_add]

-- ============================================================================================
-- 5. The names of the flat text of a well-formed graph
-- ============================================================================================

section flat

-- the graph
variable {G : Graph S ℕ}

/-- The flat text of `G` with the names of `realPn` and `realLn` above the free ports. -/
noncomputable abbrev flatB
    (G : Graph S ℕ) :
    Net S ℕ :=
  flat (realPn (freeBound G)) (realLn (freeBound G)) G

/-- **How often a name occurs in the flat text of a well-formed graph** (Lafont 1997, page 71).
A name below the bound occurs as often as it ends wires of `G`; a name above it is the name of a
port or of a cyclic wire, and occurs twice or not at all. -/
theorem count_vars_flatB
    -- the graph is well formed
    (hG : G.WF)
    -- a name
    (y : ℕ) :
    -- either the name is below the bound and occurs as often as it ends wires of `G`,
    (y < freeBound G ∧ (flatB G).vars.count y = G.ends.count (.name y))
    -- or it is above the bound and occurs not at all or twice
    ∨ (freeBound G ≤ y ∧ ((flatB G).vars.count y = 0 ∨ (flatB G).vars.count y = 2)) := by
  have hB : ∀ x, End.name x ∈ G.ends → x < freeBound G := fun x hx => lt_freeBound hx
  simp only [flatB]
  generalize hb : freeBound G = B at hB ⊢
  rw [vars_flat, vars_flatLoops, Multiset.count_add, Multiset.count_add]
  have hE : ∀ e ∈ G.cells.bind cellPorts + G.ends,
      unflat B (.name (e.flatName (realPn B))) = e := by
    intro e he
    refine unflat_flatName fun x hx => ?_
    subst hx
    rcases Multiset.mem_add.1 he with he | he
    · exact absurd he (name_notMem_bind_cellPorts _ _)
    · exact hB x he
  have hcnt : ∀ e, unflat B (.name (e.flatName (realPn B))) = e →
      ((G.cells.bind cellPorts + G.ends).map (End.flatName (realPn B))).count
        (e.flatName (realPn B)) = (G.cells.bind cellPorts + G.ends).count e :=
    fun e he => count_map_of_leftInv (g := fun y => unflat B (.name y)) hE he
  by_cases hy : y < B
  · left
    refine ⟨hy, ?_⟩
    have h0 : ((Multiset.range G.loops).map (realLn B)).count y = 0 :=
      Multiset.count_eq_zero.2 fun hm => by
        obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hm
        simp only [realLn] at hj
        omega
    have h1 := hcnt (.name y) (unflat_low hy)
    simp only [End.flatName_name] at h1
    rw [h0, h1, Multiset.count_add, Multiset.count_eq_zero.2 (name_notMem_bind_cellPorts _ _)]
    simp
  · right
    refine ⟨by omega, ?_⟩
    by_cases hpar : (y - B) % 2 = 0
    · obtain ⟨c, i, hci⟩ : ∃ c i, y = realPn B c i :=
        ⟨(Nat.unpair ((y - B) / 2)).1, (Nat.unpair ((y - B) / 2)).2, by
          simp only [realPn, Nat.pair_unpair]
          omega⟩
      have h0 : ((Multiset.range G.loops).map (realLn B)).count y = 0 :=
        Multiset.count_eq_zero.2 fun hm => by
          obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hm
          simp only [realLn] at hj
          omega
      have h1 := hcnt (.port c i) (unflat_pn B c i)
      simp only [End.flatName_port] at h1
      rw [h0, ← hci] at *
      rw [h1, Multiset.count_add]
      by_cases hc : ∃ α, (c, α) ∈ G.cells ∧ i ≤ S.arity α
      · right
        obtain ⟨α, hα, hi⟩ := hc
        rw [Multiset.count_eq_one_of_mem (nodup_bind_cellPorts hG.nodup)
          (mem_bind_cellPorts.2 ⟨α, hα, hi⟩), hG.port c α hα i hi]
      · left
        rw [Multiset.count_eq_zero.2 fun hm => hc (mem_bind_cellPorts.1 hm),
          Multiset.count_eq_zero.2 fun hm => hc (hG.cell c i hm)]
    · have h0 : ((G.cells.bind cellPorts + G.ends).map (End.flatName (realPn B))).count y = 0 :=
        Multiset.count_eq_zero.2 fun hm => by
          obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hm
          cases e with
          | port c i =>
            simp only [End.flatName_port, realPn] at hpar
            omega
          | name x =>
            rcases Multiset.mem_add.1 he with he | he
            · exact name_notMem_bind_cellPorts _ _ he
            · exact hy (hB x he)
      have hy' : y = realLn B ((y - B) / 2) := by
        simp only [realLn]
        omega
      rw [h0, hy', Multiset.count_map_eq_count' _ _ (realLn_injective B),
        Multiset.count_eq_of_nodup (Multiset.nodup_range _)]
      split_ifs <;> simp

/-- **The flat text of a well-formed graph is linear** (Lafont 1997, page 71). -/
theorem linear_flatB
    -- the graph is well formed
    (hG : G.WF) :
    (flatB G).Linear := fun y => by
  rcases count_vars_flatB hG y with ⟨-, h⟩ | ⟨-, h | h⟩ <;> rw [h]
  · exact (hG.name y).trans (by omega)
  · omega

/-- **The free ports of the flat text are those of the graph** (Lafont 1997, page 71): a name
occurs once in the flat text of a well-formed graph `G` if and only if it is a free port of `G`. -/
theorem count_vars_flatB_eq_one
    -- the graph is well formed
    (hG : G.WF)
    -- a name
    (y : ℕ) :
    (flatB G).vars.count y = 1 ↔ y ∈ G.free := by
  rw [mem_free]
  rcases count_vars_flatB hG y with ⟨-, h⟩ | ⟨hy, h⟩
  · rw [h]
    have := hG.name y
    constructor
    · intro h1
      exact Multiset.count_pos.1 (by omega)
    · intro hm
      have := Multiset.count_pos.2 hm
      omega
  · constructor
    · intro h1
      omega
    · intro hm
      have := lt_freeBound hm
      omega

end flat

-- ============================================================================================
-- 6. Main results
-- ============================================================================================

/-- **The flat text of a well-formed graph has a graph isomorphic to it** (Lafont 1997,
Section 1.1, page 71): the raw graph of the flat text, contracted, is `G` up to `Iso`. -/
theorem WF.hasGraph_flatB
    -- a well-formed graph
    {G : Graph S ℕ}
    (h : G.WF) :
    -- its flat text has a graph `G'`, isomorphic to `G`
    ∃ G' : Graph S ℕ,
      (flatB G).HasGraph G'
      ∧ G'.Iso G := by
  have hB : ∀ x, End.name x ∈ G.ends → x < freeBound G := fun x hx => lt_freeBound hx
  suffices H : ∃ L : List (Term S ℕ × Term S ℕ), Net.ofList L = flatB G ∧
      ∃ H, Relation.ReflTransGen Contract (raw 0 L) H ∧ G.Iso H by
    obtain ⟨L, hL, H, hH, iH⟩ := H
    exact ⟨H, ⟨L, 0, hL.symm, hH, fun x => (iH.count_name x).trans_le (h.name x)⟩,
      iH.symm h.portsIn⟩
  simp only [flatB]
  generalize hb : freeBound G = B at hB
  -- the text: the equations of the cells, of the wires and of the cyclic wires
  obtain ⟨lw, hlw⟩ := exists_list_sym2 G.wires
  let pn := realPn B
  let ln := realLn B
  let cl := G.cells.toList
  let lv : List (ℕ × ℕ) := lw.map (fun q => (q.1.flatName pn, q.2.flatName pn)) ++
    (List.range G.loops).map (fun j => (ln j, ln j))
  let L := cl.map (cellPair pn) ++ lv.map (fun q => ((var q.1 : Term S ℕ), (var q.2 : Term S ℕ)))
  -- the wires between names in the raw graph
  let Wn : Multiset (Sym2 (End ℕ)) := G.wires.map (Sym2.map fun e => .name (e.flatName pn))
  let Lp : Multiset (Sym2 (End ℕ)) :=
    (Multiset.range G.loops).map (fun j => s(End.name (ln j), End.name (ln j)))
  have hlv : ((lv.map fun q => s(End.name q.1, End.name q.2) : List (Sym2 (End ℕ))) :
      Multiset (Sym2 (End ℕ))) = Wn + Lp := by
    simp only [lv, Wn, Lp, ← hlw, List.map_append, List.map_map, ← Multiset.coe_add,
      Multiset.map_coe, Multiset.range]
    rfl
  refine ⟨L, ?_, ?_⟩
  · simp only [L, lv, Net.ofList, List.map_append, List.map_map, ← Multiset.coe_add, flat,
      flatCells, flatWires, flatLoops, ← hlw, Multiset.map_coe, Multiset.range]
    rw [← Multiset.coe_toList G.cells, Multiset.map_coe]
    rw [add_assoc]
    rfl
  -- the graph of the stubs, isomorphic to the raw graph
  let P : Multiset (End ℕ) := G.cells.bind cellPorts
  let R : Graph S ℕ := ⟨G.cells, P.map (fun e => s(.name (e.flatName pn), e)) + (Wn + Lp), 0⟩
  have hR : R.Iso (raw 0 L) := by
    have e1 : raw 0 L = (raw 0 (cl.map (cellPair pn))).union ⟨0, Wn + Lp, 0⟩ := by
      rw [raw_append, raw_names, hlv]
    have e2 : R = (cellGraph pn (cl : Multiset (ℕ × S.Sym))).union ⟨0, Wn + Lp, 0⟩ := by
      simp [R, P, cellGraph, union, cl]
    have hnd : (cl.map Prod.fst).Nodup := by
      rw [← Multiset.coe_nodup, ← Multiset.map_coe, Multiset.coe_toList]
      exact h.nodup
    rw [e1, e2]
    refine (cellGraph_iso pn cl 0 hnd).union (Iso.refl _) (cellGraph_portsIn pn _) ?_
      (by simp) (by simp)
    intro c i hm
    exfalso
    rw [ends_eq_bind] at hm
    change End.port c i ∈ (Wn + Lp).bind wireEnds at hm
    rw [Multiset.add_bind, Multiset.mem_add, bind_wireEnds_map] at hm
    rcases hm with hm | hm
    · obtain ⟨e, -, he⟩ := Multiset.mem_map.1 hm
      cases he
    · obtain ⟨w, hw, hm⟩ := Multiset.mem_bind.1 hm
      obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hw
      simp at hm
  -- the stubs contract to the graph
  have hPp : ∀ e ∈ P, ∃ c i, e = .port c i := fun e he => by
    obtain ⟨p, -, hp⟩ := Multiset.mem_bind.1 he
    obtain ⟨i, rfl, -⟩ := mem_cellPorts hp
    exact ⟨_, _, rfl⟩
  have hun : ∀ e ∈ G.ends, unflat B (.name (e.flatName pn)) = e := fun e he =>
    unflat_flatName fun x hx => hB x (hx ▸ he)
  have hLp : ∀ y, End.name y ∈ Lp.bind wireEnds → ∃ j, y = ln j := fun y hm => by
    obtain ⟨w, hw, hm⟩ := Multiset.mem_bind.1 hm
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hw
    simp only [wireEnds_mk, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton,
      End.name.injEq, or_self] at hm
    exact ⟨j, hm⟩
  have hWn : Wn.bind wireEnds = G.ends.map (fun e => .name (e.flatName pn)) :=
    bind_wireEnds_map _ _
  have hA := contracts_stubs G.cells 0 (End.flatName pn) (unflat B) (fun _ _ => rfl) P (Wn + Lp)
    hPp
    ((nodup_bind_cellPorts h.nodup).map_on fun e he e' he' hee => by
      obtain ⟨c, i, rfl⟩ := hPp e he
      obtain ⟨d, j, rfl⟩ := hPp e' he'
      simp only [End.flatName_port, pn, realPn] at hee
      obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 (by omega : Nat.pair c i = Nat.pair d j)
      rfl)
    (fun e he => by
      obtain ⟨c, i, rfl⟩ := hPp e he
      exact unflat_pn B c i)
    (fun e he => by
      obtain ⟨c, i, rfl⟩ := hPp e he
      obtain ⟨α, hα, hi⟩ := mem_bind_cellPorts.1 he
      rw [Multiset.add_bind, Multiset.count_add, hWn,
        count_map_of_leftInv (f := fun e => End.name (e.flatName pn)) (g := unflat B) hun
          (unflat_pn B c i), h.port c α hα i hi, Multiset.count_eq_zero.2]
      intro hm
      obtain ⟨j, hj⟩ := hLp _ hm
      simp only [End.flatName_port, pn, ln, realPn, realLn] at hj
      omega)
    (fun y hy hgy => by
      rw [Multiset.add_bind, Multiset.mem_add, hWn] at hy
      rcases hy with hy | hy
      · obtain ⟨e, he, hey⟩ := Multiset.mem_map.1 hy
        cases e with
        | port c i =>
          exact ⟨_, mem_bind_cellPorts.2 (h.cell c i he), End.name.inj hey⟩
        | name x =>
          cases hey
          exact absurd (unflat_low (hB x he)) hgy
      · obtain ⟨j, rfl⟩ := hLp y hy
        exact absurd (unflat_ln B j) hgy)
  have e3 : (Wn + Lp).map (Sym2.map (unflat B)) = Lp + G.wires := by
    rw [Multiset.map_add, add_comm]
    congr 1
    · simp only [Lp, Multiset.map_map]
      refine Multiset.map_congr rfl fun j _ => ?_
      simp only [Function.comp_apply, Sym2.map_mk, ln, unflat_ln]
    · simp only [Wn, Multiset.map_map]
      conv_rhs => rw [← Multiset.map_id G.wires]
      refine Multiset.map_congr rfl fun w hw => ?_
      induction w using Sym2.ind with
      | _ p q =>
        have hp : p ∈ G.ends := Multiset.mem_bind.2 ⟨_, hw, by simp⟩
        have hq : q ∈ G.ends := Multiset.mem_bind.2 ⟨_, hw, by simp⟩
        simp only [Function.comp_apply, Sym2.map_mk, hun p hp, hun q hq, id]
  rw [e3] at hA
  have hC := contracts_loops G.cells ln G.loops 0 G.wires
  rw [zero_add] at hC
  obtain ⟨H, hH, iH⟩ := hR.contracts (hA.trans hC)
  exact ⟨H, hH, iH⟩

/-- **Every well-formed graph is the graph of a linear net, with the same free ports** (Lafont
1997, Section 1.1, page 71). If `G` is well formed, its flat text `N` is linear, has a graph
isomorphic to `G`, and a name occurs once in `N` exactly when it is a free port of `G`. -/
theorem WF.exists_net_free
    -- a well-formed graph
    {G : Graph S ℕ}
    (h : G.WF) :
    -- there are a net `N` and a graph `G'` such that
    ∃ (N : Net S ℕ) (G' : Graph S ℕ),
      -- `N` is linear,
      N.Linear
      -- `G'` is the graph of `N`,
      ∧ N.HasGraph G'
      -- `G'` is isomorphic to `G`,
      ∧ G'.Iso G
      -- and the names that occur once in `N` are the free ports of `G`
      ∧ ∀ x, N.vars.count x = 1 ↔ x ∈ G.free := by
  obtain ⟨G', hG', iG⟩ := h.hasGraph_flatB
  exact ⟨flatB G, G', linear_flatB h, hG', iG, count_vars_flatB_eq_one h⟩

/-- **Every well-formed graph is the graph of a linear net** (Lafont 1997, Section 1.1, page 71).
The graph of the net is isomorphic to `G`, not equal: the cells of the graph of a net are
numbered in the order of its text. -/
theorem WF.exists_net
    -- a well-formed graph
    {G : Graph S ℕ}
    (h : G.WF) :
    -- there are a net `N` and a graph `G'` such that
    ∃ (N : Net S ℕ) (G' : Graph S ℕ),
      -- `N` is linear,
      N.Linear
      -- `G'` is the graph of `N`,
      ∧ N.HasGraph G'
      -- and `G'` is isomorphic to `G`
      ∧ G'.Iso G := by
  obtain ⟨N, G', h1, h2, h3, -⟩ := h.exists_net_free
  exact ⟨N, G', h1, h2, h3⟩

end Graph

end INet
