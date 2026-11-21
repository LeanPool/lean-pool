/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Core.Graph
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The raw graph of a text

Facts about `Graph.raw`, the graph read off a list of equations (Lafont 1997, Section 1.1,
pages 71 and 72: a net is described by its cells, its free ports and its wires, and the wires
form a partition of the ports). They give the fields of `Graph.WF` for the raw graph.

Contents, in the order of the file:

1. Definitions: `wireEnds`, the ends of a wire, with `wireEnds_mk` and `ends_eq_bind`;
   `cellPorts`, the ports of a cell; `rawSize`, the number of cells of the trees of a list of
   equations.
2. Auxiliary lemmas on finite sums of multisets: `bind_finsum`, `map_finsum`, `range_succ_map`,
   `sum_Ico_blocks`, `cons_Ico`.
3. Auxiliary lemmas on texts and trees: `Net.ofList_cons`; `Term.rawCells_fst`, the cells of a
   tree are numbered consecutively; `Term.rootEnd_cons_rawWires`, the ends of the wires of a
   tree.
4. Auxiliary lemmas on ports and names: `name_notMem_cellPorts`, `port_notMem_names`,
   `count_cellPorts`.
5. Main results on the raw graph `Graph.raw k L`:
   - `raw_cells_fst`: its cells are numbered `k, k + 1, …, k + n - 1`, with `n` the number of
     cells of the trees of `L`; so the numbers are distinct (`raw_nodup`), and there is no
     cyclic wire (`raw_loops`);
   - `raw_ends`: the ends of its wires are the ports of its cells, each once, and the names of
     `L`, each as many times as it occurs;
   - `raw_port`, `raw_cell`: the fields `port` and `cell` of `Graph.WF`;
   - `raw_count_name`: a name ends as many wires as it has occurrences, and so at most two
     when the text is linear (`raw_count_name_le_two`).
-/

@[expose] public section

namespace INet

variable {S : Signature} {ν : Type}

namespace Graph

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- The ends of one wire, with multiplicity. -/
def wireEnds :
    Sym2 (End ν) → Multiset (End ν) :=
  Sym2.lift ⟨fun p q => {p, q}, fun p q => Multiset.pair_comm p q⟩

-- the ends of the wire between `p` and `q` are `p` and `q`
@[simp] theorem wireEnds_mk
    (p q : End ν) :
    wireEnds s(p, q) = {p, q} := rfl

-- the ends of a graph are the ends of its wires
theorem ends_eq_bind
    (G : Graph S ν) :
    G.ends = G.wires.bind wireEnds := rfl

/-- The ports of a cell: its principal port `0` and its auxiliary ports `1, …, arity`. -/
def cellPorts
    -- the cell: its number and its symbol
    (p : ℕ × S.Sym) :
    Multiset (End ν) :=
  (Multiset.range (S.arity p.2 + 1)).map (End.port p.1)

/-- The number of cells of the trees of a list of equations. -/
def rawSize
    (L : List (Term S ν × Term S ν)) :
    ℕ :=
  (L.map fun e => e.1.size + e.2.size).sum

end Graph

-- ============================================================================================
-- 2. Auxiliary lemmas: finite sums of multisets
-- ============================================================================================

-- binding a finite sum of multisets is the sum of the binds
private theorem bind_finsum
    {ι α β : Type}
    -- the finite sum
    (s : Finset ι)
    (g : ι → Multiset α)
    -- the function bound
    (f : α → Multiset β) :
    (∑ i ∈ s, g i).bind f = ∑ i ∈ s, (g i).bind f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

-- mapping a finite sum of multisets is the sum of the maps
private theorem map_finsum
    {ι α β : Type}
    -- the finite sum
    (s : Finset ι)
    (g : ι → Multiset α)
    -- the function mapped
    (f : α → β) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

-- the image of `0, …, n` is the image of `0` and the sum of the images of `1, …, n`
private theorem range_succ_map
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

/-- Consecutive blocks of lengths `f 0, f 1, …` starting at `b` fill an interval. -/
private theorem sum_Ico_blocks :
    -- for the lengths `f` of `n` blocks and a start `b`,
    ∀ (n : ℕ) (f : Fin n → ℕ) (b : ℕ),
      -- the block `i` starts after the blocks before it, and together they fill `[b, b + Σ f)`
      ∑ i : Fin n, Multiset.Ico (b + ∑ j, if j < i then f j else 0)
          (b + (∑ j, if j < i then f j else 0) + f i)
        = Multiset.Ico b (b + ∑ i, f i)
  | 0, f, b => by simp
  | n + 1, f, b => by
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc f]
    have hc : ∀ i : Fin n, (∑ j : Fin (n + 1), if j < i.castSucc then f j else 0) =
        ∑ j : Fin n, if j < i then f j.castSucc else 0 := by
      intro i
      rw [Fin.sum_univ_castSucc]
      simp [Fin.castSucc_lt_castSucc_iff, not_lt.2 (Fin.castSucc_lt_last i).le]
    have hl : (∑ j : Fin (n + 1), if j < Fin.last n then f j else 0) =
        ∑ j : Fin n, f j.castSucc := by
      rw [Fin.sum_univ_castSucc]
      simp [Fin.castSucc_lt_last]
    simp only [hc, hl]
    rw [sum_Ico_blocks n (fun j => f j.castSucc) b, ← add_assoc]
    exact Multiset.Ico_add_Ico_eq_Ico (by omega) (by omega)

-- the interval `[k, m)` is `k` followed by `[k + 1, m)`, when `k < m`
private theorem cons_Ico
    (k m : ℕ)
    (h : k < m) :
    k ::ₘ Multiset.Ico (k + 1) m = Multiset.Ico k m := by
  rw [← Multiset.singleton_add, ← Multiset.Ico_add_Ico_eq_Ico (Nat.le_succ k) h]
  congr 1
  simp [Multiset.Ico, Nat.Ico_succ_singleton]

-- ============================================================================================
-- 3. Auxiliary lemmas: texts and trees
-- ============================================================================================

/-- The text of a list of equations, one equation at a time. -/
theorem Net.ofList_cons
    -- the first equation
    (a b : Term S ν)
    -- the other equations
    (L : List (Term S ν × Term S ν)) :
    Net.ofList ((a, b) :: L) = s(a, b) ::ₘ Net.ofList L := rfl

namespace Term

/-- **The cells of a tree are numbered consecutively** (Lafont 1997, page 72): the numbers of the
cells of `t` numbered from `k` are `k, …, k + t.size - 1`. -/
theorem rawCells_fst
    -- the tree
    (t : Term S ν)
    -- the number of its first cell
    (k : ℕ) :
    (t.rawCells k).map Prod.fst = Multiset.Ico k (k + t.size) := by
  induction t generalizing k with
  | var x => simp [rawCells, size]
  | app α ts ih =>
    simp only [rawCells, size, Multiset.map_cons, map_finsum, ih, childBase]
    rw [sum_Ico_blocks _ (fun i => (ts i).size) (k + 1), ← add_assoc]
    exact cons_Ico _ _ (by omega)

/-- **The ends of the wires of a tree** (Lafont 1997, page 72). The root of `t` together with the
ends of the inner wires of `t` are the ports of the cells of `t`, each once, and the leaves of `t`,
each as many times as it occurs. -/
theorem rootEnd_cons_rawWires
    -- the tree
    (t : Term S ν)
    -- the number of its first cell
    (k : ℕ) :
    -- the root and the ends of the inner wires
    t.rootEnd k ::ₘ (t.rawWires k).bind Graph.wireEnds
      -- are the ports of the cells and the leaves
      = (t.rawCells k).bind Graph.cellPorts + t.vars.map End.name := by
  induction t generalizing k with
  | var x => simp [rootEnd, rawWires, rawCells]
  | app α ts ih =>
    have h : ∀ i : Fin (S.arity α),
        (s(End.port k ((i : ℕ) + 1), (ts i).rootEnd (childBase k ts i)) ::ₘ
          (ts i).rawWires (childBase k ts i)).bind Graph.wireEnds =
        {End.port k ((i : ℕ) + 1)} + (((ts i).rawCells (childBase k ts i)).bind Graph.cellPorts
          + (ts i).vars.map End.name) := by
      intro i
      rw [Multiset.cons_bind, Graph.wireEnds_mk, ← ih i]
      simp only [Multiset.insert_eq_cons, Multiset.cons_add, Multiset.singleton_add,
        Multiset.add_cons]
      exact Multiset.cons_swap _ _ _
    rw [show (app α ts).rawWires k = ∑ i : Fin (S.arity α),
        (s(End.port k ((i : ℕ) + 1), (ts i).rootEnd (childBase k ts i)) ::ₘ
          (ts i).rawWires (childBase k ts i)) from rfl, bind_finsum]
    simp only [h]
    simp only [rootEnd, rawCells, vars_app, Multiset.cons_bind, map_finsum, bind_finsum,
      Finset.sum_add_distrib, Graph.cellPorts, range_succ_map]
    rw [← Multiset.singleton_add, ← Multiset.singleton_add]
    abel

end Term

namespace Graph

-- ============================================================================================
-- 4. Auxiliary lemmas: ports and names
-- ============================================================================================

-- a name is not a port of a cell
private theorem name_notMem_cellPorts
    (x : ν)
    (p : ℕ × S.Sym) :
    End.name x ∉ (cellPorts p : Multiset (End ν)) := by
  simp [cellPorts]

-- a port is not among names
private theorem port_notMem_names
    (c i : ℕ)
    (V : Multiset ν) :
    End.port c i ∉ V.map End.name := by
  simp

section

variable [DecidableEq ν]

-- the port `i` of the cell `c` is a port of the cell `p` once if `p` is `c` and has the port
-- `i`, and not at all otherwise
private theorem count_cellPorts
    -- the port
    (c i : ℕ)
    -- the cell
    (p : ℕ × S.Sym) :
    (cellPorts p : Multiset (End ν)).count (.port c i)
      = if p.1 = c ∧ i ≤ S.arity p.2 then 1 else 0 := by
  unfold cellPorts
  split_ifs with h
  · obtain ⟨h1, h2⟩ := h
    rw [← h1, Multiset.count_map_eq_count' _ _ (fun _ _ h => (End.port.inj h).2)]
    exact Multiset.count_eq_one_of_mem (Multiset.nodup_range _) (Multiset.mem_range.2 (by omega))
  · rw [Multiset.count_eq_zero]
    intro hm
    obtain ⟨j, hj, e⟩ := Multiset.mem_map.1 hm
    obtain ⟨e1, e2⟩ := End.port.inj e
    rw [Multiset.mem_range] at hj
    exact h ⟨e1, by omega⟩

end

-- ============================================================================================
-- 5. Main results: the raw graph of a list of equations
-- ============================================================================================

/-- **The cells of the raw graph are numbered consecutively** (Lafont 1997, page 72): the cells
of `Graph.raw k L` are numbered `k, …, k + n - 1`, where `n` is the number of cells of the trees
of `L`. -/
theorem raw_cells_fst
    -- the number of the first cell
    (k : ℕ)
    -- the list of equations
    (L : List (Term S ν × Term S ν)) :
    (raw k L).cells.map Prod.fst = Multiset.Ico k (k + rawSize L) := by
  induction L generalizing k with
  | nil => simp [raw, rawSize]
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    simp only [raw, Multiset.map_add, Term.rawCells_fst, ih, rawSize, List.map_cons,
      List.sum_cons]
    rw [Multiset.Ico_add_Ico_eq_Ico (by omega) (by omega),
      Multiset.Ico_add_Ico_eq_Ico (by omega) (by omega)]
    congr 1
    omega

/-- **The cells of the raw graph are distinct** (Lafont 1997, page 72): no two cells of
`Graph.raw k L` have the same number. This is the field `nodup` of `Graph.WF`. -/
theorem raw_nodup
    -- the number of the first cell
    (k : ℕ)
    -- the list of equations
    (L : List (Term S ν × Term S ν)) :
    ((raw k L).cells.map Prod.fst).Nodup := by
  rw [raw_cells_fst]
  exact Multiset.nodup_Ico

/-- The raw graph of a text has no cyclic wire (Lafont 1997, pages 71 and 72). -/
theorem raw_loops
    -- the number of the first cell
    (k : ℕ)
    -- the list of equations
    (L : List (Term S ν × Term S ν)) :
    (raw k L).loops = 0 := by
  induction L generalizing k with
  | nil => rfl
  | cons e L ih => exact ih _

/-- **The ends of the wires of the raw graph** (Lafont 1997, page 72): the ports of its cells,
each once, and the names of the text, each as many times as it occurs. -/
theorem raw_ends
    -- the number of the first cell
    (k : ℕ)
    -- the list of equations
    (L : List (Term S ν × Term S ν)) :
    -- the ends of the wires are the ports of the cells and the names of the text
    (raw k L).ends
      = (raw k L).cells.bind cellPorts + (Net.ofList L).vars.map End.name := by
  induction L generalizing k with
  | nil => simp [raw, ends, Net.ofList]
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    have ha := Term.rootEnd_cons_rawWires a k
    have hb := Term.rootEnd_cons_rawWires b (k + a.size)
    have hG := ih (k + a.size + b.size)
    simp only [ends_eq_bind] at hG ⊢
    simp only [raw, Multiset.cons_bind, wireEnds_mk, Multiset.add_bind, Net.ofList_cons,
      Net.vars_cons, eqVars_mk, Multiset.map_add, hG]
    rw [Multiset.insert_eq_cons, ← Multiset.singleton_add]
    rw [← Multiset.singleton_add] at ha hb
    calc _ = ({a.rootEnd k} + (a.rawWires k).bind wireEnds) + ({b.rootEnd (k + a.size)} +
          (b.rawWires (k + a.size)).bind wireEnds) + ((raw (k + a.size + b.size) L).cells.bind
            cellPorts + Multiset.map End.name (Net.ofList L).vars) := by abel
      _ = _ := by rw [ha, hb]; abel

variable [DecidableEq ν]

/-- **Every port of a cell of the raw graph ends exactly one wire** (Lafont 1997, page 72): the
principal port ends the wire from the auxiliary port above it, or the wire of its equation, and
the auxiliary port `i + 1` ends the wire to the root of the `i`-th subtree. This is the field
`port` of `Graph.WF`. -/
theorem raw_port
    -- the raw graph
    (k : ℕ)
    (L : List (Term S ν × Term S ν))
    -- a cell of the raw graph
    (c : ℕ)
    (α : S.Sym)
    (hc : (c, α) ∈ (raw k L).cells)
    -- one of its ports
    (i : ℕ)
    (hi : i ≤ S.arity α) :
    (raw k L).ends.count (.port c i) = 1 := by
  have hnd := raw_nodup k L
  rw [raw_ends, Multiset.count_add, Multiset.count_eq_zero.2 (port_notMem_names _ _ _)]
  obtain ⟨R, hR⟩ := Multiset.exists_cons_of_mem hc
  rw [hR] at hnd ⊢
  rw [Multiset.map_cons, Multiset.nodup_cons] at hnd
  rw [Multiset.cons_bind, Multiset.count_add, count_cellPorts,
    ite_eq_left_of_eq_true _ _ (eq_true ⟨rfl, hi⟩), Multiset.count_eq_zero.2]
  simp only [Multiset.mem_bind, not_exists, not_and]
  intro p hp hm
  have h1 := Multiset.count_pos.2 hm
  rw [count_cellPorts] at h1
  split_ifs at h1 with h2
  · exact hnd.1 (Multiset.mem_map.2 ⟨p, hp, h2.1⟩)
  · exact absurd h1 (by omega)

omit [DecidableEq ν] in
/-- **An end of the raw graph that is a port is a port of one of its cells** (Lafont 1997,
page 72). This is the field `cell` of `Graph.WF`. -/
theorem raw_cell
    -- the raw graph
    (k : ℕ)
    (L : List (Term S ν × Term S ν))
    -- the port `i` of `c` is an end of the raw graph
    (c i : ℕ)
    (h : End.port c i ∈ (raw k L).ends) :
    -- there is a cell `c` of the raw graph, with a symbol `α` that has the port `i`
    ∃ α, (c, α) ∈ (raw k L).cells ∧ i ≤ S.arity α := by
  classical
  rw [raw_ends, Multiset.mem_add] at h
  rcases h with h | h
  · obtain ⟨p, hp, hm⟩ := Multiset.mem_bind.1 h
    have h1 := Multiset.count_pos.2 hm
    rw [count_cellPorts] at h1
    split_ifs at h1 with h2
    · exact ⟨p.2, h2.1 ▸ hp, h2.2⟩
    · exact absurd h1 (by omega)
  · exact absurd h (port_notMem_names _ _ _)

/-- **A name ends as many wires of the raw graph as it has occurrences in the text** (Lafont 1997,
page 72). -/
theorem raw_count_name
    -- the raw graph
    (k : ℕ)
    (L : List (Term S ν × Term S ν))
    -- the name
    (x : ν) :
    (raw k L).ends.count (.name x) = (Net.ofList L).vars.count x := by
  rw [raw_ends, Multiset.count_add, Multiset.count_eq_zero.2, zero_add,
    Multiset.count_map_eq_count' _ _ (fun _ _ h => End.name.inj h)]
  simp only [Multiset.mem_bind, not_exists, not_and]
  exact fun p _ => name_notMem_cellPorts x p

/-- In the raw graph of a linear text, a name ends at most two wires (Lafont 1997, page 72). -/
theorem raw_count_name_le_two
    -- the raw graph of a linear text
    (k : ℕ)
    (L : List (Term S ν × Term S ν))
    (hL : (Net.ofList L).Linear)
    -- the name
    (x : ν) :
    (raw k L).ends.count (.name x) ≤ 2 := by
  rw [raw_count_name]
  exact hL x

end Graph

end INet
