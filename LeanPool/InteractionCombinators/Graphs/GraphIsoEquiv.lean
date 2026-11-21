/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Graphs.GraphEquiv
public import LeanPool.InteractionCombinators.Text.Rename
public import Mathlib.Data.Nat.Pairing

/-!
# Linear nets with isomorphic graphs are equivalent

Lafont 1997, Section 1.1, page 71: a net is a graph, and a text is only one way to write it down.
This file proves the direction "`Iso` implies `Equiv`", and with `Net.Linear.equiv_hasGraph_iso`
the equivalence of the two.

The proof goes through a *flat* text read directly off the graph. Given names `pn c i` for the
ports of the cells and `ln j` for the cyclic wires, `Graph.flat pn ln G` has

* one equation `pn c 0 = α(pn c 1, …, pn c n)` for each cell `c` of symbol `α`,
* one equation between the names of the two ends of each wire, a free port keeping its name,
* one equation `ln j = ln j` for each cyclic wire.

Contents, in the order of the file:

1. Definitions: `End.flatName` (the name of an end in the flat text), `End.flatName_mapCell`;
   `Graph.cellEq`, `Graph.flatCells`, `Graph.flatWire`, `Graph.flatWires`, `Graph.flatLoops`,
   `Graph.flat` (the flat text of a graph), `Graph.flatTree`.
2. The names of the flat text: the private `range_succ_map'` and `map_finsum_flat`,
   `Graph.eqVars_cellEq`, `Graph.vars_flatCells`, `Graph.vars_flatWires`, `Graph.vars_flat`,
   `Graph.mem_vars_flatLoops`, `Graph.mem_cellPorts`.
3. Flattening a tree: `Graph.flatTree_var`, `Graph.flatTree_app`, `Graph.equiv_flatTree` (a tree
   is equivalent to its cells, each in its own equation: each subtree is pulled out of its cell
   by a wire substitution read backwards).
4. Flattening a text: `Graph.flat_raw_cons`, `Graph.equiv_flat_raw` (a text is equivalent to the
   flat text of its raw graph), `Graph.linear_flat_raw`.
5. Erasing a name: `Graph.equiv_loop_rename`, `Graph.equiv_flat_contract` (erasing a name of the
   graph is a wire substitution of the flat text, or renames a cyclic wire),
   `Graph.equiv_flat_of_contracts`.
6. Isomorphic graphs: `Graph.flat_iso`, the flat texts of isomorphic graphs differ by the names of
   the ports.
7. Main results: `Net.Linear.equiv_of_hasGraph_iso`, linear nets whose graphs are isomorphic are
   equivalent; `Net.Linear.equiv_iff_hasGraph_iso`, the equivalence.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

namespace End

/-- The name of an end in the flat text: the port `i` of the cell `c` is called `pn c i`, and a
free port keeps its name. -/
def flatName
    -- the names of the ports of the cells
    (pn : ℕ → ℕ → ℕ) :
    End ℕ → ℕ
  | port c i => pn c i
  | name x => x

/-- The port `i` of the cell `c` is called `pn c i`. -/
@[simp] theorem flatName_port
    (pn : ℕ → ℕ → ℕ)
    (c i : ℕ) :
    flatName pn (port c i) = pn c i := rfl

/-- A free port keeps its name. -/
@[simp] theorem flatName_name
    (pn : ℕ → ℕ → ℕ)
    (x : ℕ) :
    flatName pn (name x) = x := rfl

/-- Renumbering the cells of an end by `σ` is renaming its ports by `pn (σ c) i`. -/
theorem flatName_mapCell
    -- the names of the ports, a renumbering of the cells, and an end
    (pn : ℕ → ℕ → ℕ)
    (σ : ℕ → ℕ)
    (e : End ℕ) :
    flatName pn (mapCell σ e) = flatName (fun c i => pn (σ c) i) e := by
  cases e <;> rfl

end End

namespace Graph

/-- The equation of a cell in the flat text: its principal port against the cell whose
auxiliary ports are all names. -/
def cellEq
    -- the names of the ports, and a cell: its number and its symbol
    (pn : ℕ → ℕ → ℕ)
    (p : ℕ × S.Sym) :
    Sym2 (Term S ℕ) :=
  s(var (pn p.1 0), app p.2 fun i => var (pn p.1 ((i : ℕ) + 1)))

/-- The equations of some cells. -/
def flatCells
    (pn : ℕ → ℕ → ℕ)
    (C : Multiset (ℕ × S.Sym)) :
    Net S ℕ := C.map (cellEq pn)

/-- The equation of a wire: the names of its two ends. -/
def flatWire
    (pn : ℕ → ℕ → ℕ) :
    Sym2 (End ℕ) → Sym2 (Term S ℕ) :=
  Sym2.map fun e => var (e.flatName pn)

/-- The equations of some wires. -/
def flatWires
    (pn : ℕ → ℕ → ℕ)
    (W : Multiset (Sym2 (End ℕ))) :
    Net S ℕ := W.map (flatWire pn)

/-- The equations of `n` cyclic wires, `ln j = ln j` for `j < n`. -/
def flatLoops
    -- the names of the cyclic wires, and their number
    (ln : ℕ → ℕ)
    (n : ℕ) :
    Net S ℕ :=
  (Multiset.range n).map fun j => s(var (ln j), var (ln j))

/-- **The flat text of a graph** (Lafont 1997, page 71): one equation for each cell, each wire and
each cyclic wire, the ports of the cells named by `pn` and the cyclic wires by `ln`. -/
def flat
    -- the names of the ports and of the cyclic wires
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ)
    -- a graph
    (G : Graph S ℕ) :
    Net S ℕ :=
  flatCells pn G.cells + flatWires pn G.wires + flatLoops ln G.loops

/-- The equations of the cells and inner wires of a tree whose cells are numbered from `k`. -/
def flatTree
    -- the names of the ports, a tree, and the number of its first cell
    (pn : ℕ → ℕ → ℕ)
    (t : Term S ℕ)
    (k : ℕ) :
    Net S ℕ :=
  flatCells pn (t.rawCells k) + flatWires pn (t.rawWires k)

-- ============================================================================================
-- 2. The names of the flat text
-- ============================================================================================

private theorem range_succ_map'
    -- a function on the numbers, and a length
    {β : Type}
    (f : ℕ → β)
    (n : ℕ) :
    -- the images of `0, …, n` are that of `0`, then those of `i + 1` for `i < n`
    (Multiset.range (n + 1)).map f = f 0 ::ₘ ∑ i : Fin n, {f ((i : ℕ) + 1)} := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Multiset.range_succ, Multiset.map_cons, ih, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [Multiset.cons_swap, ← Multiset.singleton_add, ← Multiset.singleton_add,
      ← Multiset.singleton_add]
    abel

private theorem map_finsum_flat
    -- a finite sum of multisets, and a function on their elements
    {ι α β : Type}
    (s : Finset ι)
    (g : ι → Multiset α)
    (f : α → β) :
    -- the image of the sum is the sum of the images
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

/-- The names of the equation of a cell are the names of its ports. -/
theorem eqVars_cellEq
    (pn : ℕ → ℕ → ℕ)
    (p : ℕ × S.Sym) :
    eqVars (cellEq pn p) = (cellPorts p).map (End.flatName pn) := by
  rw [cellPorts, Multiset.map_map]
  rw [show End.flatName pn ∘ End.port p.1 = pn p.1 from rfl, range_succ_map']
  simp only [cellEq, eqVars_mk, vars_var, vars_app, Multiset.singleton_add]

/-- The names of the equations of some cells are the names of their ports. -/
theorem vars_flatCells
    (pn : ℕ → ℕ → ℕ)
    (C : Multiset (ℕ × S.Sym)) :
    (flatCells (S := S) pn C).vars = (C.bind cellPorts).map (End.flatName pn) := by
  unfold flatCells Net.vars
  rw [Multiset.bind_map, Multiset.map_bind]
  congr 1
  funext p
  exact eqVars_cellEq pn p

/-- The names of the equations of some wires are the names of their ends. -/
theorem vars_flatWires
    (pn : ℕ → ℕ → ℕ)
    (W : Multiset (Sym2 (End ℕ))) :
    (flatWires (S := S) pn W).vars = (W.bind wireEnds).map (End.flatName pn) := by
  unfold flatWires Net.vars
  rw [Multiset.bind_map, Multiset.map_bind]
  congr 1
  funext e
  induction e using Sym2.ind with
  | _ p q => simp [flatWire, Multiset.insert_eq_cons, Multiset.singleton_add]

/-- The names of the flat text: the names of the ports of the cells, the names of the ends of the
wires, and the names of the cyclic wires. -/
theorem vars_flat
    -- the names of the ports and of the cyclic wires, and a graph
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ)
    (G : Graph S ℕ) :
    (flat pn ln G).vars
      = (G.cells.bind cellPorts + G.ends).map (End.flatName pn)
        + (flatLoops (S := S) ln G.loops).vars := by
  simp only [flat, Net.vars_add, vars_flatCells, vars_flatWires, ends_eq_bind, Multiset.map_add]

/-- A name of the equations of `n` cyclic wires is the name of one of them. -/
theorem mem_vars_flatLoops
    -- a name of the equations of `n` cyclic wires
    {ln : ℕ → ℕ}
    {n y : ℕ}
    (h : y ∈ (flatLoops (S := S) ln n).vars) :
    -- is the name `ln j` of a cyclic wire `j < n`
    ∃ j < n, ln j = y := by
  simp only [flatLoops, Net.vars, Multiset.mem_bind, Multiset.mem_map, Multiset.mem_range] at h
  obtain ⟨e, ⟨j, hj, rfl⟩, hy⟩ := h
  simp only [eqVars_mk, vars_var, Multiset.mem_add, Multiset.mem_singleton, or_self] at hy
  exact ⟨j, hj, hy.symm⟩

/-- A port of a cell is one of its ports `0, …, n`, for `n` the arity of its symbol. -/
theorem mem_cellPorts
    -- a port of a cell
    {e : End ℕ}
    {p : ℕ × S.Sym}
    (h : e ∈ (cellPorts p : Multiset (End ℕ))) :
    -- is its port `i`, for some `i` at most its arity
    ∃ i, e = .port p.1 i ∧ i ≤ S.arity p.2 := by
  simp only [cellPorts, Multiset.mem_map, Multiset.mem_range] at h
  obtain ⟨i, hi, rfl⟩ := h
  exact ⟨i, rfl, by omega⟩

-- ============================================================================================
-- 3. Flattening a tree
-- ============================================================================================

/-- The flat text of a name is empty. -/
theorem flatTree_var
    (pn : ℕ → ℕ → ℕ)
    (x k : ℕ) :
    flatTree (S := S) pn (var x) k = 0 := by
  simp [flatTree, flatCells, flatWires, rawCells, rawWires]

/-- The flat text of a tree `α(t_1, …, t_n)`: the equation of its root cell, and for each `i` the
wire from the auxiliary port `i` to the root of `t_i` and the flat text of `t_i`. -/
theorem flatTree_app
    -- the names of the ports
    (pn : ℕ → ℕ → ℕ)
    -- a tree `α(t_1, …, t_n)`, its root cell numbered `k`
    (α : S.Sym)
    (ts : Fin (S.arity α) → Term S ℕ)
    (k : ℕ) :
    flatTree pn (app α ts) k
      = cellEq pn (k, α)
        ::ₘ ∑ i : Fin (S.arity α),
          (s(var (pn k ((i : ℕ) + 1)), var (((ts i).rootEnd (childBase k ts i)).flatName pn))
            ::ₘ flatTree pn (ts i) (childBase k ts i)) := by
  simp only [flatTree, flatCells, flatWires, rawCells, rawWires, Multiset.map_cons,
    map_finsum_flat, Multiset.cons_add]
  congr 1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [flatWire, Sym2.map_mk, End.flatName_port, Multiset.add_cons]

/-- **A tree is equivalent to its cells, each in its own equation** (Lafont 1997, page 71). In a
context `Δ`, the equation `t = u` is equivalent to the equation between the name of the root of
`t` and `u`, beside the flat text of `t`, when that flat text is linear. Each subtree is pulled
out of its cell into an equation of its own, by a wire substitution read backwards. -/
theorem equiv_flatTree
    -- the names of the ports
    (pn : ℕ → ℕ → ℕ) :
    ∀
      -- a tree, the number of its first cell, the other side of its equation
      (t : Term S ℕ)
      (k : ℕ)
      (u : Term S ℕ)
      -- the rest of the net
      (Δ : Net S ℕ),
      -- if the flat text beside `Δ` is linear
      Net.Linear (s(var ((t.rootEnd k).flatName pn), u) ::ₘ (flatTree pn t k + Δ)) →
      -- then `t = u` is equivalent to the root of `t` against `u`, beside the flat text of `t`
      Equiv
        (s(t, u) ::ₘ Δ)
        (s(var ((t.rootEnd k).flatName pn), u) ::ₘ (flatTree pn t k + Δ)) := by
  intro t
  induction t with
  | var x =>
    intro k u Δ _
    rw [flatTree_var, zero_add]
    exact Equiv.refl _
  | app α ts ih =>
    intro k u Δ hlin
    -- the names of the auxiliary ports, and the pieces of the flat text of each subtree
    let q : Fin (S.arity α) → ℕ := fun i => pn k ((i : ℕ) + 1)
    let F : Fin (S.arity α) → Net S ℕ := fun i =>
      s(var (q i), var (((ts i).rootEnd (childBase k ts i)).flatName pn)) ::ₘ
        flatTree pn (ts i) (childBase k ts i)
    let Δ' : Net S ℕ := s(var (pn k 0), u) ::ₘ Δ
    -- the cell with the subtrees of `s` pulled out
    let f : Finset (Fin (S.arity α)) → Fin (S.arity α) → Term S ℕ := fun s i =>
      if i ∈ s then var (q i) else ts i
    let X : Finset (Fin (S.arity α)) → Net S ℕ := fun s =>
      s(app α (f s), var (pn k 0)) ::ₘ ((∑ i ∈ s, F i) + Δ')
    have key : ∀ s, (X s).Linear → Equiv (X s) (X ∅) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact fun _ => Equiv.refl _
      | insert a s ha ihs =>
        intro hX
        have hf : f (insert a s) = Function.update (f s) a (var (q a)) := by
          funext i
          by_cases hi : i = a
          · subst hi
            simp [f]
          · simp [f, hi]
        have hfa : f s a = ts a := by simp [f, ha]
        have e1 : X (insert a s) =
            s(var (((ts a).rootEnd (childBase k ts a)).flatName pn), var (q a)) ::ₘ
              (flatTree pn (ts a) (childBase k ts a) +
                s(app α (Function.update (f s) a (var (q a))), var (pn k 0)) ::ₘ
                  ((∑ i ∈ s, F i) + Δ')) := by
          simp only [X, hf, Finset.sum_insert ha, F]
          rw [Sym2.eq_swap (a := var (q a))]
          simp only [← Multiset.singleton_add]
          abel
        rw [e1] at hX ⊢
        have E1 := ih a (childBase k ts a) (var (q a)) _ hX
        have hY := E1.symm.linear hX
        have hc := hY (q a)
        have hcu := count_vars_update (f s) a (q a) (q a)
        rw [hfa] at hcu
        simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, vars_var,
          Multiset.count_singleton_self, ite_true] at hc hcu
        have h0 : q a ∉ (app α (f s)).vars := Multiset.count_eq_zero.1 (by omega)
        have h0' : q a ∉ (var (pn k 0) : Term S ℕ).vars :=
          Multiset.count_eq_zero.1 (by simp only [vars_var] at hc ⊢; omega)
        have hx : q a ∈ (app α (Function.update (f s) a (var (q a)))).vars +
            (var (pn k 0) : Term S ℕ).vars := by
          refine Multiset.mem_add.2 (Or.inl ?_)
          simp only [vars_app]
          exact Multiset.mem_sum.2 ⟨a, Finset.mem_univ _, by simp⟩
        have W := Wire.mk (q a) (ts a) (app α (Function.update (f s) a (var (q a))))
          (var (pn k 0)) ((∑ i ∈ s, F i) + Δ') (by rw [Sym2.eq_swap]; exact hY) hx
        have hsu := subst_update (f s) a h0
        rw [hfa] at hsu
        rw [hsu, subst_of_notMem h0', Sym2.eq_swap (a := var (q a)) (b := ts a)] at W
        exact E1.symm.trans (W.equiv.trans (ihs W.linear_right))
    have hfu : f Finset.univ = fun i => var (q i) := by
      funext i
      simp [f]
    have hf0 : f ∅ = ts := by
      funext i
      simp [f]
    have eU : X Finset.univ = s(var (pn k 0), u) ::ₘ (flatTree pn (app α ts) k + Δ) := by
      simp only [X, hfu, flatTree_app, Δ', F, cellEq, q]
      rw [Sym2.eq_swap (a := app α _)]
      simp only [← Multiset.singleton_add]
      abel
    have e0 : X ∅ = s(var (pn k 0), app α ts) ::ₘ s(var (pn k 0), u) ::ₘ Δ := by
      simp only [X, hf0, Finset.sum_empty, zero_add, Δ']
      rw [Sym2.eq_swap]
    change Net.Linear (s(var (pn k 0), u) ::ₘ (flatTree pn (app α ts) k + Δ)) at hlin
    change Equiv _ (s(var (pn k 0), u) ::ₘ (flatTree pn (app α ts) k + Δ))
    rw [← eU] at hlin ⊢
    have E := key _ hlin
    rw [e0] at E
    have hl0 := E.linear hlin
    have hc := hl0 (pn k 0)
    simp only [Net.vars_cons, eqVars_mk, Multiset.count_add, vars_var,
      Multiset.count_singleton_self] at hc
    have hu : pn k 0 ∉ u.vars := Multiset.count_eq_zero.1 (by omega)
    have W := Wire.mk (pn k 0) (app α ts) (var (pn k 0)) u Δ hl0 (by simp)
    rw [show (var (pn k 0) : Term S ℕ).subst (pn k 0) (app α ts) = app α ts by simp [subst],
      subst_of_notMem hu] at W
    exact (E.trans W.equiv).symm

-- ============================================================================================
-- 4. Flattening a text
-- ============================================================================================

/-- The flat text of the raw graph of `(a = b) :: L`. -/
theorem flat_raw_cons
    -- the names of the ports and of the cyclic wires, and the number of the first cell
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ)
    (k : ℕ)
    -- a text: a first equation `a = b`, then `L`
    (a b : Term S ℕ)
    (L : List (Term S ℕ × Term S ℕ)) :
    -- the roots of `a` and `b` against each other, the flat texts of `a`, `b` and `L`
    flat pn ln (raw k ((a, b) :: L))
      = s(var ((a.rootEnd k).flatName pn), var ((b.rootEnd (k + a.size)).flatName pn))
        ::ₘ (flatTree pn a k + flatTree pn b (k + a.size)
          + flat pn ln (raw (k + a.size + b.size) L)) := by
  simp only [flat, raw, flatCells, flatWires, flatTree, Multiset.map_add, Multiset.map_cons,
    flatWire, Sym2.map_mk]
  simp only [← Multiset.singleton_add]
  abel

/-- **A text is equivalent to the flat text of its raw graph** (Lafont 1997, page 71), in any
context `Δ`, when the flat text beside `Δ` is linear. -/
theorem equiv_flat_raw
    -- the names of the ports and of the cyclic wires
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ) :
    ∀
      -- a text, the number of its first cell, and the rest of the net
      (L : List (Term S ℕ × Term S ℕ))
      (k : ℕ)
      (Δ : Net S ℕ),
      -- if the flat text beside `Δ` is linear
      Net.Linear (flat pn ln (raw k L) + Δ) →
      -- then the text is equivalent to the flat text, beside `Δ`
      Equiv (Net.ofList L + Δ) (flat pn ln (raw k L) + Δ)
  | [], k, Δ, _ => by
    simp only [flat, raw, flatCells, flatWires, flatLoops, Multiset.map_zero, Multiset.range_zero,
      add_zero]
    exact Equiv.refl _
  | (a, b) :: L, k, Δ, hlin => by
    rw [flat_raw_cons] at hlin ⊢
    have e1 : s(var ((a.rootEnd k).flatName pn), var ((b.rootEnd (k + a.size)).flatName pn)) ::ₘ
        (flatTree pn a k + flatTree pn b (k + a.size) + flat pn ln (raw (k + a.size + b.size) L))
          + Δ =
        s(var ((b.rootEnd (k + a.size)).flatName pn), var ((a.rootEnd k).flatName pn)) ::ₘ
          (flatTree pn b (k + a.size) +
            (flatTree pn a k + flat pn ln (raw (k + a.size + b.size) L) + Δ)) := by
      rw [Sym2.eq_swap (a := var ((a.rootEnd k).flatName pn)), Multiset.cons_add]
      congr 1
      abel
    rw [e1] at hlin ⊢
    have E1 := equiv_flatTree pn b (k + a.size) (var ((a.rootEnd k).flatName pn)) _ hlin
    have h1 := E1.symm.linear hlin
    have e2 : s(b, var ((a.rootEnd k).flatName pn)) ::ₘ
        (flatTree pn a k + flat pn ln (raw (k + a.size + b.size) L) + Δ) =
        s(var ((a.rootEnd k).flatName pn), b) ::ₘ
          (flatTree pn a k + (flat pn ln (raw (k + a.size + b.size) L) + Δ)) := by
      rw [Sym2.eq_swap, add_assoc]
    rw [e2] at h1 E1
    have E2 := equiv_flatTree pn a k b _ h1
    have h2 := E2.symm.linear h1
    have e3 : s(a, b) ::ₘ (flat pn ln (raw (k + a.size + b.size) L) + Δ) =
        flat pn ln (raw (k + a.size + b.size) L) + s(a, b) ::ₘ Δ :=
      (Multiset.add_cons _ _ _).symm
    rw [e3] at h2 E2
    have E3 := equiv_flat_raw pn ln L _ _ h2
    rw [Net.ofList_cons, Multiset.cons_add, ← Multiset.add_cons]
    exact E3.trans (E2.trans E1)

/-- **The flat text of the raw graph of a linear text is linear** (Lafont 1997, page 71), when the
names of the ports are distinct and unused in the text: each port name occurs in the equation of
its cell and in the equation of its wire, and each name of the text as often as in the text. -/
theorem linear_flat_raw
    -- the names of the ports and of the cyclic wires, and the number of the first cell
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ)
    (k : ℕ)
    -- a linear text
    (L : List (Term S ℕ × Term S ℕ))
    (hN : (Net.ofList L).Linear)
    -- the names of the ports of the cells of its raw graph are distinct
    (hpn : ∀ c i d j,
      c ∈ (raw k L).cells.map Prod.fst → d ∈ (raw k L).cells.map Prod.fst →
      pn c i = pn d j → c = d ∧ i = j)
    -- and unused in the text
    (hpN : ∀ c i, pn c i ∉ (Net.ofList L).vars) :
    (flat pn ln (raw k L)).Linear := by
  intro y
  rw [vars_flat, raw_loops, raw_ends]
  have hl0 : (flatLoops (S := S) ln 0).vars = 0 := by simp [flatLoops]
  have hmap : ((Net.ofList L).vars.map End.name).map (End.flatName pn) = (Net.ofList L).vars := by
    rw [Multiset.map_map]
    exact Multiset.map_id' _
  rw [hl0, add_zero, Multiset.map_add, Multiset.map_add, hmap]
  set P := (raw k L).cells.bind cellPorts with hP
  have hPmem : ∀ e ∈ P, ∃ c α i, (c, α) ∈ (raw k L).cells ∧ i ≤ S.arity α ∧ e = .port c i := by
    intro e he
    obtain ⟨p, hp, hep⟩ := Multiset.mem_bind.1 he
    obtain ⟨i, rfl, hi⟩ := mem_cellPorts hep
    exact ⟨p.1, p.2, i, hp, hi, rfl⟩
  have hPnd : P.Nodup := by
    refine Multiset.nodup_iff_count_le_one.2 fun e => ?_
    by_cases he : e ∈ P
    · obtain ⟨c, α, i, hc, hi, rfl⟩ := hPmem _ he
      have := raw_port k L c α hc i hi
      rw [raw_ends, ← hP, Multiset.count_add] at this
      omega
    · rw [Multiset.count_eq_zero.2 he]
      omega
  have hnd : (P.map (End.flatName pn)).Nodup := by
    refine hPnd.map_on fun e he e' he' h => ?_
    obtain ⟨c, α, i, hc, -, rfl⟩ := hPmem _ he
    obtain ⟨d, β, j, hd, -, rfl⟩ := hPmem _ he'
    obtain ⟨rfl, rfl⟩ := hpn c i d j (Multiset.mem_map_of_mem _ hc)
      (Multiset.mem_map_of_mem _ hd) h
    rfl
  rw [Multiset.count_add, Multiset.count_add]
  by_cases hy : y ∈ P.map (End.flatName pn)
  · obtain ⟨e, he, rfl⟩ := Multiset.mem_map.1 hy
    obtain ⟨c, α, i, -, -, rfl⟩ := hPmem _ he
    rw [Multiset.count_eq_one_of_mem hnd hy, End.flatName_port,
      Multiset.count_eq_zero.2 (hpN c i)]
  · rw [Multiset.count_eq_zero.2 hy]
    have := hN y
    omega

-- ============================================================================================
-- 5. Erasing a name
-- ============================================================================================

/-- An equation `x = x` whose name occurs nowhere else may be renamed: it is a cyclic wire. -/
theorem equiv_loop_rename
    -- an equation `x = x` beside the rest of the net `Δ`, the whole linear
    {x z : ℕ}
    {Δ : Net S ℕ}
    (hlin : Net.Linear (s(var x, var x) ::ₘ Δ))
    -- a name `z` unused in the net
    (hz : z ∉ Net.vars (s(var x, var x) ::ₘ Δ)) :
    -- the equation may be renamed to `z = z`
    Equiv (s(var x, var x) ::ₘ Δ) (s(var z, var z) ::ₘ Δ) := by
  simp only [Net.vars_cons, eqVars_mk, vars_var, Multiset.mem_add, Multiset.mem_singleton,
    or_self, not_or] at hz
  obtain ⟨hzx, hzΔ⟩ := hz
  have hΔz := Multiset.count_eq_zero.2 hzΔ
  have hK : Net.Linear (s(var x, var z) ::ₘ s(var z, var x) ::ₘ Δ) := by
    intro y
    have h := hlin y
    simp only [Net.vars_cons, eqVars_mk, vars_var, Multiset.count_add,
      Multiset.count_singleton] at h ⊢
    by_cases h1 : y = x
    · subst h1
      simp only [ite_true, Ne.symm hzx, ite_false] at h ⊢
      omega
    · by_cases h2 : y = z
      · subst h2
        simp only [h1, ite_true, ite_false, hΔz]
        omega
      · simp only [h1, h2, ite_false] at h ⊢
        omega
  have hK' : Net.Linear (s(var z, var x) ::ₘ s(var x, var z) ::ₘ Δ) := by
    rw [Multiset.cons_swap]; exact hK
  have W1 := Wire.mk x (var z) (var z) (var x) Δ hK (by simp)
  have W2 := Wire.mk z (var x) (var x) (var z) Δ hK' (by simp)
  have e1 : (var z : Term S ℕ).subst x (var z) = var z := by simp [subst, hzx]
  have e2 : (var x : Term S ℕ).subst x (var z) = var z := by simp [subst]
  have e3 : (var x : Term S ℕ).subst z (var x) = var x := by simp [subst, Ne.symm hzx]
  have e4 : (var z : Term S ℕ).subst z (var x) = var x := by simp [subst]
  rw [e1, e2] at W1
  rw [e3, e4] at W2
  rw [Multiset.cons_swap] at W2
  exact W2.equiv.symm.trans W1.equiv

/-- **Erasing a name of the graph is a wire substitution of the flat text** (Lafont 1997,
page 71). Joining the two wires of a name `x` is the wire substitution of `x`; turning a wire from
`x` to itself into a cyclic wire renames the equation `x = x`, when the next name of a cyclic wire
is unused. -/
theorem equiv_flat_contract
    -- the names of the ports and of the cyclic wires
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ)
    -- a graph `G` that contracts to `H` by erasing one name
    {G H : Graph S ℕ}
    (h : Contract G H)
    -- the flat text of `G` is linear
    (hlin : (flat pn ln G).Linear)
    -- and the name of the next cyclic wire is unused in it
    (hfr : ln G.loops ∉ (flat pn ln G).vars) :
    Equiv (flat pn ln G) (flat pn ln H) := by
  cases h with
  | join x p q C W n =>
    have e : flat pn ln ⟨C, s(.name x, p) ::ₘ s(.name x, q) ::ₘ W, n⟩ =
        s(var x, var (p.flatName pn)) ::ₘ s(var x, var (q.flatName pn)) ::ₘ
          (flatCells pn C + flatWires pn W + flatLoops ln n) := by
      simp only [flat, flatWires, Multiset.map_cons, flatWire, Sym2.map_mk, End.flatName_name]
      simp only [← Multiset.singleton_add]
      abel
    have e' : flat pn ln ⟨C, s(p, q) ::ₘ W, n⟩ =
        s(var (p.flatName pn), var (q.flatName pn)) ::ₘ
          (flatCells pn C + flatWires pn W + flatLoops ln n) := by
      simp only [flat, flatWires, Multiset.map_cons, flatWire, Sym2.map_mk]
      simp only [← Multiset.singleton_add]
      abel
    rw [e] at hlin ⊢
    rw [e']
    have hc := hlin x
    simp only [Net.vars_cons, eqVars_mk, vars_var, Multiset.count_add,
      Multiset.count_singleton_self, Multiset.count_singleton] at hc
    have hq : x ∉ (var (q.flatName pn) : Term S ℕ).vars := by
      simp only [vars_var, Multiset.mem_singleton]
      intro h
      split_ifs at hc <;> omega
    have W := Wire.mk x (var (p.flatName pn)) (var x) (var (q.flatName pn)) _ hlin (by simp)
    rw [show (var x : Term S ℕ).subst x (var (p.flatName pn)) = var (p.flatName pn) by
      simp [subst], subst_of_notMem hq] at W
    exact W.equiv
  | loop x C W n =>
    have e : flat pn ln ⟨C, s(.name x, .name x) ::ₘ W, n⟩ =
        s(var x, var x) ::ₘ (flatCells pn C + flatWires pn W + flatLoops ln n) := by
      simp only [flat, flatWires, Multiset.map_cons, flatWire, Sym2.map_mk, End.flatName_name]
      simp only [← Multiset.singleton_add]
      abel
    have e' : flat pn ln ⟨C, W, n + 1⟩ =
        s(var (ln n), var (ln n)) ::ₘ (flatCells pn C + flatWires pn W + flatLoops ln n) := by
      simp only [flat, flatLoops, Multiset.range_succ, Multiset.map_cons]
      simp only [← Multiset.singleton_add]
      abel
    change ln n ∉ (flat pn ln ⟨C, s(.name x, .name x) ::ₘ W, n⟩).vars at hfr
    rw [e] at hlin hfr ⊢
    rw [e']
    exact equiv_loop_rename hlin hfr

/-- **A linear text is equivalent to the flat text of each of its graphs** (Lafont 1997,
page 71). Let the raw graph of `L` contract to `G`, the names `pn c i` of the ports of the cells be
distinct, the names `ln j` of the cyclic wires be distinct, and all of them be different from each
other and unused in `L`. Then the text of `L` is equivalent to the flat text of `G`. -/
theorem equiv_flat_of_contracts
    -- a linear text, whose raw graph, with cells numbered from `k`, contracts to `G`
    {L : List (Term S ℕ × Term S ℕ)}
    {k : ℕ}
    {G : Graph S ℕ}
    (hN : (Net.ofList L).Linear)
    (h : Relation.ReflTransGen Contract (raw k L) G)
    -- the names of the ports and of the cyclic wires
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ)
    -- the names of the ports of the cells are distinct
    (hpn : ∀ c i d j,
      c ∈ (raw k L).cells.map Prod.fst → d ∈ (raw k L).cells.map Prod.fst →
      pn c i = pn d j → c = d ∧ i = j)
    -- the names of the cyclic wires are distinct, and different from those of the ports
    (hln : Function.Injective ln)
    (hpl : ∀ c i j, pn c i ≠ ln j)
    -- and all of them are unused in the text
    (hpN : ∀ c i, pn c i ∉ (Net.ofList L).vars)
    (hlN : ∀ j, ln j ∉ (Net.ofList L).vars) :
    Equiv (Net.ofList L) (flat pn ln G) := by
  have hl := linear_flat_raw pn ln k L hN hpn hpN
  have E0 : Equiv (Net.ofList L) (flat pn ln (raw k L)) := by
    have := equiv_flat_raw pn ln L k 0 (by rw [add_zero]; exact hl)
    rwa [add_zero, add_zero] at this
  induction h with
  | refl => exact E0
  | tail hab hbc ih =>
    rename_i H₁ H₂
    refine ih.trans (equiv_flat_contract pn ln hbc (ih.linear hN) fun hm => ?_)
    rw [vars_flat] at hm
    rcases Multiset.mem_add.1 hm with hm | hm
    · obtain ⟨e, he, hfe⟩ := Multiset.mem_map.1 hm
      rcases Multiset.mem_add.1 he with he | he
      · obtain ⟨p, -, hep⟩ := Multiset.mem_bind.1 he
        obtain ⟨i, rfl, -⟩ := mem_cellPorts hep
        exact hpl _ _ _ hfe
      · have he' := Multiset.mem_of_le (contracts_ends_le hab) he
        rw [raw_ends, Multiset.mem_add] at he'
        rcases he' with he' | he'
        · obtain ⟨p, -, hep⟩ := Multiset.mem_bind.1 he'
          obtain ⟨i, rfl, -⟩ := mem_cellPorts hep
          exact hpl _ _ _ hfe
        · obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 he'
          rw [End.flatName_name] at hfe
          exact hlN _ (hfe ▸ hx)
    · obtain ⟨j, hj, hje⟩ := mem_vars_flatLoops hm
      rw [hln hje] at hj
      exact lt_irrefl _ hj

-- ============================================================================================
-- 6. Isomorphic graphs
-- ============================================================================================

/-- **The flat texts of isomorphic graphs differ by the names of the ports** (Lafont 1997,
page 71): if `σ` carries the cells and wires of `G` to those of `G'`, the flat text of `G'` with
the port names `pn` is the flat text of `G` with the port names `pn (σ c) i`. -/
theorem flat_iso
    -- the names of the ports and of the cyclic wires
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ)
    -- two graphs, and a renumbering `σ` of the cells
    {G G' : Graph S ℕ}
    {σ : ℕ → ℕ}
    -- that carries the cells, the wires and the cyclic wires of `G` to those of `G'`
    (hc : G'.cells = G.cells.map (Prod.map σ id))
    (hw : G'.wires = G.wires.map (Sym2.map (End.mapCell σ)))
    (hl : G'.loops = G.loops) :
    flat pn ln G' = flat (fun c i => pn (σ c) i) ln G := by
  simp only [flat, hc, hw, hl, flatCells, flatWires, Multiset.map_map]
  congr 2
  refine Multiset.map_congr rfl fun e _ => ?_
  induction e using Sym2.ind with
  | _ p q => simp [flatWire, End.flatName_mapCell]

end Graph

-- ============================================================================================
-- 7. Main results
-- ============================================================================================

/-- **Linear nets with isomorphic graphs are equivalent** (Lafont 1997, Section 1.1, page 71;
the direction from `Iso` to `Equiv`): if `N` and `M` are linear and a graph of `N` is isomorphic
to a graph of `M`, then `Equiv N M`. Both are equivalent to the flat text of the graph of `N`,
with ports named above every name of `N` and `M`. -/
theorem Net.Linear.equiv_of_hasGraph_iso
    -- two linear nets
    {N M : Net S ℕ}
    (hN : N.Linear)
    (hM : M.Linear)
    -- a graph of each, the two isomorphic
    {G G' : Graph S ℕ}
    (hG : N.HasGraph G)
    (hG' : M.HasGraph G')
    (h : G.Iso G') :
    Equiv N M := by
  obtain ⟨L, k, rfl, hc, -⟩ := hG
  obtain ⟨L', k', rfl, hc', -⟩ := hG'
  obtain ⟨σ, hσ, hcs, hws, hls⟩ := h
  -- a bound on the names of both texts
  let B : ℕ := ((Net.ofList L).vars + (Net.ofList L').vars).sup + 1
  have hB : ∀ x, x ∈ (Net.ofList L).vars + (Net.ofList L').vars → x < B := fun x hx =>
    Nat.lt_succ_of_le (Multiset.le_sup hx)
  have hBL : ∀ x ∈ (Net.ofList L).vars, x < B := fun x hx => hB x (Multiset.mem_add.2 (.inl hx))
  have hBL' : ∀ x ∈ (Net.ofList L').vars, x < B := fun x hx =>
    hB x (Multiset.mem_add.2 (.inr hx))
  -- ports and cyclic wires named above `B`, the ports even and the cyclic wires odd
  let pn : ℕ → ℕ → ℕ := fun c i => B + 2 * Nat.pair c i
  let ln : ℕ → ℕ := fun j => B + 2 * j + 1
  have hln : Function.Injective ln := fun a b e => by simp only [ln] at e; omega
  have hpl : ∀ (σ : ℕ → ℕ) c i j, pn (σ c) i ≠ ln j := fun σ c i j e => by
    simp only [pn, ln] at e; omega
  have hpnI : ∀ c i d j, pn c i = pn d j → c = d ∧ i = j := fun c i d j e => by
    simp only [pn] at e
    exact Nat.pair_eq_pair.1 (by omega)
  have hpB : ∀ (σ : ℕ → ℕ) c i (L₀ : List (Term S ℕ × Term S ℕ)),
      (∀ x ∈ (Net.ofList L₀).vars, x < B) → pn (σ c) i ∉ (Net.ofList L₀).vars :=
    fun σ c i L₀ hb hm => by have := hb _ hm; simp only [pn] at this; omega
  have hlB : ∀ j (L₀ : List (Term S ℕ × Term S ℕ)),
      (∀ x ∈ (Net.ofList L₀).vars, x < B) → ln j ∉ (Net.ofList L₀).vars :=
    fun j L₀ hb hm => by have := hb _ hm; simp only [ln] at this; omega
  -- `M` is equivalent to the flat text of `G'`
  have E2 := Graph.equiv_flat_of_contracts hM hc' pn ln (fun c i d j _ _ e => hpnI c i d j e)
    hln (hpl id) (fun c i => hpB id c i L' hBL') (fun j => hlB j L' hBL')
  rw [Graph.flat_iso pn ln hcs hws hls] at E2
  -- `N` is equivalent to the flat text of `G` with the ports of `G'`
  have hcells : G.cells = (Graph.raw k L).cells := Graph.contracts_cells_eq hc
  have E1 := Graph.equiv_flat_of_contracts hN hc (fun c i => pn (σ c) i) ln
    (fun c i d j hcm hdm e => by
      obtain ⟨e1, e2⟩ := hpnI _ _ _ _ e
      rw [← hcells] at hcm hdm
      exact ⟨hσ hcm hdm e1, e2⟩)
    hln (hpl σ) (fun c i => hpB σ c i L hBL) (fun j => hlB j L hBL)
  exact E1.trans E2.symm

/-- **Two linear nets are equivalent if and only if their graphs are isomorphic** (Lafont 1997,
Section 1.1, page 71). -/
theorem Net.Linear.equiv_iff_hasGraph_iso
    -- two linear nets
    {N M : Net S ℕ}
    (hN : N.Linear)
    (hM : M.Linear)
    -- a graph of each
    {G G' : Graph S ℕ}
    (hG : N.HasGraph G)
    (hG' : M.HasGraph G') :
    -- the nets are equivalent exactly when the graphs are isomorphic
    Equiv N M ↔ G.Iso G' :=
  ⟨fun h => hN.equiv_hasGraph_iso h hG hG', hN.equiv_of_hasGraph_iso hM hG hG'⟩

end INet
