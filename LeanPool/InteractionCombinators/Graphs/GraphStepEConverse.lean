/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Graphs.GraphInteractUnique
public import LeanPool.InteractionCombinators.Graphs.GraphRealize

/-!
# An interaction of graphs is an interaction of texts

Lafont 1997, Section 1.2, page 73: an interaction rule replaces two cells joined by their
principal ports by the right-hand side of the rule. On texts this is `StepE`, on graphs
`Graph.Interact`. `GraphStepE.lean` proves that a `StepE` of a linear net is an interaction of its
graph; this file proves the converse: every interaction of the graph of a linear net is, up to
`Graph.Iso`, the graph of a `StepE` of that net.

The proof writes the graph `G` as its flat text (`Graph.flatB`), one equation for each cell and
each wire. Two wire substitutions along the principal ports of the two cells make the active pair
literal, `α(pn c 1, …) = β(pn d 1, …)`, beside the flat text `Γ` of the rest of `G`. One `Step`
on it gives `r.inst … + Γ`. Its raw graph contracts to the graph that `Interact` contracts, with
a graph `R'` of the rule numbered above the cells of `G`, and the names of the auxiliary ports in
the flat text as fresh names: erasing the names of the ports of the other cells (`stubs`) plugs
them back into the wires, and the auxiliary ports of the two cells stay as names, which is the
cut. The uniqueness of the result of an interaction (`Graph.interact_unique`) gives the theorem.

The example on the combinators is in `Checks/Graphs/GraphStepEConverseCheck.lean`.

Contents, in the order of the file:

1. Definitions: `Graph.stubGraph`, the stubs of a graph (its cells, a wire from each port to its
   name, the wires between names); `Graph.stubBack`, reading the names of the stubs back as
   their ports.
2. Auxiliary lemmas: the stubs, `exists_list_sym2'`, `Graph.stubGraph_portsIn`,
   `Graph.stubGraph_iso_raw` (the raw graph of the flat text of a graph whose cells have distinct
   numbers is isomorphic to its stubs); the names of the flat text, `Graph.realPn_inj`,
   `Graph.le_realPn`, `Graph.realPn_ne_realLn`, `Graph.unflat_eq_port` (a name that `unflat`
   reads as a port is the name of that port).
3. Main result: `Net.Linear.interact_stepE`, every interaction of the graph of a linear net is,
   up to isomorphism, the graph of a `StepE` of the net.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

namespace Graph

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

/-- **The stubs of a graph** (Lafont 1997, page 71): its cells, a wire `pn c i — port c i` for each
port of each cell, a wire between the names of the two ends of each wire, and a wire
`ln j — ln j` for each cyclic wire. This is the raw graph of the flat text, up to the numbering
of the cells. -/
def stubGraph
    -- the names of the ports and of the cyclic wires
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ)
    -- the graph
    (G : Graph S ℕ) :
    Graph S ℕ :=
  ⟨G.cells, (G.cells.bind cellPorts).map (fun e => s(.name (e.flatName pn), e)) +
    (G.wires.map (Sym2.map fun e => .name (e.flatName pn)) +
      (Multiset.range G.loops).map fun j => s(End.name (ln j), End.name (ln j))), 0⟩

/-- Reading back the names of the stubs `P` as their ports, and keeping every other end. -/
def stubBack
    -- the bound of the free names of the graph
    (B : ℕ)
    -- the ports of the stubs
    (P : Multiset (End ℕ)) :
    End ℕ → End ℕ
  | .port c i => .port c i
  | .name y => if unflat B (.name y) ∈ P then unflat B (.name y) else .name y

-- ============================================================================================
-- 2. Auxiliary lemmas: the stubs and the names of a flat text
-- ============================================================================================

/-- Every multiset of unordered pairs is a list of ordered pairs. -/
private theorem exists_list_sym2'
    -- the type of the elements
    {α : Type}
    -- the multiset of unordered pairs
    (M : Multiset (Sym2 α)) :
    -- some list of ordered pairs gives `M` when its pairs are unordered
    ∃ l : List (α × α),
      ((l.map fun q => s(q.1, q.2) : List (Sym2 α)) : Multiset (Sym2 α)) = M := by
  induction M using Multiset.induction_on with
  | empty => exact ⟨[], rfl⟩
  | cons e M ih =>
    obtain ⟨l, rfl⟩ := ih
    induction e using Sym2.ind with
    | _ a b => exact ⟨(a, b) :: l, rfl⟩

/-- Every port at an end of a wire of the stubs of a graph is a port of one of its cells. -/
theorem stubGraph_portsIn
    -- the names of the ports and of the cyclic wires, and the graph
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ)
    (G : Graph S ℕ)
    -- the port `i` of `c`, at an end of a wire of the stubs
    (c i : ℕ)
    (hm : End.port c i ∈ (stubGraph pn ln G).ends) :
    -- `c` is a cell of the stubs
    c ∈ (stubGraph pn ln G).cells.map Prod.fst := by
  rw [ends_eq_bind] at hm
  simp only [stubGraph, Multiset.add_bind, Multiset.mem_add] at hm
  rcases hm with hm | hm | hm
  · exact cellGraph_portsIn pn G.cells c i (by rw [ends_eq_bind]; exact hm)
  · rw [bind_wireEnds_map] at hm
    obtain ⟨e, -, he⟩ := Multiset.mem_map.1 hm
    cases he
  · obtain ⟨w, hw, hm⟩ := Multiset.mem_bind.1 hm
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hw
    simp at hm

/-- **The raw graph of the flat text of a graph is isomorphic to its stubs** (Lafont 1997,
page 71), for any graph whose cells have distinct numbers and any numbering of the cells of the
text. -/
theorem stubGraph_iso_raw
    -- the names of the ports and of the cyclic wires
    (pn : ℕ → ℕ → ℕ)
    (ln : ℕ → ℕ)
    -- the graph, whose cells have distinct numbers
    (G : Graph S ℕ)
    (hnd : (G.cells.map Prod.fst).Nodup)
    -- the first number of the cells of the raw graph
    (k : ℕ) :
    -- there is a list of equations `L` such that
    ∃ L : List (Term S ℕ × Term S ℕ),
      -- `L` is the flat text of `G`,
      Net.ofList L = flat pn ln G ∧
      -- and the stubs of `G` are isomorphic to the raw graph of `L`
      (stubGraph pn ln G).Iso (raw k L) := by
  obtain ⟨lw, hlw⟩ := exists_list_sym2' G.wires
  let cl := G.cells.toList
  let lv : List (ℕ × ℕ) := lw.map (fun q => (q.1.flatName pn, q.2.flatName pn)) ++
    (List.range G.loops).map (fun j => (ln j, ln j))
  let L := cl.map (cellPair pn) ++ lv.map (fun q => ((var q.1 : Term S ℕ), (var q.2 : Term S ℕ)))
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
  · have e1 : raw k L = (raw k (cl.map (cellPair pn))).union ⟨0, Wn + Lp, 0⟩ := by
      rw [raw_append, raw_names, hlv]
    have e2 : stubGraph pn ln G = (cellGraph pn (cl : Multiset (ℕ × S.Sym))).union
        ⟨0, Wn + Lp, 0⟩ := by
      simp [stubGraph, cellGraph, union, cl, Wn, Lp]
    have hnd' : (cl.map Prod.fst).Nodup := by
      rw [← Multiset.coe_nodup, ← Multiset.map_coe, Multiset.coe_toList]
      exact hnd
    rw [e1, e2]
    refine (cellGraph_iso pn cl k hnd').union (Iso.refl _) (cellGraph_portsIn pn _) ?_
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

/-- Distinct ports get distinct names (Lafont 1997, page 71). -/
theorem realPn_inj
    -- the bound, and the two ports `i` of `c` and `j` of `d`
    {B c i d j : ℕ}
    -- with the same name
    (h : realPn B c i = realPn B d j) :
    -- are the same port
    c = d ∧ i = j := by
  simp only [realPn] at h
  exact Nat.pair_eq_pair.1 (by omega)

/-- The name of a port is at least the bound `B`. -/
theorem le_realPn
    -- the bound, and the port `i` of `c`
    (B c i : ℕ) :
    B ≤ realPn B c i := by
  simp [realPn]

/-- The name of a port is not the name of a cyclic wire. -/
theorem realPn_ne_realLn
    -- the bound, the port `i` of `c`, and the cyclic wire `j`
    (B c i j : ℕ) :
    realPn B c i ≠ realLn B j := by
  simp only [realPn, realLn]
  omega

/-- **A name that `unflat` reads as a port is the name of that port** (Lafont 1997, page 71). -/
theorem unflat_eq_port
    -- the bound, the name `y`, and the port `i` of `c`
    {B y c i : ℕ}
    -- `unflat` reads `y` as that port
    (h : unflat B (.name y) = .port c i) :
    -- `y` is the name of the port
    y = realPn B c i := by
  simp only [unflat] at h
  split_ifs at h with hy
  · obtain ⟨rfl, rfl⟩ := End.port.inj h
    simp only [realPn, Nat.pair_unpair]
    omega

end Graph

-- ============================================================================================
-- 3. Main result: an interaction of graphs is an interaction of texts
-- ============================================================================================

/-- Reconstruct a text's graph from the contractions after the active pair is removed. -/
private theorem inst_hasGraph_after_preInteract {c d B D n : ℕ} {α β : S.Sym}
    {C : Multiset (ℕ × S.Sym)} {W : Multiset (Sym2 (End ℕ))}
    {r : Rule S (S.arity α) (S.arity β)}
    {Lr : List (Term S (Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal) ×
      Term S (Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal))}
    {R' : Graph S (Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal)} {H' : Graph S ℕ}
    {f : Fin r.internal → ℕ}
    {g' : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal → ℕ}
    (hGwf : (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ :
      Graph S ℕ).WF)
    (hLr : r.net = Net.ofList Lr)
    (hR'c : Relation.ReflTransGen Graph.Contract (Graph.raw D Lr) R')
    (hH' : Relation.ReflTransGen Graph.Contract (Graph.preInteract c d C W n R' id g') H')
    (hH'1 : ∀ x, H'.ends.count (.name x) ≤ 1)
    (hWB : ∀ y, End.name y ∈ W.bind Graph.wireEnds → y < B)
    (hDG : ∀ x ∈ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst, x < D)
    (hg'P : ∀ e ∈ C.bind Graph.cellPorts, ∀ w, g' w ≠ e.flatName (Graph.realPn B))
    (leftPort : ∀ i, g' (.inl i) = Graph.realPn B c (i.val + 1))
    (rightPort : ∀ j, g' (.inr (.inl j)) = Graph.realPn B d (j.val + 1))
    (wirePort : ∀ w, g' (.inr (.inr w)) = f w) :
    let xs : Fin (S.arity α) → Term S ℕ := fun i => var (Graph.realPn B c (i.val + 1))
    let ys : Fin (S.arity β) → Term S ℕ := fun j => var (Graph.realPn B d (j.val + 1))
    let Γ := Graph.flat (Graph.realPn B) (Graph.realLn B) (⟨C, W, n⟩ : Graph S ℕ)
    ∃ H'', (r.inst xs ys f + Γ).HasGraph H'' ∧ H'.Iso H'' := by
  classical
  dsimp only
  set xs : Fin (S.arity α) → Term S ℕ := fun i => var (Graph.realPn B c (i.val + 1))
  set ys : Fin (S.arity β) → Term S ℕ := fun j => var (Graph.realPn B d (j.val + 1))
  set Γ := Graph.flat (Graph.realPn B) (Graph.realLn B) (⟨C, W, n⟩ : Graph S ℕ)
  have hcd := Graph.WF.pair_ne hGwf
  have hcC := Graph.WF.pair_notMem_left hGwf
  have hdC := Graph.WF.pair_notMem_right hGwf
  obtain ⟨hc0, hd0⟩ := Graph.WF.port_zero_notMem hGwf
  have hndC : (C.map Prod.fst).Nodup := by
    have hnd := hGwf.nodup
    simp only [Multiset.map_cons, Multiset.nodup_cons] at hnd
    exact hnd.2.2
  set Lr' := Graph.renameList g' Lr with hLr'def
  have hLr' : Net.ofList Lr' = r.inst xs ys f := by
    rw [Graph.ofList_renameList, ← hLr, Rule.inst]
    congr 1
    funext x
    rcases x with i | j | w
    · simp only [leftPort, xs, Sum.elim_inl]
    · simp only [rightPort, ys, Sum.elim_inr, Sum.elim_inl]
    · simp only [wirePort, Sum.elim_inr]
  obtain ⟨LΓ, hLΓ, iΓ⟩ := Graph.stubGraph_iso_raw (Graph.realPn B) (Graph.realLn B)
    (⟨C, W, n⟩ : Graph S ℕ) hndC (0 + Graph.rawSize Lr')
  have hMtext : r.inst xs ys f + Γ = Net.ofList (Lr' ++ LΓ) := by
    rw [Graph.ofList_append, hLr', hLΓ]
  set SΓ := Graph.stubGraph (Graph.realPn B) (Graph.realLn B) (⟨C, W, n⟩ : Graph S ℕ) with hSΓ
  have iQ : ((Graph.raw D Lr').union SΓ).Iso (Graph.raw 0 (Lr' ++ LΓ)) := by
    rw [Graph.raw_append]
    refine (Graph.raw_shift_iso Lr' D 0).union iΓ (Graph.raw_portsIn D Lr')
      (Graph.stubGraph_portsIn _ _ _) ?_ ?_
    · intro x hx hx'
      rw [Graph.mem_raw_fst] at hx
      have := hDG x (by
        simp only [Multiset.map_cons, Multiset.mem_cons]
        exact Or.inr (Or.inr hx'))
      omega
    · intro x hx hx'
      rw [Graph.mem_raw_fst] at hx hx'
      omega
  -- contract the rule
  have hQ1 : Relation.ReflTransGen Graph.Contract ((Graph.raw D Lr').union SΓ)
      ((R'.mapEnd (End.map id g')).union SΓ) := by
    rw [hLr'def, Graph.raw_bind_var]
    exact Graph.contracts_union_right
      (Graph.contracts_mapEnd (f := End.map id g') (h := g') (fun _ => rfl) hR'c) SΓ
  -- erase the names of the stubs
  set P : Multiset (End ℕ) := C.bind Graph.cellPorts with hP
  set Wn : Multiset (Sym2 (End ℕ)) :=
    W.map (Sym2.map fun e => End.name (e.flatName (Graph.realPn B))) with hWn
  set Lp : Multiset (Sym2 (End ℕ)) := (Multiset.range n).map
    fun j => s(End.name (Graph.realLn B j), End.name (Graph.realLn B j)) with hLp
  set R'w := R'.wires.map (Sym2.map (End.map id g')) with hR'w
  set cut' := Graph.cutEnd c d (fun i => g' (.inl i)) (fun j => g' (.inr (.inl j))) with hcut'
  have e1 : (R'.mapEnd (End.map id g')).union SΓ =
      ⟨R'.cells + C, P.map (fun e => s(.name (e.flatName (Graph.realPn B)), e)) +
        (R'w + (Wn + Lp)), R'.loops⟩ := by
    simp only [Graph.union, Graph.mapEnd, hSΓ, Graph.stubGraph, Graph.mk.injEq, add_zero,
      true_and, and_true]
    exact add_left_comm _ _ _
  have hPp : ∀ e ∈ P, ∃ x i, e = End.port x i := fun e he => by
    obtain ⟨p, -, hp⟩ := Multiset.mem_bind.1 he
    obtain ⟨i, rfl, -⟩ := Graph.mem_cellPorts hp
    exact ⟨_, _, rfl⟩
  have hR'ends : ∀ z ∈ R'w.bind Graph.wireEnds, (∃ x i, z = End.port x i) ∨
      ∃ w, z = End.name (g' w) := fun z hz => by
    rw [hR'w, Graph.bind_wireEnds_map_end] at hz
    obtain ⟨z₀, -, rfl⟩ := Multiset.mem_map.1 hz
    cases z₀ with
    | port x i => exact Or.inl ⟨x, i, rfl⟩
    | name w => exact Or.inr ⟨w, rfl⟩
  have hLpends : ∀ z ∈ Lp.bind Graph.wireEnds, ∃ j, z = End.name (Graph.realLn B j) :=
    fun z hz => by
      obtain ⟨w, hw, hm⟩ := Multiset.mem_bind.1 hz
      obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hw
      simp only [Graph.wireEnds_mk, Multiset.insert_eq_cons, Multiset.mem_cons,
        Multiset.mem_singleton, or_self] at hm
      exact ⟨j, hm⟩
  have hstub := Graph.contracts_stubs (R'.cells + C) R'.loops (End.flatName (Graph.realPn B))
    (Graph.stubBack B P) (fun _ _ => rfl) P (R'w + (Wn + Lp)) hPp
    ((Graph.nodup_bind_cellPorts hndC).map_on fun e he e' he' hee => by
      obtain ⟨x, i, rfl⟩ := hPp e he
      obtain ⟨y, j, rfl⟩ := hPp e' he'
      simp only [End.flatName_port] at hee
      obtain ⟨rfl, rfl⟩ := Graph.realPn_inj hee
      rfl)
    (fun e he => by
      obtain ⟨x, i, rfl⟩ := hPp e he
      simp [Graph.stubBack, Graph.unflat_pn, he])
    (fun e he => by
      obtain ⟨x, i, rfl⟩ := hPp e he
      obtain ⟨γ, hγ, hi⟩ := Graph.mem_bind_cellPorts.1 he
      have hxc : x ≠ c := fun h => hcC (h ▸ Multiset.mem_map_of_mem Prod.fst hγ)
      have hxd : x ≠ d := fun h => hdC (h ▸ Multiset.mem_map_of_mem Prod.fst hγ)
      simp only [End.flatName_port]
      rw [Multiset.add_bind, Multiset.add_bind, Multiset.count_add, Multiset.count_add]
      have h1 : (R'w.bind Graph.wireEnds).count (.name (Graph.realPn B x i)) = 0 :=
        Multiset.count_eq_zero.2 fun hm => by
          rcases hR'ends _ hm with ⟨y, j, e⟩ | ⟨w, e⟩
          · cases e
          · exact hg'P _ he w (End.name.inj e).symm
      have h2 : (Wn.bind Graph.wireEnds).count (.name (Graph.realPn B x i)) = 1 := by
        rw [hWn, Graph.bind_wireEnds_map, Graph.count_map_eq_of_iff (a := End.port x i)]
        · have := hGwf.port x γ (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hγ)) i hi
          rw [Graph.ends_pair, Multiset.count_cons_of_ne (by simp [hxc]),
            Multiset.count_cons_of_ne (by simp [hxd])] at this
          exact this
        · intro z hz
          cases z with
          | port y j =>
            simp only [End.flatName_port, End.name.injEq, End.port.injEq]
            exact ⟨fun e => by obtain ⟨rfl, rfl⟩ := Graph.realPn_inj e; exact ⟨rfl, rfl⟩,
              fun ⟨e1, e2⟩ => by rw [e1, e2]⟩
          | name y =>
            simp only [End.flatName_name, End.name.injEq, reduceCtorEq, iff_false]
            intro e
            have := hWB y hz
            have := Graph.le_realPn B x i
            omega
      have h3 : (Lp.bind Graph.wireEnds).count (.name (Graph.realPn B x i)) = 0 :=
        Multiset.count_eq_zero.2 fun hm => by
          obtain ⟨j, e⟩ := hLpends _ hm
          exact Graph.realPn_ne_realLn B x i j (End.name.inj e)
      rw [h1, h2, h3])
    (fun y _ hy => by
      simp only [Graph.stubBack] at hy
      split_ifs at hy with hmem
      · obtain ⟨x, i, hxi⟩ := hPp _ hmem
        refine ⟨_, hmem, ?_⟩
        rw [hxi, End.flatName_port, Graph.unflat_eq_port hxi]
      · exact absurd rfl hy)
  -- the result of erasing the stubs
  have hbR : R'w.map (Sym2.map (Graph.stubBack B P)) = R'w := by
    refine Graph.map_wires_eq_self fun z hz => ?_
    rcases hR'ends z hz with ⟨x, i, rfl⟩ | ⟨w, rfl⟩
    · rfl
    · simp only [Graph.stubBack]
      refine ite_eq_right_of_eq_false _ _ (eq_false fun hmem => ?_)
      obtain ⟨x, i, hxi⟩ := hPp _ hmem
      exact hg'P (End.port x i) (hxi ▸ hmem) w (Graph.unflat_eq_port hxi)
  have hbL : Lp.map (Sym2.map (Graph.stubBack B P)) = Lp := by
    refine Graph.map_wires_eq_self fun z hz => ?_
    obtain ⟨j, rfl⟩ := hLpends z hz
    simp only [Graph.stubBack, Graph.unflat_ln]
    rw [ite_eq_right_of_eq_false _ _ (eq_false (Graph.name_notMem_bind_cellPorts C _))]
  have hbW : Wn.map (Sym2.map (Graph.stubBack B P)) = W.map (Sym2.map cut') := by
    rw [hWn, Multiset.map_map, ← Sym2.map_comp]
    refine Graph.map_wires_congr_ends fun z hz => ?_
    simp only [Function.comp_apply]
    cases z with
    | name y =>
      have hy := hWB y hz
      simp only [End.flatName_name, Graph.stubBack, Graph.unflat_low hy,
        hcut', Graph.cutEnd]
      split_ifs <;> rfl
    | port x i =>
      obtain ⟨γ, hγ, hi⟩ := hGwf.cell x i (by
        rw [Graph.ends_pair]
        exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hz))
      simp only [End.flatName_port, Graph.stubBack, Graph.unflat_pn]
      rcases Multiset.mem_cons.1 hγ with he | he
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        cases i with
        | zero => exact absurd hz hc0
        | succ k =>
          have hk : k < S.arity γ := by omega
          rw [ite_eq_right_of_eq_false _ _ (eq_false fun hm => hcC (by
            obtain ⟨δ, hδ, -⟩ := Graph.mem_bind_cellPorts.1 hm
            exact Multiset.mem_map_of_mem Prod.fst hδ))]
          simp [hcut', Graph.cutEnd, hk, leftPort]
      · rcases Multiset.mem_cons.1 he with he | he
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          cases i with
          | zero => exact absurd hz hd0
          | succ k =>
            have hk : k < S.arity γ := by omega
            rw [ite_eq_right_of_eq_false _ _ (eq_false fun hm => hdC (by
              obtain ⟨δ, hδ, -⟩ := Graph.mem_bind_cellPorts.1 hm
              exact Multiset.mem_map_of_mem Prod.fst hδ))]
            simp [hcut', Graph.cutEnd, hk, rightPort, Ne.symm hcd]
        · have hxc : x ≠ c := fun h => hcC (h ▸ Multiset.mem_map_of_mem Prod.fst he)
          have hxd : x ≠ d := fun h => hdC (h ▸ Multiset.mem_map_of_mem Prod.fst he)
          rw [ite_eq_left_of_eq_true _ _ (eq_true (Graph.mem_bind_cellPorts.2 ⟨γ, he, hi⟩)), hcut',
            Graph.cutEnd_port_of_ne hxc hxd]
  -- the cyclic wires
  have hloops := Graph.contracts_loops (R'.cells + C) (Graph.realLn B) n R'.loops
    (W.map (Sym2.map cut') + R'w)
  have hfin : (⟨R'.cells + C, W.map (Sym2.map cut') + R'w, R'.loops + n⟩ : Graph S ℕ) =
      Graph.preInteract c d C W n R' id g' := by
    simp only [Graph.preInteract, Prod.map_id, Multiset.map_id, Graph.mk.injEq, hR'w, hcut']
    exact ⟨add_comm _ _, trivial, add_comm _ _⟩
  have hchain : Relation.ReflTransGen Graph.Contract ((Graph.raw D Lr').union SΓ) H' := by
    refine hQ1.trans ?_
    rw [e1]
    refine hstub.trans ?_
    rw [Multiset.map_add, Multiset.map_add, hbR, hbL, hbW,
      show R'w + (W.map (Sym2.map cut') + Lp) = Lp + (W.map (Sym2.map cut') + R'w) by abel]
    refine hloops.trans ?_
    rw [hfin]
    exact hH'
  obtain ⟨H'', hH'', iH''⟩ := iQ.contracts hchain
  exact ⟨H'', ⟨Lr' ++ LΓ, 0, hMtext, hH'', fun x =>
    (iH''.count_name x).trans_le (hH'1 x)⟩, iH''⟩

/-- **An interaction of graphs is an interaction of texts** (Lafont 1997, Section 1.2, page 73;
the converse of `GraphStepE.lean`). Let the rules of `I` be linear, `N` a linear net with graph
`G`, and `Graph.Interact I G H` one interaction of `G`. Then `N` has a step `StepE I N M` whose
result `M` has a graph `H'` isomorphic to `H`. -/
theorem Net.Linear.interact_stepE
    -- the interaction system, whose rules are linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- the linear net
    {N : Net S ℕ}
    (hN : N.Linear)
    -- its graph `G`, and an interaction from `G` to `H`
    {G H : Graph S ℕ}
    (hG : N.HasGraph G)
    (h : Graph.Interact I G H) :
    -- there are a net `M` and a graph `H'` such that
    ∃ M H',
      -- `N` makes one step, up to wires, to `M`,
      StepE I N M ∧
      -- `H'` is a graph of `M`,
      M.HasGraph H' ∧
      -- and `H` is isomorphic to `H'`
      H.Iso H' := by
  classical
  obtain ⟨c, d, α, β, C, W, n, r, hr, R, hR, σ, hσ, hσG, g, hg, hgW, H, hH, hH1⟩ := h
  have hrl := hI _ _ _ hr
  have hGwf := hG.wf
  have hcd : c ≠ d := Graph.WF.pair_ne hGwf
  have hcC := Graph.WF.pair_notMem_left hGwf
  have hdC := Graph.WF.pair_notMem_right hGwf
  -- the flat text of `G`
  obtain ⟨G', hG', iG'⟩ := hGwf.hasGraph_flatB
  have hlin := Graph.linear_flatB hGwf
  have E1 := hN.equiv_of_hasGraph_iso hlin hG hG' (iG'.symm hG'.wf.portsIn)
  have hB : ∀ y, End.name y ∈ Graph.ends (⟨(c, α) ::ₘ (d, β) ::ₘ C,
      s(.port c 0, .port d 0) ::ₘ W, n⟩ : Graph S ℕ) →
      y < Graph.freeBound (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ :
        Graph S ℕ) := fun y hy => Graph.lt_freeBound hy
  change Equiv N (Graph.flat (Graph.realPn (Graph.freeBound _)) (Graph.realLn (Graph.freeBound _))
    _) at E1
  change (Graph.flat (Graph.realPn (Graph.freeBound _)) (Graph.realLn (Graph.freeBound _))
    _).Linear at hlin
  generalize Graph.freeBound (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ :
    Graph S ℕ) = B at hB E1 hlin
  have hWB : ∀ y, End.name y ∈ W.bind Graph.wireEnds → y < B := fun y hy =>
    hB y (by
      rw [Graph.ends_pair]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hy))
  -- the active pair made literal
  set Γ : Net S ℕ := Graph.flat (Graph.realPn B) (Graph.realLn B) ⟨C, W, n⟩ with hΓ
  let xs : Fin (S.arity α) → Term S ℕ := fun i => var (Graph.realPn B c ((i : ℕ) + 1))
  let ys : Fin (S.arity β) → Term S ℕ := fun j => var (Graph.realPn B d ((j : ℕ) + 1))
  have hflat : Graph.flat (Graph.realPn B) (Graph.realLn B)
      (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ : Graph S ℕ) =
      s(var (Graph.realPn B c 0), app α xs) ::ₘ s(var (Graph.realPn B d 0), app β ys) ::ₘ
        s(var (Graph.realPn B c 0), var (Graph.realPn B d 0)) ::ₘ Γ := by
    simp only [hΓ, Graph.flat, Graph.flatCells, Graph.flatWires, Multiset.map_cons,
      Multiset.cons_add, Multiset.add_cons]
    rw [Multiset.cons_swap (Graph.flatWire _ _) (Graph.cellEq _ (c, α)),
      Multiset.cons_swap (Graph.flatWire _ _) (Graph.cellEq _ (d, β))]
    rfl
  have hq0 : Graph.realPn B d 0 ∉ (app α xs).vars := by
    simp only [vars_app, xs, vars_var, Multiset.mem_sum, Finset.mem_univ, true_and,
      Multiset.mem_singleton, not_exists]
    intro i e
    exact hcd (Graph.realPn_inj e).1.symm
  have hpq : Graph.realPn B c 0 ≠ Graph.realPn B d 0 := fun e => hcd (Graph.realPn_inj e).1
  have W1 : Wire (s(var (Graph.realPn B c 0), app α xs) ::ₘ
      s(var (Graph.realPn B c 0), var (Graph.realPn B d 0)) ::ₘ
        (s(var (Graph.realPn B d 0), app β ys) ::ₘ Γ))
      (s(app α xs, var (Graph.realPn B d 0)) ::ₘ s(var (Graph.realPn B d 0), app β ys) ::ₘ Γ) := by
    refine (Wire.mk (Graph.realPn B c 0) (app α xs) (var (Graph.realPn B c 0))
      (var (Graph.realPn B d 0)) (s(var (Graph.realPn B d 0), app β ys) ::ₘ Γ) ?_
      (by simp)).cast rfl ?_
    · rw [hflat] at hlin
      exact hlin.cast (by rw [Multiset.cons_swap (s(var (Graph.realPn B d 0), app β ys))])
    · rw [Term.subst_of_notMem (by simpa using hpq : Graph.realPn B c 0 ∉
        (var (Graph.realPn B d 0) : Term S ℕ).vars)]
      simp [Term.subst]
  have W2 : Wire (s(var (Graph.realPn B d 0), app β ys) ::ₘ s(app α xs, var (Graph.realPn B d 0))
      ::ₘ Γ) (s(app α xs, app β ys) ::ₘ Γ) := by
    refine (Wire.mk (Graph.realPn B d 0) (app β ys) (app α xs) (var (Graph.realPn B d 0)) Γ ?_
      (by simp)).cast rfl ?_
    · exact W1.linear_right.cast (Multiset.cons_swap _ _ _)
    · rw [Term.subst_of_notMem hq0]
      simp [Term.subst]
  have E2 : Equiv (Graph.flat (Graph.realPn B) (Graph.realLn B)
      (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ : Graph S ℕ))
      (s(app α xs, app β ys) ::ₘ Γ) := by
    rw [hflat]
    refine (Equiv.of_eq ?_).trans (W1.equiv.trans ((Equiv.of_eq (Multiset.cons_swap _ _ _)).trans
      W2.equiv))
    rw [Multiset.cons_swap (s(var (Graph.realPn B d 0), app β ys))]
  -- the step
  obtain ⟨F, hF⟩ := Net.exists_below (s(app α xs, app β ys) ::ₘ Γ)
  let f : Fin r.internal → ℕ := fun w => F + w
  have hf : Function.Injective f := fun a b e => Fin.ext (by simp only [f] at e; omega)
  have hfresh : ∀ w, f w ∉ Net.vars (s(app α xs, app β ys) ::ₘ Γ) := fun w hm => by
    have := hF _ hm
    simp only [f] at this
    omega
  have hstep : StepE I N (r.inst xs ys f + Γ) :=
    ⟨_, E1.trans E2, Step.mk α β r hr xs ys Γ f hf hfresh⟩
  -- names of the redex
  have hvΓ : ∀ y ∈ Γ.vars, y ∈ Net.vars (s(app α xs, app β ys) ::ₘ Γ) := fun y hy => by
    rw [Net.vars_cons]
    exact Multiset.mem_add.2 (Or.inr hy)
  have hvxs : ∀ i : Fin (S.arity α),
      Graph.realPn B c ((i : ℕ) + 1) ∈ Net.vars (s(app α xs, app β ys) ::ₘ Γ) := fun i => by
    simp only [Net.vars_cons, eqVars_mk, vars_app, Multiset.mem_add, Multiset.mem_sum,
      Finset.mem_univ, true_and, xs, ys, vars_var, Multiset.mem_singleton]
    exact Or.inl (Or.inl ⟨i, rfl⟩)
  have hvys : ∀ j : Fin (S.arity β),
      Graph.realPn B d ((j : ℕ) + 1) ∈ Net.vars (s(app α xs, app β ys) ::ₘ Γ) := fun j => by
    simp only [Net.vars_cons, eqVars_mk, vars_app, Multiset.mem_add, Multiset.mem_sum,
      Finset.mem_univ, true_and, xs, ys, vars_var, Multiset.mem_singleton]
    exact Or.inl (Or.inr ⟨j, rfl⟩)
  have hvP : ∀ e ∈ C.bind Graph.cellPorts, e.flatName (Graph.realPn B) ∈ Γ.vars := fun e he => by
    rw [hΓ, Graph.vars_flat]
    exact Multiset.mem_add.2 (Or.inl (Multiset.mem_map_of_mem _ (Multiset.mem_add.2 (Or.inl he))))
  have hvW : ∀ y, End.name y ∈ W.bind Graph.wireEnds → y ∈ Γ.vars := fun y hy => by
    rw [hΓ, Graph.vars_flat]
    exact Multiset.mem_add.2 (Or.inl (Multiset.mem_map_of_mem (End.flatName (Graph.realPn B))
      (Multiset.mem_add.2 (Or.inr hy))))
  -- the fresh names of the interaction: the names of the auxiliary ports, and `f`
  let g' : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal → ℕ :=
    Sum.elim (fun i => Graph.realPn B c ((i : ℕ) + 1))
      (Sum.elim (fun j => Graph.realPn B d ((j : ℕ) + 1)) f)
  have hg' : Function.Injective g' := by
    rintro (i | j | w) (i' | j' | w') e <;> simp only [g', Sum.elim_inl, Sum.elim_inr] at e
    · obtain ⟨-, h⟩ := Graph.realPn_inj e
      exact congrArg _ (Fin.ext (by omega))
    · exact absurd (Graph.realPn_inj e).1 hcd
    · exact absurd (by rw [← e]; exact hvxs i) (hfresh w')
    · exact absurd (Graph.realPn_inj e).1 (Ne.symm hcd)
    · obtain ⟨-, h⟩ := Graph.realPn_inj e
      exact congrArg _ (congrArg _ (Fin.ext (by omega)))
    · exact absurd (by rw [← e]; exact hvys j) (hfresh w')
    · exact absurd (by rw [e]; exact hvxs i') (hfresh w)
    · exact absurd (by rw [e]; exact hvys j') (hfresh w)
    · exact congrArg _ (congrArg _ (hf e))
  have hgW' : ∀ w, End.name (g' w) ∉ W.bind Graph.wireEnds := by
    rintro (i | j | w) hm <;> simp only [g', Sum.elim_inl, Sum.elim_inr] at hm
    · have := hWB _ hm
      have := Graph.le_realPn B c ((i : ℕ) + 1)
      omega
    · have := hWB _ hm
      have := Graph.le_realPn B d ((j : ℕ) + 1)
      omega
    · exact hfresh w (hvΓ _ (hvW _ hm))
  have hg'P : ∀ e ∈ C.bind Graph.cellPorts, ∀ w, g' w ≠ e.flatName (Graph.realPn B) := by
    intro e he w hw
    obtain ⟨p, hp, hep⟩ := Multiset.mem_bind.1 he
    obtain ⟨i, rfl, -⟩ := Graph.mem_cellPorts hep
    have hxC : p.1 ∈ C.map Prod.fst := Multiset.mem_map_of_mem Prod.fst hp
    rcases w with k | k | w <;> simp only [g', Sum.elim_inl, Sum.elim_inr, End.flatName_port] at hw
    · exact hcC ((Graph.realPn_inj hw).1 ▸ hxC)
    · exact hdC ((Graph.realPn_inj hw).1 ▸ hxC)
    · exact hfresh w (hvΓ _ (by rw [hw]; exact hvP _ he))
  -- a graph of the rule, numbered above the cells of `G`
  set D := (((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst).sup + 1 with hD
  have hDG : ∀ x ∈ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst, x < D := fun x hx =>
    Nat.lt_succ_of_le (Multiset.le_sup hx)
  obtain ⟨Lr, hLr⟩ := Net.exists_ofList r.net
  obtain ⟨R', hR'c, hR'1⟩ := Graph.exists_contracts (Graph.raw D Lr)
  have hR' : r.net.HasGraph R' := ⟨Lr, D, hLr, hR'c, hR'1⟩
  have hσG' : ∀ x ∈ R'.cells.map Prod.fst,
      (id x : ℕ) ∉ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst := fun x hx hm => by
    rw [Graph.contracts_cells_eq hR'c, Graph.mem_raw_fst] at hx
    have := hDG _ hm
    simp only [id] at this
    omega
  -- the interaction with these choices, and the uniqueness of its result
  obtain ⟨H', hH', hH'1⟩ := Graph.exists_contracts (Graph.preInteract c d C W n R' id g')
  have iHH' : H.Iso H' := Graph.interact_unique hGwf hrl hR hR' hσ hσG (Set.injOn_id _) hσG'
    hg hgW hg' hgW' hH hH1 hH' hH'1
  -- a text of the result
  obtain ⟨H'', hGraph, hIso⟩ :=
    inst_hasGraph_after_preInteract (f := f) hGwf hLr hR'c hH' hH'1 hWB hDG hg'P
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  exact ⟨_, H'', hstep, hGraph, iHH'.trans hIso⟩

end INet
