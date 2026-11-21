/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Graphs.GraphStep
public import LeanPool.InteractionCombinators.Translations.Simulation
public import LeanPool.InteractionCombinators.Graphs.GraphEquiv

/-!
# An interaction of texts is an interaction of graphs

Lafont 1997, Section 1.2, page 73: an interaction rule replaces two cells joined by their
principal ports by the right-hand side of the rule. On texts this is `StepE`, a wire substitution
followed by `Step`; on graphs it is `Graph.Interact`. This file proves the forward direction: the
graph of the result of a step is, up to `Graph.Iso`, the result of one interaction on the graph.

The proof expands the active pair twice (`Simulation.equiv_expand`): its auxiliary ports carry
fresh names `F + i`, which the rest of the net `Γ` plugs into the trees of the pair. The raw graph
of this text, contracted inside `Γ`, is the graph `G₁` to which the interaction applies; cutting
`G₁` and gluing a graph of the rule gives a graph that is literally the raw graph of a text of the
result, with the rule renamed and the wires `G' + i = F + i` added, contracted inside `Γ` and
inside the rule. That text is the result up to wires (`Simulation.equiv_contract_inst`, twice).

The rules are assumed linear, as Lafont's rules are (page 73); `StepE` alone does not give it.
The hypothesis is not decoration: a rule that does not use the auxiliary port of a cell erases the
tree plugged into it on texts, while the interaction on graphs keeps that tree, attached to a free
port, so the two results have different cells. (This is an informal remark; no refutation of the
statement without the hypothesis is formalized.)

The example on the combinators is in `Checks/Graphs/GraphStepECheck.lean`.

Contents, in the order of the file:

1. Definitions: `Graph.mapEnd`, renaming the ends of the wires of a graph, keeping its cells;
   `Graph.renameList`, renaming the names of a list of equations.
2. Auxiliary lemmas, contraction and renaming: `Graph.Contract.mapEnd`, `Graph.contracts_mapEnd`
   (contraction commutes with renaming the ends), `Graph.Contract.union_right`,
   `Graph.contracts_union_right`, `Graph.contracts_union_left` (contraction can be done beside
   another graph).
3. Auxiliary lemmas, the raw graph of a renamed text: `Term.size_bind_var`,
   `Term.rawCells_bind_var`, `Term.rootEnd_bind_var`, `Term.rawWires_bind_var`;
   `Graph.raw_bind_var` (the raw graph of a renamed text is the renamed raw graph),
   `Graph.ofList_renameList`, `Graph.raw_vars`, `Graph.rawSize_vars`, `Graph.ofList_append`.
4. Auxiliary lemmas, an interaction of isomorphic graphs: `Graph.mapCell_endMap`,
   `Graph.mapCell_cutEnd`, `Graph.map_wires_mapCell_congr`; `Graph.Interact.iso`, an interaction
   of a graph is an interaction of every isomorphic graph.
5. Auxiliary lemmas, the active pair with names on its auxiliary ports: `Graph.coe_ofFn_eq_sum`,
   `Graph.size_app_var`, `Graph.rawCells_app_var`, `Graph.rawWires_app_var`,
   `Graph.map_cutEnd_left`, `Graph.map_cutEnd_right`, `Graph.map_cutEnd_of_ports` (the cut on
   the wires of the pair and of the rest of the net); `Simulation.mem_vars_expand`.
6. Main result: `Net.Linear.stepE_interact`, a step `StepE I N M` of a linear net with linear
   rules is an interaction of the graph of `N`, whose result is isomorphic to a graph of `M`.
-/

@[expose] public section

namespace INet

variable {S : Signature} {ν μ : Type}

open Term

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

namespace Graph

/-- Renaming the ends of the wires of a graph by `f`; the cells and the cyclic wires are kept. -/
def mapEnd
    -- the renaming of the ends
    (f : End ν → End μ)
    -- the graph
    (G : Graph S ν) :
    Graph S μ :=
  ⟨G.cells, G.wires.map (Sym2.map f), G.loops⟩

/-- Renaming the names of the equations of a list. -/
def renameList
    -- the renaming of the names
    (ρ : ν → μ)
    -- the list of equations
    (L : List (Term S ν × Term S ν)) :
    List (Term S μ × Term S μ) :=
  L.map fun e => (e.1.bind fun x => var (ρ x), e.2.bind fun x => var (ρ x))

-- ============================================================================================
-- 2. Auxiliary lemmas: contraction and renaming
-- ============================================================================================

/-- **A contraction is a contraction of the renamed graph** (Lafont 1997, page 71), when the
renaming sends names to names. -/
theorem Contract.mapEnd
    -- a renaming of the ends that sends each name `x` to the name `h x`
    {f : End ν → End μ}
    {h : ν → μ}
    (hf : ∀ x, f (.name x) = .name (h x))
    -- one contraction from `G` to `H`
    {G H : Graph S ν}
    (c : Contract G H) :
    -- is one contraction of the renamed graphs
    Contract (G.mapEnd f) (H.mapEnd f) := by
  cases c with
  | join x p q C W n =>
    simp only [Graph.mapEnd, Multiset.map_cons, Sym2.map_mk, hf]
    exact .join (h x) (f p) (f q) C _ n
  | loop x C W n =>
    simp only [Graph.mapEnd, Multiset.map_cons, Sym2.map_mk, hf]
    exact .loop (h x) C _ n

/-- **Contractions are contractions of the renamed graph** (Lafont 1997, page 71). -/
theorem contracts_mapEnd
    -- a renaming of the ends that sends each name `x` to the name `h x`
    {f : End ν → End μ}
    {h : ν → μ}
    (hf : ∀ x, f (.name x) = .name (h x))
    -- contractions from `G` to `H`
    {G H : Graph S ν}
    (c : Relation.ReflTransGen Contract G H) :
    -- are contractions of the renamed graphs
    Relation.ReflTransGen Contract (G.mapEnd f) (H.mapEnd f) := by
  induction c with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (s.mapEnd hf)

/-- **A contraction can be done beside another graph** (Lafont 1997, page 71). -/
theorem Contract.union_right
    -- one contraction from `G` to `H`
    {G H : Graph S ν}
    (c : Contract G H)
    -- another graph
    (K : Graph S ν) :
    -- is one contraction of the unions with `K` on the right
    Contract (G.union K) (H.union K) := by
  cases c with
  | join x p q C W n =>
    simp only [union, Multiset.cons_add]
    exact .join x p q _ _ _
  | loop x C W n =>
    have e : n + 1 + K.loops = n + K.loops + 1 := by omega
    simp only [union, Multiset.cons_add, e]
    exact .loop x _ _ _

/-- **Contractions can be done beside another graph, on the left** (Lafont 1997, page 71). -/
theorem contracts_union_right
    -- contractions from `G` to `H`
    {G H : Graph S ν}
    (c : Relation.ReflTransGen Contract G H)
    -- another graph
    (K : Graph S ν) :
    -- are contractions of the unions with `K` on the right
    Relation.ReflTransGen Contract (G.union K) (H.union K) := by
  induction c with
  | refl => exact .refl
  | tail _ s ih => exact ih.tail (s.union_right K)

/-- **Contractions can be done beside another graph, on the right** (Lafont 1997, page 71). -/
theorem contracts_union_left
    -- contractions from `G` to `H`, and another graph `K`
    {G H : Graph S ν}
    (K : Graph S ν)
    (c : Relation.ReflTransGen Contract G H) :
    -- are contractions of the unions with `K` on the left
    Relation.ReflTransGen Contract (K.union G) (K.union H) := by
  rw [union_comm K G, union_comm K H]
  exact contracts_union_right c K

end Graph

-- ============================================================================================
-- 3. Auxiliary lemmas: the raw graph of a renamed text
-- ============================================================================================

-- the image of a finite sum of multisets is the sum of the images
private theorem map_finsum_multiset
    -- the multisets `g i`, for `i` in `s`
    {ι α β : Type}
    (s : Finset ι)
    (g : ι → Multiset α)
    -- the map
    (f : α → β) :
    (∑ i ∈ s, g i).map f = ∑ i ∈ s, (g i).map f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => simp [Finset.sum_insert ha, ih]

namespace Term

/-- Renaming the names of a tree keeps its number of cells. -/
theorem size_bind_var
    -- the renaming and the tree
    (ρ : ν → μ)
    (t : Term S ν) :
    (t.bind fun x => var (ρ x)).size = t.size := by
  induction t with
  | var x => rfl
  | app α ts ih =>
    simp only [bind_app, size]
    congr 1
    exact Finset.sum_congr rfl fun i _ => ih i

-- renaming the names of the children keeps the numbers of their first cells
theorem childBase_bind_var
    -- the renaming
    (ρ : ν → μ)
    -- the children `ts`, numbered from `k`, and one of them
    {n : ℕ}
    (k : ℕ)
    (ts : Fin n → Term S ν)
    (i : Fin n) :
    childBase k (fun i => (ts i).bind fun x => var (ρ x)) i = childBase k ts i := by
  simp only [childBase, size_bind_var]

/-- Renaming the names of a tree keeps its cells (Lafont 1997, page 71). -/
theorem rawCells_bind_var
    -- the renaming, the tree, and the number of its first cell
    (ρ : ν → μ)
    (t : Term S ν)
    (k : ℕ) :
    (t.bind fun x => var (ρ x)).rawCells k = t.rawCells k := by
  induction t generalizing k with
  | var x => rfl
  | app α ts ih =>
    simp only [bind_app, rawCells, childBase_bind_var, ih]

/-- The root of a renamed tree is the renamed root. -/
theorem rootEnd_bind_var
    -- the renaming, the tree, and the number of its first cell
    (ρ : ν → μ)
    (t : Term S ν)
    (k : ℕ) :
    (t.bind fun x => var (ρ x)).rootEnd k = End.map id ρ (t.rootEnd k) := by
  cases t <;> rfl

/-- The inner wires of a renamed tree are the renamed inner wires (Lafont 1997, page 71). -/
theorem rawWires_bind_var
    -- the renaming, the tree, and the number of its first cell
    (ρ : ν → μ)
    (t : Term S ν)
    (k : ℕ) :
    (t.bind fun x => var (ρ x)).rawWires k
      = (t.rawWires k).map (Sym2.map (End.map id ρ)) := by
  induction t generalizing k with
  | var x => rfl
  | app α ts ih =>
    simp only [bind_app, rawWires, childBase_bind_var, ih, rootEnd_bind_var, map_finsum_multiset,
      Multiset.map_cons, Sym2.map_mk]
    rfl

end Term

namespace Graph

/-- **The raw graph of a renamed text** is the raw graph with its names renamed (Lafont 1997,
page 71). -/
theorem raw_bind_var
    -- the renaming, the number of the first cell, and the list of equations
    (ρ : ν → μ)
    (k : ℕ)
    (L : List (Term S ν × Term S ν)) :
    raw k (renameList ρ L) = (raw k L).mapEnd (End.map id ρ) := by
  induction L generalizing k with
  | nil => simp [renameList, raw, mapEnd]
  | cons e L ih =>
    obtain ⟨a, b⟩ := e
    have ih' := ih (k + a.size + b.size)
    simp only [renameList] at ih'
    simp only [renameList, List.map_cons, raw, Term.size_bind_var, Term.rawCells_bind_var,
      Term.rootEnd_bind_var, Term.rawWires_bind_var, ih', mapEnd, Multiset.map_cons,
      Multiset.map_add, Sym2.map_mk]

/-- The text of a renamed list is the renamed text. -/
theorem ofList_renameList
    -- the renaming and the list of equations
    (ρ : ν → μ)
    (L : List (Term S ν × Term S ν)) :
    Net.ofList (renameList ρ L) = (Net.ofList L).bind fun x => var (ρ x) := by
  simp only [Net.ofList, renameList, Net.bind, Multiset.map_coe, List.map_map]
  congr 1

/-- The raw graph of a list of equations between names: no cell, one wire for each equation. -/
theorem raw_vars
    -- the number of the first cell, and the list of pairs of names
    (k : ℕ)
    (L : List (ν × ν)) :
    raw (S := S) k (L.map fun e => (var e.1, var e.2))
      = ⟨0, ((L.map fun e => s(End.name e.1, End.name e.2) : List _) : Multiset _), 0⟩ := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [List.map_cons, raw, Term.size, add_zero, ih, Term.rawCells, Term.rawWires,
      Term.rootEnd, zero_add, Multiset.cons_coe]

-- a list of equations between names has no cell
theorem rawSize_vars
    -- the list of pairs of names
    (L : List (ν × ν)) :
    rawSize (S := S) (L.map fun e => (var e.1, var e.2)) = 0 := by
  induction L with
  | nil => rfl
  | cons e L ih =>
    simp only [rawSize, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]
    rfl

/-- The text of two lists of equations. -/
theorem ofList_append
    -- the two lists
    (A B : List (Term S ν × Term S ν)) :
    Net.ofList (A ++ B) = Net.ofList A + Net.ofList B := by
  simp [Net.ofList]

-- ============================================================================================
-- 4. Auxiliary lemmas: an interaction of isomorphic graphs
-- ============================================================================================

-- renaming the cells after renaming the cells and the names is renaming both at once
theorem mapCell_endMap
    -- the two renamings of the cells, and the renaming of the names
    (τ σ : ℕ → ℕ)
    {ν : Type}
    (g : ν → ℕ) :
    End.mapCell τ ∘ End.map σ g = End.map (τ ∘ σ) g := by
  funext z; cases z <;> rfl

/-- An injective renaming of the cells commutes with the cut, the two cells renamed. -/
theorem mapCell_cutEnd
    -- an injective renaming of the cells
    {τ : ℕ → ℕ}
    (hτ : Function.Injective τ)
    -- the two cells of the cut, and the fresh names of their auxiliary ports
    (c d : ℕ)
    {a b : ℕ}
    (u : Fin a → ℕ)
    (v : Fin b → ℕ)
    -- an end
    (z : End ℕ) :
    End.mapCell τ (cutEnd c d u v z) = cutEnd (τ c) (τ d) u v (End.mapCell τ z) := by
  match z with
  | .name x => rfl
  | .port e 0 => rfl
  | .port e (k + 1) =>
    have hc : τ e = τ c ↔ e = c := hτ.eq_iff
    have hd : τ e = τ d ↔ e = d := hτ.eq_iff
    simp only [cutEnd, End.mapCell, hc, hd]
    split_ifs <;> rfl

/-- Two renamings that agree on the cells of the ports at the ends of some wires rename these
wires alike. -/
theorem map_wires_mapCell_congr
    -- the wires
    {W : Multiset (Sym2 (End ν))}
    -- two renamings of the cells that agree on every cell with a port at an end of `W`
    {ρ σ : ℕ → ℕ}
    (h : ∀ c i, End.port c i ∈ W.bind wireEnds → ρ c = σ c) :
    W.map (Sym2.map (End.mapCell ρ)) = W.map (Sym2.map (End.mapCell σ)) := by
  apply Multiset.map_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ p q =>
    have key : ∀ r ∈ ({p, q} : Multiset (End ν)), End.mapCell ρ r = End.mapCell σ r := by
      intro r hr
      cases r with
      | name x => rfl
      | port c i =>
        change End.port (ρ c) i = End.port (σ c) i
        rw [h c i (Multiset.mem_bind.2 ⟨_, he, by rwa [wireEnds_mk]⟩)]
    simp only [Sym2.map_mk]
    rw [key p (by simp), key q (by simp)]

/-- **An interaction of a graph is an interaction of every isomorphic graph** (Lafont 1997,
Section 1.2, page 73): if `G` has an interaction giving `H` and `G` is isomorphic to `G'`, then
`G'` has an interaction giving a graph isomorphic to `H`. Every port at an end of a wire of `G`
is assumed to be a port of a cell of `G`, as in a well-formed graph. -/
theorem Interact.iso
    -- the interaction system
    {I : System S}
    -- an interaction from `G` to `H`, and a graph `G'` isomorphic to `G`
    {G G' H : Graph S ℕ}
    (h : Interact I G H)
    (hi : G.Iso G')
    -- every port at an end of a wire of `G` is a port of a cell of `G`
    (hG : ∀ c i, End.port c i ∈ G.ends → c ∈ G.cells.map Prod.fst) :
    -- `G'` has an interaction giving a graph `H'`
    ∃ H', Interact I G' H' ∧
      -- isomorphic to `H`
      H.Iso H' := by
  classical
  obtain ⟨c, d, α, β, C, W, n, r, hr, R, hR, σ, hσ, hσG, g, hg, hgW, H, hH, hH1⟩ := h
  obtain ⟨τ, hτ, hc, hw, hl⟩ := hi
  obtain ⟨C', W', n'⟩ := G'
  simp only at hc hw hl
  subst hc hw
  rw [hl]
  set s := ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst with hs
  set B := (((c, α) ::ₘ (d, β) ::ₘ C).map (Prod.map τ id) |>.map Prod.fst).sup + 1 with hB
  let τ' : ℕ → ℕ := fun x => if x ∈ s then τ x else B + x
  have hlt : ∀ x ∈ s, τ x < B := fun x hx => by
    have : τ x ∈ (((c, α) ::ₘ (d, β) ::ₘ C).map (Prod.map τ id)).map Prod.fst := by
      rw [Multiset.map_map]
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
      exact Multiset.mem_map.2 ⟨p, hp, rfl⟩
    exact Nat.lt_succ_of_le (Multiset.le_sup this)
  have eq_s : ∀ x ∈ s, τ' x = τ x := fun x hx => by simp [τ', hx]
  have eq_n : ∀ x, x ∉ s → τ' x = B + x := fun x hx => by simp [τ', hx]
  have hτ' : Function.Injective τ' := by
    intro x y e
    by_cases hx : x ∈ s <;> by_cases hy : y ∈ s
    · rw [eq_s x hx, eq_s y hy] at e
      exact hτ hx hy e
    · rw [eq_s x hx, eq_n y hy] at e
      have := hlt x hx
      omega
    · rw [eq_n x hx, eq_s y hy] at e
      have := hlt y hy
      omega
    · rw [eq_n x hx, eq_n y hy] at e
      omega
  have hcs : c ∈ s := by simp [hs]
  have hds : d ∈ s := by simp [hs]
  -- the graph `G'`, written with `τ'`
  have hC' : ((c, α) ::ₘ (d, β) ::ₘ C).map (Prod.map τ id) =
      (τ' c, α) ::ₘ (τ' d, β) ::ₘ C.map (Prod.map τ' id) := by
    have : ((c, α) ::ₘ (d, β) ::ₘ C).map (Prod.map τ id) =
        ((c, α) ::ₘ (d, β) ::ₘ C).map (Prod.map τ' id) :=
      Multiset.map_congr rfl fun p hp => Prod.ext (eq_s _ (Multiset.mem_map_of_mem _ hp)).symm rfl
    rw [this, Multiset.map_cons, Multiset.map_cons]
    rfl
  have hW' : (s(End.port c 0, End.port d 0) ::ₘ W).map (Sym2.map (End.mapCell τ)) =
      s(End.port (τ' c) 0, End.port (τ' d) 0) ::ₘ W.map (Sym2.map (End.mapCell τ')) := by
    rw [map_wires_mapCell_congr (σ := τ') (fun c' i h => (eq_s c' (hG c' i h)).symm),
      Multiset.map_cons]
    rfl
  rw [hC', hW']
  -- the graph before contraction, renamed
  set cut := cutEnd c d (fun i => g (.inl i)) (fun j => g (.inr (.inl j))) with hcut
  set cut' := cutEnd (τ' c) (τ' d) (fun i => g (.inl i)) (fun j => g (.inr (.inl j))) with hcut'
  have hP : (⟨C + R.cells.map (Prod.map σ id),
      W.map (Sym2.map cut) + R.wires.map (Sym2.map (End.map σ g)), n + R.loops⟩ :
        Graph S ℕ).Iso
      ⟨C.map (Prod.map τ' id) + R.cells.map (Prod.map (τ' ∘ σ) id),
        (W.map (Sym2.map (End.mapCell τ'))).map (Sym2.map cut') +
          R.wires.map (Sym2.map (End.map (τ' ∘ σ) g)), n + R.loops⟩ := by
    refine ⟨τ', hτ'.injOn, ?_, ?_, rfl⟩
    · simp only [Multiset.map_add, Multiset.map_map, Prod.map_comp_map]
      rfl
    · simp only [Multiset.map_add, Multiset.map_map, ← Sym2.map_comp]
      congr 1
      · refine Multiset.map_congr rfl fun e _ => ?_
        congr 1
        funext z
        change cut' (End.mapCell τ' z) = End.mapCell τ' (cut z)
        exact (mapCell_cutEnd hτ' c d _ _ z).symm
      · rw [mapCell_endMap]
  obtain ⟨H', hH', iH⟩ := hP.contracts hH
  refine ⟨H', Interact.mk (τ' c) (τ' d) α β (C.map (Prod.map τ' id))
    (W.map (Sym2.map (End.mapCell τ'))) n r hr R hR (τ' ∘ σ) ?_ ?_ g hg ?_ H' hH' ?_, iH⟩
  · intro x hx y hy e
    have hx' := hσG x hx
    have hy' := hσG y hy
    simp only [Function.comp_apply] at e
    rw [eq_n _ hx', eq_n _ hy'] at e
    exact hσ hx hy (by omega)
  · intro x hx hm
    simp only [Function.comp_apply, eq_n _ (hσG x hx)] at hm
    rw [← hC'] at hm
    have := Multiset.le_sup hm
    omega
  · intro w hm
    rw [bind_wireEnds_map_end] at hm
    obtain ⟨z, hz, hze⟩ := Multiset.mem_map.1 hm
    cases z with
    | port _ _ => cases hze
    | name y =>
      cases hze
      exact hgW w hz
  · intro x
    rw [iH.count_name]
    exact hH1 x

-- ============================================================================================
-- 5. Auxiliary lemmas: the active pair with names on its auxiliary ports
-- ============================================================================================

-- the multiset of a list `List.ofFn φ` is the sum of the singletons `{φ i}`
theorem coe_ofFn_eq_sum
    -- the vector
    {α : Type}
    {n : ℕ}
    (φ : Fin n → α) :
    ((List.ofFn φ : List α) : Multiset α) = ∑ i, ({φ i} : Multiset α) := by
  rw [← Fin.univ_val_map]
  have := Multiset.sum_map_singleton (Finset.univ.val.map φ)
  rw [Multiset.map_map] at this
  exact this.symm

-- a cell with names on its auxiliary ports has one cell
theorem size_app_var
    -- the symbol of the cell, and the names on its auxiliary ports
    (α : S.Sym)
    (φ : Fin (S.arity α) → ν) :
    (app α fun i => var (φ i)).size = 1 := by
  simp [Term.size]

-- the cell of a cell with names on its auxiliary ports, numbered `k`
theorem rawCells_app_var
    -- the symbol of the cell, the names on its auxiliary ports, and its number
    (α : S.Sym)
    (φ : Fin (S.arity α) → ν)
    (k : ℕ) :
    (app α fun i => var (φ i)).rawCells k = {(k, α)} := by
  simp [Term.rawCells]

-- the inner wires of a cell with names on its auxiliary ports: one from each auxiliary port to
-- its name
theorem rawWires_app_var
    -- the symbol of the cell, the names on its auxiliary ports, and its number
    (α : S.Sym)
    (φ : Fin (S.arity α) → ν)
    (k : ℕ) :
    (app α fun i => var (φ i)).rawWires k
      = ∑ i : Fin (S.arity α), {s(End.port k ((i : ℕ) + 1), End.name (φ i))} := by
  simp [Term.rawWires, Term.rootEnd]

/-- The cut of the auxiliary ports of the first cell. -/
theorem map_cutEnd_left
    -- the two cells of the cut, and the fresh names of their auxiliary ports
    {c d a b : ℕ}
    (u : Fin a → ℕ)
    (v : Fin b → ℕ)
    -- the names on the auxiliary ports of `c`
    (φ : Fin a → ℕ) :
    (∑ i : Fin a, ({s(End.port c ((i : ℕ) + 1), End.name (φ i))} : Multiset _)).map
        (Sym2.map (cutEnd c d u v))
      = ∑ i : Fin a, {s(End.name (u i), End.name (φ i))} := by
  rw [map_finsum_multiset]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [cutEnd]

/-- The cut of the auxiliary ports of the second cell. -/
theorem map_cutEnd_right
    -- the two cells of the cut, distinct, and the fresh names of their auxiliary ports
    {c d a b : ℕ}
    (hcd : d ≠ c)
    (u : Fin a → ℕ)
    (v : Fin b → ℕ)
    -- the names on the auxiliary ports of `d`
    (φ : Fin b → ℕ) :
    (∑ j : Fin b, ({s(End.port d ((j : ℕ) + 1), End.name (φ j))} : Multiset _)).map
        (Sym2.map (cutEnd c d u v))
      = ∑ j : Fin b, {s(End.name (v j), End.name (φ j))} := by
  rw [map_finsum_multiset]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp [cutEnd, hcd]

/-- The cut keeps the wires that do not end at the two cells. -/
theorem map_cutEnd_of_ports
    -- the two cells of the cut, and the fresh names of their auxiliary ports
    {c d a b : ℕ}
    (u : Fin a → ℕ)
    (v : Fin b → ℕ)
    -- wires none of whose ends is a port of `c` or of `d`
    {W : Multiset (Sym2 (End ℕ))}
    (h : ∀ e i, End.port e i ∈ W.bind wireEnds → e ≠ c ∧ e ≠ d) :
    W.map (Sym2.map (cutEnd c d u v)) = W := by
  conv_rhs => rw [← Multiset.map_id W]
  apply Multiset.map_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ p q =>
    have key : ∀ z ∈ ({p, q} : Multiset (End ℕ)), cutEnd c d u v z = z := by
      intro z hz
      cases z with
      | name x => rfl
      | port e i =>
        obtain ⟨h1, h2⟩ := h e i (Multiset.mem_bind.2 ⟨_, he, by rwa [wireEnds_mk]⟩)
        exact cutEnd_port_of_ne h1 h2 i
    simp only [Sym2.map_mk, id]
    rw [key p (by simp), key q (by simp)]

end Graph

namespace Simulation

/-- The names of the expanded active pair: those of the active pair and the fresh names. -/
theorem mem_vars_expand
    -- the bound from which the fresh names are numbered
    {B : ℕ}
    -- the active pair `s(app α as, app β bs)`, the rest of the net `Δ`
    {α β : S.Sym}
    {as : Fin (S.arity α) → Term S ℕ}
    {bs : Fin (S.arity β) → Term S ℕ}
    {Δ : Net S ℕ}
    -- a name of the expanded net
    {y : ℕ}
    (hy : y ∈ Net.vars ((pairVar B α β ::ₘ Δ)
      + wires (arg B as bs) (ports B (S.arity α) (S.arity β)))) :
    -- is a name of the net, or one of the fresh names
    y ∈ Net.vars (s(.app α as, .app β bs) ::ₘ Δ) ∨ y ∈ ports B (S.arity α) (S.arity β) := by
  rw [Net.vars_add, vars_wires_ports, Net.vars_cons] at hy
  rw [Net.vars_cons]
  simp only [Multiset.mem_add, eqVars_mk, vars_app, vars_var, Multiset.mem_sum, Finset.mem_univ,
    true_and, Multiset.mem_singleton, Multiset.mem_coe] at hy ⊢
  rcases hy with ((⟨i, rfl⟩ | ⟨j, rfl⟩) | hΔ) | hp | (⟨i, hi⟩ | ⟨j, hj⟩)
  · exact Or.inr (left_mem_ports B i)
  · exact Or.inr (right_mem_ports B j)
  · exact Or.inl (Or.inr hΔ)
  · exact Or.inr hp
  · exact Or.inl (Or.inl (Or.inl ⟨i, hi⟩))
  · exact Or.inl (Or.inl (Or.inr ⟨j, hj⟩))

end Simulation

-- ============================================================================================
-- 6. Main result
-- ============================================================================================

private theorem injective_port_names {left right internal start : ℕ}
    {wireName : Fin internal → ℕ} (wireInjective : Function.Injective wireName)
    (wireBelow : ∀ w, wireName w < start) :
    Function.Injective
      (Sum.elim (fun i : Fin left => start + i.val)
        (Sum.elim (fun j : Fin right => start + left + j.val) wireName)) := by
  rintro (i | j | w) (i' | j' | w') equal <;>
    simp only [Sum.elim_inl, Sum.elim_inr] at equal
  · exact congrArg _ (Fin.ext (by omega))
  · omega
  · have := wireBelow w'
    omega
  · omega
  · exact congrArg _ (congrArg _ (Fin.ext (by omega)))
  · have := wireBelow w'
    omega
  · have := wireBelow w
    omega
  · have := wireBelow w
    omega
  · exact congrArg _ (congrArg _ (wireInjective equal))

private def activePairGraph (α β : S.Sym) : Graph S ℕ :=
  ⟨(0, α) ::ₘ (1, β) ::ₘ 0, s(End.port 0 0, End.port 1 0) ::ₘ 0, 0⟩

private theorem activePairGraph_union_ends (α β : S.Sym) (X : Graph S ℕ) :
    ((activePairGraph α β).union X).ends = End.port 0 0 ::ₘ End.port 1 0 ::ₘ X.ends := by
  simp [Graph.union, activePairGraph, Graph.ends_eq_bind, Multiset.cons_bind,
    Multiset.insert_eq_cons]

private theorem activePairGraph_union_name_count (α β : S.Sym) (X : Graph S ℕ) (x : ℕ) :
    ((activePairGraph α β).union X).ends.count (.name x) = X.ends.count (.name x) := by
  rw [activePairGraph_union_ends, Multiset.count_cons_of_ne (by simp),
    Multiset.count_cons_of_ne (by simp)]

private theorem raw_active_pair (α β : S.Sym)
    (leftName : Fin (S.arity α) → ℕ) (rightName : Fin (S.arity β) → ℕ)
    (tail : List (Term S ℕ × Term S ℕ)) :
    Graph.raw 0 ((Term.app α fun i => var (leftName i),
      Term.app β fun j => var (rightName j)) :: tail) =
      (activePairGraph α β).union ⟨(Graph.raw 2 tail).cells,
        (Term.app α fun i => var (leftName i)).rawWires 0 +
          (Term.app β fun j => var (rightName j)).rawWires 1 + (Graph.raw 2 tail).wires, 0⟩ := by
  simp only [Graph.raw, Graph.size_app_var, zero_add, Graph.union, activePairGraph]
  rw [Graph.raw_loops, Graph.rawCells_app_var, Graph.rawCells_app_var]
  simp [Multiset.cons_add, Multiset.singleton_add, Term.rootEnd]

/-- **An interaction of texts is an interaction of graphs** (Lafont 1997, Section 1.2, page 73;
the forward direction). Let the rules of `I` be linear, `N` a linear net with graph `G`, and
`StepE I N M` one interaction up to wires. Then `G` has an interaction `Graph.Interact I G H`
whose result `H` is isomorphic to a graph `H'` of `M`. -/
theorem Net.Linear.stepE_interact
    -- an interaction system whose rules are linear
    {I : System S}
    (hI : ∀ α β r, I.rule α β = some r → r.Linear)
    -- a linear net `N` with one interaction up to wires to `M`
    {N M : Net S ℕ}
    (hN : N.Linear)
    (h : StepE I N M)
    -- a graph of `N`
    {G : Graph S ℕ}
    (hG : N.HasGraph G) :
    ∃ H H',
      -- `G` has an interaction giving `H`,
      Graph.Interact I G H ∧
      -- `H'` is a graph of `M`,
      M.HasGraph H' ∧
      -- and `H` is isomorphic to `H'`
      H.Iso H' := by
  classical
  obtain ⟨N', hNN', hs⟩ := h
  have hN' : N'.Linear := hNN'.linear hN
  obtain ⟨α, β, r, hr, as, bs, Δ, f, hf, hfresh⟩ := hs
  have hrl := hI _ _ _ hr
  -- the bounds `F` and `F'` on the names
  obtain ⟨F₀, hF₀⟩ := Net.exists_below (s(Term.app α as, Term.app β bs) ::ₘ Δ)
  set F := F₀ + Finset.univ.sup f + 1 with hF
  have hBF : Net.Below F (s(Term.app α as, Term.app β bs) ::ₘ Δ) := hF₀.mono (by omega)
  have hfF : ∀ w, f w < F := fun w => by
    have := Finset.le_sup (f := f) (Finset.mem_univ w)
    omega
  obtain ⟨hA, hBb, hΔ⟩ := Net.below_cons.1 hBF
  have has : ∀ i, (as i).Below F := fun i x hx => hA x (by
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]; exact ⟨i, hx⟩)
  have hbs : ∀ j, (bs j).Below F := fun j x hx => hBb x (by
    simp only [vars_app, Multiset.mem_sum, Finset.mem_univ, true_and]; exact ⟨j, hx⟩)
  set F' := F + S.arity α + S.arity β with hF'
  -- the first expansion: names `F + i` on the auxiliary ports
  obtain ⟨hlin₁, E₁⟩ := Simulation.equiv_expand hN' hBF
  set W₁ := Simulation.wires (Simulation.arg F as bs)
    (Simulation.ports F (S.arity α) (S.arity β)) with hW₁
  let xs : Fin (S.arity α) → Term S ℕ := fun i => var (F + i)
  let ys : Fin (S.arity β) → Term S ℕ := fun j => var (F + S.arity α + j)
  set Γ := Δ + W₁ with hΓ
  have e₁ : (Simulation.pairVar F α β ::ₘ Δ) + W₁ = s(Term.app α xs, Term.app β ys) ::ₘ Γ :=
    Multiset.cons_add _ _ _
  have mem₁ : ∀ y ∈ Net.vars (s(Term.app α xs, Term.app β ys) ::ₘ Γ),
      y ∈ Net.vars (s(Term.app α as, Term.app β bs) ::ₘ Δ) ∨
        y ∈ Simulation.ports F (S.arity α) (S.arity β) := fun y hy =>
    Simulation.mem_vars_expand (by rw [e₁]; exact hy)
  rw [e₁] at hlin₁ E₁
  have hB₁ : Net.Below F' (s(Term.app α xs, Term.app β ys) ::ₘ Γ) := fun y hy => by
    rcases mem₁ y hy with h | h
    · have := hBF y h
      omega
    · have := (Simulation.mem_ports.1 h).2
      omega
  -- the second expansion: names `F' + i`, joined to `F + i`
  obtain ⟨hlin₃, -⟩ := Simulation.equiv_expand hlin₁ hB₁
  set W₃ := Simulation.wires (Simulation.arg F' xs ys)
    (Simulation.ports F' (S.arity α) (S.arity β)) with hW₃
  let xs' : Fin (S.arity α) → Term S ℕ := fun i => var (F' + i)
  let ys' : Fin (S.arity β) → Term S ℕ := fun j => var (F' + S.arity α + j)
  have e₃ : (Simulation.pairVar F' α β ::ₘ Γ) + W₃ =
      s(Term.app α xs', Term.app β ys') ::ₘ (Γ + W₃) := Multiset.cons_add _ _ _
  have mem₃ : ∀ y ∈ Net.vars (s(Term.app α xs', Term.app β ys') ::ₘ (Γ + W₃)),
      y ∈ Net.vars (s(Term.app α xs, Term.app β ys) ::ₘ Γ) ∨
        y ∈ Simulation.ports F' (S.arity α) (S.arity β) := fun y hy =>
    Simulation.mem_vars_expand (by rw [e₃]; exact hy)
  rw [e₃] at hlin₃
  -- the new wires of the rule are fresh
  have hf₁ : ∀ w, f w ∉ Net.vars (s(Term.app α xs, Term.app β ys) ::ₘ Γ) := fun w hm => by
    rcases mem₁ _ hm with h | h
    · exact hfresh w h
    · have := (Simulation.mem_ports.1 h).1
      have := hfF w
      omega
  have hf₃ : ∀ w, f w ∉ Net.vars (s(Term.app α xs', Term.app β ys') ::ₘ (Γ + W₃)) :=
    fun w hm => by
      rcases mem₃ _ hm with h | h
      · exact hf₁ w h
      · have := (Simulation.mem_ports.1 h).1
        have := hfF w
        omega
  have hM₂ : (r.inst xs ys f + Γ).Linear := (Step.mk α β r hr xs ys Γ f hf hf₁).linear hI hlin₁
  have hM₃ : (r.inst xs' ys' f + (Γ + W₃)).Linear :=
    (Step.mk α β r hr xs' ys' (Γ + W₃) f hf hf₃).linear hI hlin₃
  -- the result, up to wires
  have hΓB : Γ.Below F' := fun y hy => hB₁ y (by
    rw [Net.vars_cons]; exact Multiset.mem_add.2 (Or.inr hy))
  have Ea := Simulation.equiv_contract_inst r hrl (B := F') (as := xs) (bs := ys) (Δ := Γ) f
    (fun i => by simp only [xs, Term.below_var]; omega)
    (fun j => by simp only [ys, Term.below_var]; omega) hΓB
    (hM₃.cast (add_assoc _ _ _).symm)
  have Eb := Simulation.equiv_contract_inst r hrl (B := F) (as := as) (bs := bs) (Δ := Δ) f
    has hbs hΔ (hM₂.cast (add_assoc _ _ _).symm)
  have EM : Equiv (r.inst xs' ys' f + (Γ + W₃)) (r.inst as bs f + Δ) :=
    (Equiv.of_eq (add_assoc _ _ _).symm).trans
      (Ea.trans ((Equiv.of_eq (add_assoc _ _ _).symm).trans Eb))
  -- texts
  obtain ⟨LΓ, hLΓ⟩ := Net.exists_ofList Γ
  obtain ⟨Lr, hLr⟩ := Net.exists_ofList r.net
  set D := 2 + Graph.rawSize LΓ with hD
  obtain ⟨R, hRc, hR1⟩ := Graph.exists_contracts (Graph.raw D Lr)
  have hR : Net.HasGraph r.net R := ⟨Lr, D, hLr, hRc, hR1⟩
  -- the graph `G₁` of the expanded net
  set A := (Term.app α xs).rawWires 0 with hAdef
  set B' := (Term.app β ys).rawWires 1 with hB'def
  let K₀ : Graph S ℕ := ⟨(Graph.raw 2 LΓ).cells, A + B' + (Graph.raw 2 LΓ).wires, 0⟩
  obtain ⟨K, hKc, hK1⟩ := Graph.exists_contracts K₀
  let Z := activePairGraph α β
  have hraw₁ : Graph.raw 0 ((Term.app α xs, Term.app β ys) :: LΓ) = Z.union K₀ :=
    raw_active_pair α β (fun i => F + i) (fun j => F + S.arity α + j) LΓ
  let G₁ : Graph S ℕ := ⟨(0, α) ::ₘ (1, β) ::ₘ K.cells,
    s(End.port 0 0, End.port 1 0) ::ₘ K.wires, K.loops⟩
  have hZK : Z.union K = G₁ := by simp [Graph.union, Z, activePairGraph, G₁, Multiset.cons_add]
  have hG₁c (x : ℕ) : G₁.ends.count (.name x) = K.ends.count (.name x) :=
    hZK ▸ activePairGraph_union_name_count α β K x
  have hL₁ : s(Term.app α xs, Term.app β ys) ::ₘ Γ =
      Net.ofList ((Term.app α xs, Term.app β ys) :: LΓ) := by
    rw [Net.ofList_cons, ← hLΓ]
  have hG₁ : Net.HasGraph (s(Term.app α xs, Term.app β ys) ::ₘ Γ) G₁ :=
    ⟨_, 0, hL₁, by rw [hraw₁, ← hZK]; exact Graph.contracts_union_left Z hKc,
      fun x => (hG₁c x).trans_le (hK1 x)⟩
  have hG₁wf := hG₁.wf
  -- the names of `K` are names of the expanded net
  have hKn : ∀ y, End.name y ∈ K.wires.bind Graph.wireEnds →
      y ∈ Net.vars (s(Term.app α xs, Term.app β ys) ::ₘ Γ) := by
    intro y hy
    have hm : End.name y ∈ K₀.ends := Multiset.mem_of_le (Graph.contracts_ends_le hKc) hy
    have h1 : End.name y ∈ (Graph.raw 0 ((Term.app α xs, Term.app β ys) :: LΓ)).ends := by
      rw [hraw₁, activePairGraph_union_ends]
      exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hm)
    rw [hL₁, ← Multiset.one_le_count_iff_mem, ← Graph.raw_count_name 0]
    exact Multiset.one_le_count_iff_mem.2 h1
  -- the interaction on `G₁`
  let g : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal → ℕ :=
    Sum.elim (fun i => F' + i) (Sum.elim (fun j => F' + S.arity α + j) f)
  have hg : Function.Injective g :=
    injective_port_names hf (fun w => (hfF w).trans_le (by omega))
  have hgW : ∀ w, End.name (g w) ∉ K.wires.bind Graph.wireEnds := by
    intro w hm
    have := hKn _ hm
    rcases w with i | j | w
    · have := hB₁ _ this
      simp only [g, Sum.elim_inl] at this
      omega
    · have := hB₁ _ this
      simp only [g, Sum.elim_inl, Sum.elim_inr] at this
      omega
    · exact hf₁ w this
  have hKcells : K.cells = (Graph.raw 2 LΓ).cells := Graph.contracts_cells_eq (G := K₀) hKc
  have hσG : ∀ x ∈ R.cells.map Prod.fst,
      (id x : ℕ) ∉ ((0, α) ::ₘ (1, β) ::ₘ K.cells).map Prod.fst := by
    intro x hx hm
    rw [Graph.contracts_cells_eq hRc, Graph.mem_raw_fst] at hx
    simp only [Multiset.map_cons, Multiset.mem_cons, hKcells, Graph.mem_raw_fst, id] at hm
    omega
  set cut := Graph.cutEnd 0 1 (fun i => g (.inl i)) (fun j => g (.inr (.inl j))) with hcut
  let R'' : Graph S ℕ := ⟨R.cells.map (Prod.map id id), R.wires.map (Sym2.map (End.map id g)),
    R.loops⟩
  obtain ⟨H, hH, hH1⟩ := Graph.exists_contracts ((K.mapEnd cut).union R'')
  have hInt : Graph.Interact I G₁ H :=
    Graph.Interact.mk 0 1 α β K.cells K.wires K.loops r hr R hR id (Set.injOn_id _) hσG g hg hgW
      H hH hH1
  -- a text of the result: the wires `F' + i = F + i`, then `Γ`, then the rule renamed by `g`
  let Lp : List (ℕ × ℕ) :=
    (List.ofFn fun i : Fin (S.arity α) => (F' + (i : ℕ), F + (i : ℕ))) ++
      List.ofFn fun j : Fin (S.arity β) => (F' + S.arity α + (j : ℕ), F + S.arity α + (j : ℕ))
  set LW : List (Term S ℕ × Term S ℕ) := Lp.map fun e => (var e.1, var e.2) with hLWdef
  let Lr' := Graph.renameList g Lr
  have hLW : Net.ofList LW = W₃ := by
    simp only [hLWdef, Lp, hW₃, Net.ofList, Simulation.wires, Simulation.ports,
      Multiset.map_coe, List.map_append, List.map_ofFn]
    congr 2
    · congr 1
      funext i
      simp only [Function.comp_apply, Simulation.arg_left, xs]
    · congr 1
      funext j
      simp only [Function.comp_apply, Simulation.arg_right, ys]
  have hLr' : Net.ofList Lr' = r.inst xs' ys' f := by
    rw [Graph.ofList_renameList, ← hLr, Rule.inst]
    congr 1
    funext x
    rcases x with i | j | w <;> rfl
  have hMtext : r.inst xs' ys' f + (Γ + W₃) = Net.ofList (LW ++ (LΓ ++ Lr')) := by
    rw [Graph.ofList_append, Graph.ofList_append, hLW, ← hLΓ, hLr']
    abel
  have hrawM : Graph.raw 2 (LW ++ (LΓ ++ Lr')) = (Graph.raw 2 LW).union
      ((Graph.raw 2 LΓ).union ((Graph.raw D Lr).mapEnd (End.map id g))) := by
    rw [Graph.raw_append, Graph.rawSize_vars, add_zero, Graph.raw_append, Graph.raw_bind_var]
  have hX : Relation.ReflTransGen Graph.Contract (Graph.raw 2 (LW ++ (LΓ ++ Lr')))
      ((Graph.raw 2 LW).union ((Graph.raw 2 LΓ).union (R.mapEnd (End.map id g)))) := by
    rw [hrawM]
    exact Graph.contracts_union_left _
      (Graph.contracts_union_left _ (Graph.contracts_mapEnd (h := g) (fun x => rfl) hRc))
  have hAB : (A + B').map (Sym2.map cut) = (Graph.raw 2 LW).wires := by
    rw [hLWdef, Graph.raw_vars, Multiset.map_add, hAdef, hB'def, hcut]
    simp only [xs, ys, Graph.rawWires_app_var]
    rw [Graph.map_cutEnd_left, Graph.map_cutEnd_right (by omega)]
    simp only [Lp, List.map_append, List.map_ofFn, ← Multiset.coe_add, Graph.coe_ofFn_eq_sum]
    rfl
  have hWΓ : (Graph.raw 2 LΓ).wires.map (Sym2.map cut) = (Graph.raw 2 LΓ).wires :=
    Graph.map_cutEnd_of_ports _ _ fun e i h => by
      have := Graph.raw_portsIn 2 LΓ e i h
      rw [Graph.mem_raw_fst] at this
      omega
  have hc0 : (Graph.raw 2 LW).cells = 0 := by rw [hLWdef, Graph.raw_vars]
  have hXQ : (Graph.raw 2 LW).union ((Graph.raw 2 LΓ).union (R.mapEnd (End.map id g))) =
      (K₀.mapEnd cut).union R'' := by
    simp only [Graph.union, Graph.mapEnd, K₀, R'', hc0, Graph.raw_loops, Multiset.map_add, hWΓ,
      ← hAB, Prod.map_id, Multiset.map_id, zero_add, add_assoc]
  have hQ : Relation.ReflTransGen Graph.Contract ((K₀.mapEnd cut).union R'')
      ((K.mapEnd cut).union R'') :=
    Graph.contracts_union_right (Graph.contracts_mapEnd (h := id) (fun x => rfl) hKc) R''
  have hM₃G : Net.HasGraph (r.inst xs' ys' f + (Γ + W₃)) H := by
    refine ⟨LW ++ (LΓ ++ Lr'), 2, hMtext, ?_, hH1⟩
    rw [← hXQ] at hQ
    exact (hX.trans hQ).trans hH
  -- back to `G` and to `M`
  have iG₁ : G₁.Iso G := Net.Linear.equiv_hasGraph_iso hlin₁ (E₁.symm.trans hNN'.symm) hG₁ hG
  obtain ⟨H₃, hI₃, iH₃⟩ := hInt.iso iG₁ hG₁wf.portsIn
  obtain ⟨H', hH', -⟩ := Net.exists_graph (r.inst as bs f + Δ)
  have iHH' : H.Iso H' := Net.Linear.equiv_hasGraph_iso hM₃ EM hM₃G hH'
  exact ⟨H₃, H', hI₃, hH', (iH₃.symm (hInt.wf hG₁wf).portsIn).trans iHH'⟩

end INet
