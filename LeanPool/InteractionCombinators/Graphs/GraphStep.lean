/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Graphs.GraphContract
public import LeanPool.InteractionCombinators.Core.System

/-!
# One interaction on graphs

Lafont 1997, Section 1.2, page 73: an interaction rule replaces two cells joined by their
principal ports by the net `ν_{i,j}`, whose `n_i + n_j` free ports are attached where the
auxiliary ports of the two cells were attached. "Cyclic wires may be created when such a rule is
applied inside a net."

This file gives that interaction on graphs. The theorem that `StepE` on texts is this
interaction on their graphs is not proved here.

The examples on the combinators are in `Checks/Graphs/GraphStepCheck.lean`.

Contents, in the order of the file:

1. Definitions: `End.map`, renaming the cells and the names of the ends of a graph;
   `Graph.cutEnd`, the auxiliary ports of the two interacting cells become fresh names;
   `Graph.Interact`, one interaction: cut, glue the graph of the rule, contract the fresh names.
2. Auxiliary lemmas: `Interact.principal` (an interaction needs a wire between two principal
   ports); `bind_wireEnds_map_end`; the ports under the cut, `cutEnd_eq_port`,
   `cutEnd_port_of_ne`, `count_map_cutEnd`; the ports under the renaming of the rule,
   `endMap_eq_port`, `count_map_endMap`, `count_map_endMap_eq_zero`.
3. Main result: `Graph.Interact.wf`, an interaction keeps a graph well formed.
-/

@[expose] public section

namespace INet

variable {S : Signature}

-- ============================================================================================
-- 1. Definitions
-- ============================================================================================

namespace End

/-- Renaming the cells by `σ` and the names by `g`. -/
def map
    -- the types of the names, before and after
    {ν μ : Type}
    -- the renaming of the cells, and of the names
    (σ : ℕ → ℕ)
    (g : ν → μ) :
    End ν → End μ
  | port c i => port (σ c) i
  | name x => name (g x)

end End

namespace Graph

/-- **The cut.** The `k`-th auxiliary port of the cell `c` (the end `port c (k + 1)`, for
`k < a`) becomes the name `u k`, and the `k`-th auxiliary port of the cell `d` (for `k < b`)
becomes the name `v k`. Every other end is kept. -/
def cutEnd
    -- the two interacting cells
    (c d : ℕ)
    -- the fresh names for the `a` auxiliary ports of `c` and the `b` auxiliary ports of `d`
    {a b : ℕ}
    (u : Fin a → ℕ)
    (v : Fin b → ℕ) :
    End ℕ → End ℕ
  | .port e (k + 1) =>
    if h : e = c ∧ k < a then .name (u ⟨k, h.2⟩)
    else if h' : e = d ∧ k < b then .name (v ⟨k, h'.2⟩)
    else .port e (k + 1)
  | z => z

/-- **One interaction on graphs** (Lafont 1997, Section 1.2, page 73). The graph `G` has two cells
`c : α` and `d : β` and a wire between their principal ports, and `I.rule α β = some r`. Then `H`
is obtained in three moves.

1. Cut. Remove the two cells and the wire between their principal ports. Each remaining end that
   is the `i`-th auxiliary port of `c` becomes the name `g (.inl i)`, and each end that is the
   `j`-th auxiliary port of `d` becomes the name `g (.inr (.inl j))` (`cutEnd`).
2. Glue. Add a graph `R` of the net of the rule (`r.net.HasGraph R`). Its cells are renumbered
   by `σ`, injectively and away from the cells of `G`, and its names by `g`: the free port `.inl i`
   of the rule becomes `g (.inl i)`, the free port `.inr (.inl j)` becomes `g (.inr (.inl j))`.
   Its cyclic wires are added to those of `G`. The names `g` are injective and do not occur in
   `G`. An internal name `.inr (.inr w)` of a linear rule does not occur in `R`, because it ends
   two wires of the raw graph and is contracted; its value under `g` does not matter.
3. Contract. Erase the fresh names, each of which now ends two wires, one on each side of the
   cut: the wires that were attached to the `i`-th auxiliary port of `c` are attached to the free
   port `.inl i` of `R`, and likewise for `d`. A fresh name that ends both sides of one wire
   gives a cyclic wire: this is how "cyclic wires may be created when such a rule is applied
   inside a net". As in `Net.HasGraph`, contraction goes on until every name ends at most one
   wire.

The definition reads `I.rule α β` with `c` the cell of `α`: the rule for `β, α`, if any, applies
when the same graph is written with the two cells in the other order. Well-formedness of `G` is
not required; it is a hypothesis of the theorems (`Interact.wf`). -/
inductive Interact
    -- the interaction system
    (I : System S) :
    Graph S ℕ → Graph S ℕ → Prop
  -- `G` is the two cells `c : α`, `d : β` joined by their principal ports, the cells `C`, the
  -- wires `W` and `n` cyclic wires; `H` is the graph after the interaction
  | mk
      -- the two interacting cells, the other cells, the other wires, the cyclic wires
      (c d : ℕ)
      (α β : S.Sym)
      (C : Multiset (ℕ × S.Sym))
      (W : Multiset (Sym2 (End ℕ)))
      (n : ℕ)
      -- the rule for `α, β`
      (r : Rule S (S.arity α) (S.arity β))
      (hr : I.rule α β = some r)
      -- a graph of the net of the rule
      (R : Graph S (Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal))
      (hR : r.net.HasGraph R)
      -- the renumbering of its cells: injective, and away from the cells of `G`
      (σ : ℕ → ℕ)
      (hσ : Set.InjOn σ {x | x ∈ R.cells.map Prod.fst})
      (hσG : ∀ x ∈ R.cells.map Prod.fst, σ x ∉ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst)
      -- the fresh names: injective, and not in the wires of `G`
      (g : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal → ℕ)
      (hg : Function.Injective g)
      (hgW : ∀ w, End.name (g w) ∉ W.bind wireEnds)
      -- the result: the cut graph glued to the renamed `R`, contracted until every name ends
      -- at most one wire
      (H : Graph S ℕ)
      (hH : Relation.ReflTransGen Contract
        ⟨C + R.cells.map (Prod.map σ id),
          W.map (Sym2.map (cutEnd c d (fun i => g (.inl i)) (fun j => g (.inr (.inl j)))))
            + R.wires.map (Sym2.map (End.map σ g)),
          n + R.loops⟩ H)
      (hH1 : ∀ x, H.ends.count (.name x) ≤ 1) :
      Interact I ⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ H

-- ============================================================================================
-- 2. Auxiliary lemmas
-- ============================================================================================

/-- **Cells interact only through their principal ports** (Lafont 1997, page 73): a graph that has
an interaction has a wire between the principal ports of two cells. -/
theorem Interact.principal
    -- the interaction system
    {I : System S}
    -- an interaction from `G` to `H`
    {G H : Graph S ℕ}
    (h : Interact I G H) :
    -- some wire of `G` joins the principal ports of two cells
    ∃ c d, s(End.port c 0, End.port d 0) ∈ G.wires := by
  cases h with
  | mk c d => exact ⟨c, d, Multiset.mem_cons_self _ _⟩

/-- The ends of renamed wires are the renamed ends. -/
theorem bind_wireEnds_map_end
    -- the renaming of the ends
    {ν μ : Type}
    (f : End ν → End μ)
    -- the wires
    (W : Multiset (Sym2 (End ν))) :
    (W.map (Sym2.map f)).bind wireEnds = (W.bind wireEnds).map f := by
  rw [Multiset.bind_map, Multiset.map_bind]
  congr 1
  funext e
  induction e using Sym2.ind with
  | _ p q => simp [Multiset.insert_eq_cons]

section cut

-- the two cells of the cut, and the fresh names of their auxiliary ports
variable {c d a b : ℕ} {u : Fin a → ℕ} {v : Fin b → ℕ}

/-- The cut produces a port only from that same port (Lafont 1997, page 73). -/
theorem cutEnd_eq_port
    -- an end that the cut sends to the port `i` of the cell `e`
    {z : End ℕ}
    {e i : ℕ}
    (h : cutEnd c d u v z = .port e i) :
    -- it was that port
    z = .port e i := by
  match z, h with
  | .name _, h => cases h
  | .port _ 0, h => exact h
  | .port e' (k + 1), h =>
    simp only [cutEnd] at h
    split_ifs at h
    exact h

/-- The cut keeps the ports of the cells other than `c` and `d` (Lafont 1997, page 73). -/
theorem cutEnd_port_of_ne
    -- a cell other than `c` and `d`
    {e : ℕ}
    (hc : e ≠ c)
    (hd : e ≠ d)
    -- one of its ports
    (i : ℕ) :
    cutEnd c d u v (.port e i) = .port e i := by
  cases i with
  | zero => rfl
  | succ k => simp [cutEnd, hc, hd]

/-- The cut does not change how many ends are a port of a cell other than `c` and `d`. -/
theorem count_map_cutEnd
    -- a port of a cell other than `c` and `d`
    {e : ℕ}
    (hc : e ≠ c)
    (hd : e ≠ d)
    (i : ℕ)
    -- the ends
    (M : Multiset (End ℕ)) :
    (M.map (cutEnd c d u v)).count (.port e i) = M.count (.port e i) := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro z _
  constructor
  · intro h
    exact (cutEnd_eq_port h.symm).symm
  · rintro rfl
    exact (cutEnd_port_of_ne hc hd i).symm

end cut

section place

-- the renaming of the cells by `σ` and of the names by `g`
variable {ν : Type} {σ : ℕ → ℕ} {g : ν → ℕ}

/-- A renamed end is a port only if it was a port, of a cell renamed to that one. -/
theorem endMap_eq_port
    -- an end renamed to the port `i` of the cell `e`
    {z : End ν}
    {e i : ℕ}
    (h : End.map σ g z = .port e i) :
    -- there is a cell `x` such that
    ∃ x,
      -- the end was the port `i` of `x`,
      z = .port x i ∧
      -- and `x` is renamed to `e`
      e = σ x := by
  cases z with
  | port x j =>
    simp only [End.map, End.port.injEq] at h
    exact ⟨x, by rw [h.2], h.1.symm⟩
  | name y => cases h

/-- Renaming the cells injectively keeps how many ends are a given port. -/
theorem count_map_endMap
    [DecidableEq ν]
    -- a set of cells on which `σ` is injective
    {s : Set ℕ}
    (hσ : Set.InjOn σ s)
    -- ends whose ports are ports of cells of `s`
    {M : Multiset (End ν)}
    (hM : ∀ y j, End.port y j ∈ M → y ∈ s)
    -- a port of a cell of `s`
    {x : ℕ}
    (hx : x ∈ s)
    (i : ℕ) :
    (M.map (End.map σ g)).count (.port (σ x) i) = M.count (.port x i) := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro z hz
  cases z with
  | port y j =>
    simp only [End.map, End.port.injEq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨hσ hx (hM y j hz) h1, h2⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨rfl, rfl⟩
  | name y => simp [End.map]

/-- A port of a cell outside the image of `σ` is not a renamed end. -/
theorem count_map_endMap_eq_zero
    -- ends whose ports are ports of cells of `s`
    {s : Set ℕ}
    {M : Multiset (End ν)}
    (hM : ∀ y j, End.port y j ∈ M → y ∈ s)
    -- a port of a cell `e` that is not the image of a cell of `s`
    {e : ℕ}
    (he : ∀ x ∈ s, σ x ≠ e)
    (i : ℕ) :
    (M.map (End.map σ g)).count (.port e i) = 0 := by
  rw [Multiset.count_eq_zero]
  intro hm
  obtain ⟨z, hz, hze⟩ := Multiset.mem_map.1 hm
  obtain ⟨x, rfl, rfl⟩ := endMap_eq_port hze
  exact he x (hM x i hz) rfl

end place

-- ============================================================================================
-- 3. Main result: an interaction keeps a graph well formed
-- ============================================================================================

/-- **An interaction keeps a graph well formed** (Lafont 1997, Section 1.2, page 73). If `G` is
well formed and `Interact I G H`, then `H` is well formed: its cells have distinct numbers, each
port of each cell ends exactly one wire, and each name ends at most one. Linearity of the rule is
not needed, because the last condition is part of the definition of `Interact`. -/
theorem Interact.wf
    -- the interaction system
    {I : System S}
    -- an interaction from `G` to `H`
    {G H : Graph S ℕ}
    (h : Interact I G H)
    -- `G` is well formed
    (hG : G.WF) :
    -- then so is `H`
    H.WF := by
  obtain ⟨c, d, α, β, C, W, n, r, hr, R, hR, σ, hσ, hσG, g, hg, hgW, H, hH, hH1⟩ := h
  set cut := cutEnd c d (fun i => g (.inl i)) (fun j => g (.inr (.inl j))) with hcut
  have hGe : Graph.ends (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ :
      Graph S ℕ) = .port c 0 ::ₘ .port d 0 ::ₘ W.bind wireEnds := by
    rw [ends_eq_bind, Multiset.cons_bind, wireEnds_mk, Multiset.insert_eq_cons, Multiset.cons_add,
      Multiset.singleton_add]
  have hnd := hG.nodup
  simp only [Multiset.map_cons, Multiset.nodup_cons, Multiset.mem_cons, not_or] at hnd
  obtain ⟨⟨hcd, hcC⟩, hdC, hCn⟩ := hnd
  have hcG : (c, α) ∈ (c, α) ::ₘ (d, β) ::ₘ C := Multiset.mem_cons_self _ _
  have hdG : (d, β) ∈ (c, α) ::ₘ (d, β) ::ₘ C :=
    Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)
  have hc0 : End.port c 0 ∉ W.bind wireEnds := by
    have := hG.port c α hcG 0 (Nat.zero_le _)
    rw [hGe, Multiset.count_cons_self, Multiset.count_cons_of_ne (by simpa using hcd)] at this
    exact Multiset.count_eq_zero.1 (by omega)
  have hd0 : End.port d 0 ∉ W.bind wireEnds := by
    have := hG.port d β hdG 0 (Nat.zero_le _)
    rw [hGe, Multiset.count_cons_of_ne (by simpa using Ne.symm hcd), Multiset.count_cons_self]
      at this
    exact Multiset.count_eq_zero.1 (by omega)
  have hRwf := hR.wf
  have hRp : ∀ y j, End.port y j ∈ R.ends → y ∈ {x | x ∈ R.cells.map Prod.fst} := by
    intro y j hm
    obtain ⟨γ, hγ, -⟩ := hRwf.cell y j hm
    exact Multiset.mem_map_of_mem Prod.fst hγ
  have hWp : ∀ y j, End.port y j ∈ W.bind wireEnds →
      y ∈ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst := by
    intro y j hm
    have hm' : End.port y j ∈ Graph.ends (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W,
        n⟩ : Graph S ℕ) := by
      rw [hGe]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hm)
    obtain ⟨γ, hγ, -⟩ := hG.cell y j hm'
    exact Multiset.mem_map_of_mem Prod.fst hγ
  have hE : Graph.ends (⟨C + R.cells.map (Prod.map σ id),
      W.map (Sym2.map cut) + R.wires.map (Sym2.map (End.map σ g)), n + R.loops⟩ : Graph S ℕ) =
      (W.bind wireEnds).map cut + R.ends.map (End.map σ g) := by
    rw [ends_eq_bind, Multiset.add_bind, bind_wireEnds_map_end, bind_wireEnds_map_end]
    rfl
  refine contracts_wf hH ?_ ?_ ?_ hH1
  · -- The cells have distinct numbers.
    change ((C + R.cells.map (Prod.map σ id)).map Prod.fst).Nodup
    have hm : (R.cells.map (Prod.map σ id)).map Prod.fst = (R.cells.map Prod.fst).map σ := by
      rw [Multiset.map_map, Multiset.map_map]
      rfl
    rw [Multiset.map_add, hm, Multiset.nodup_add]
    refine ⟨hCn, hRwf.nodup.map_on fun x hx y hy e => hσ hx hy e, ?_⟩
    rw [Multiset.disjoint_left]
    intro e heC heR
    obtain ⟨x, hx, rfl⟩ := Multiset.mem_map.1 heR
    exact hσG x hx (by simp only [Multiset.map_cons, Multiset.mem_cons]; exact Or.inr (Or.inr heC))
  · -- Each port of each cell ends exactly one wire.
    intro e γ hm i hi
    rw [hE, Multiset.count_add]
    rcases Multiset.mem_add.1 hm with hC | hR'
    · have heC : e ∈ C.map Prod.fst := Multiset.mem_map_of_mem Prod.fst hC
      have hec : e ≠ c := fun h => hcC (h ▸ heC)
      have hed : e ≠ d := fun h => hdC (h ▸ heC)
      rw [count_map_cutEnd hec hed, count_map_endMap_eq_zero hRp]
      · have := hG.port e γ (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hC)) i hi
        rw [hGe, Multiset.count_cons_of_ne (fun h => hec (End.port.inj h).1),
          Multiset.count_cons_of_ne (fun h => hed (End.port.inj h).1)] at this
        exact this
      · intro x hx hxe
        exact hσG x hx (by
          simp only [Multiset.map_cons, Multiset.mem_cons]
          exact Or.inr (Or.inr (hxe ▸ heC)))
    · obtain ⟨⟨x, γ'⟩, hx, he⟩ := Multiset.mem_map.1 hR'
      simp only [Prod.map, id, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      have hxs : x ∈ {x | x ∈ R.cells.map Prod.fst} := Multiset.mem_map_of_mem Prod.fst hx
      rw [count_map_endMap hσ hRp hxs, hRwf.port x γ' hx i hi]
      have : (Multiset.map cut (W.bind wireEnds)).count (.port (σ x) i) = 0 := by
        rw [Multiset.count_eq_zero]
        intro hm'
        obtain ⟨z, hz, hze⟩ := Multiset.mem_map.1 hm'
        rw [cutEnd_eq_port hze] at hz
        exact hσG x hxs (hWp _ _ hz)
      rw [this]
  · -- A port that is an end is a port of a cell.
    intro e i hm
    rw [hE] at hm
    rcases Multiset.mem_add.1 hm with hW | hR'
    · obtain ⟨z, hz, hze⟩ := Multiset.mem_map.1 hW
      have hz' := cutEnd_eq_port hze
      subst hz'
      obtain ⟨γ, hγ, hi⟩ := hG.cell e i (by
        rw [hGe]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hz))
      rcases Multiset.mem_cons.1 hγ with he | he
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        cases i with
        | zero => exact absurd hz hc0
        | succ k =>
          have hk : k < S.arity γ := by omega
          simp [hcut, cutEnd, hk] at hze
      · rcases Multiset.mem_cons.1 he with he | he
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
          cases i with
          | zero => exact absurd hz hd0
          | succ k =>
            have hk : k < S.arity γ := by omega
            simp [hcut, cutEnd, hk, Ne.symm hcd] at hze
        · exact ⟨γ, Multiset.mem_add.2 (Or.inl he), hi⟩
    · obtain ⟨z, hz, hze⟩ := Multiset.mem_map.1 hR'
      obtain ⟨x, rfl, rfl⟩ := endMap_eq_port hze
      obtain ⟨γ, hγ, hi⟩ := hRwf.cell x i hz
      exact ⟨γ, Multiset.mem_add.2 (Or.inr (Multiset.mem_map_of_mem (Prod.map σ id) hγ)), hi⟩

end Graph

end INet
