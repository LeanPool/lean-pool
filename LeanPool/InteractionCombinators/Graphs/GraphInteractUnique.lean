/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Graphs.GraphStepE
public import LeanPool.InteractionCombinators.Universality.RecursionFree.Decomposition

/-!
# The result of an interaction on graphs is unique

Lafont 1997, Section 1.2, page 73: an interaction rule replaces two cells joined by their
principal ports by the right-hand side of the rule. `Graph.Interact` makes three choices that
the paper does not make: the graph `R` of the right-hand side, the renumbering `σ` of its cells
and the fresh names `g` of the cut. This file proves that for a fixed pair of cells of a
well-formed graph and a linear rule, the result does not depend on them, up to `Graph.Iso`.

Contents, in the order of the file:

1. Parity of the ends of a name: `Graph.Contract.count_name_mod_two`,
   `Graph.contracts_count_name_mod_two` (contraction keeps the parity of the number of ends of
   every name), `Net.HasGraph.count_name_mod_two`, `Rule.Linear.count_name_graph` (the free
   ports of a graph of a linear rule).
2. Counting through a map: `count_map_eq_of_iff`, `count_map_eq_zero_of`,
   `map_wires_congr_ends`, `map_wires_eq_self`.
3. Definition: `Graph.preInteract`, the graph of `Interact` before contraction, and
   `preInteract_ends`.
4. The well-formed graph of an interaction: `ends_pair`, `WF.pair_ne`, `WF.count_left`,
   `WF.count_right`, `WF.count_name_rest`, `WF.port_zero_notMem`, `WF.cut_port`.
5. Counting the names of the graph before contraction: `count_cut_name`,
   `count_cut_name_of_notMem`, `count_rule_name`, `count_rule_name_of_notMem`.
6. Uniqueness for a fixed graph of the rule: `preInteract_count_name`, the renamings
   `freshRename` and `cellRename`, `preInteract_mapEnd` (other fresh names give the graph
   renamed), `preInteract_iso_cells` (another renumbering of the cells of the rule gives an
   isomorphic graph), `preInteract_unique`.
7. Main result: `Graph.interact_unique`, the result of an interaction is unique up to
   `Graph.Iso`.
-/

@[expose] public section

namespace INet

variable {S : Signature} {ν : Type}

open Term

namespace Graph

-- ============================================================================================
-- 1. Parity of the ends of a name
-- ============================================================================================

/-- **A contraction keeps the parity of the ends of a name** (Lafont 1997, page 71): it removes
two ends of one name. -/
theorem Contract.count_name_mod_two
    [DecidableEq ν]
    -- a contraction from `G` to `H`
    {G H : Graph S ν}
    (h : Contract G H)
    -- a name
    (y : ν) :
    -- `y` ends as many wires in `G` as in `H`, up to parity
    G.ends.count (.name y) % 2 = H.ends.count (.name y) % 2 := by
  obtain ⟨x, hx⟩ := h.ends_eq
  rw [hx]
  by_cases hy : y = x
  · subst hy
    rw [Multiset.count_cons_self, Multiset.count_cons_self]
    omega
  · have hne : (End.name y : End ν) ≠ .name x := fun e => hy (End.name.inj e)
    rw [Multiset.count_cons_of_ne hne, Multiset.count_cons_of_ne hne]

/-- **Contractions keep the parity of the ends of a name** (Lafont 1997, page 71). -/
theorem contracts_count_name_mod_two
    [DecidableEq ν]
    -- a sequence of contractions from `G` to `H`
    {G H : Graph S ν}
    (h : Relation.ReflTransGen Contract G H)
    -- a name
    (y : ν) :
    -- `y` ends as many wires in `G` as in `H`, up to parity
    G.ends.count (.name y) % 2 = H.ends.count (.name y) % 2 := by
  induction h with
  | refl => rfl
  | tail _ s ih => rw [ih, s.count_name_mod_two]

end Graph

/-- **In a graph of a net, a name ends as many wires as it has occurrences, up to parity**
(Lafont 1997, page 71). -/
theorem Net.HasGraph.count_name_mod_two
    [DecidableEq ν]
    -- a net and a graph of it
    {N : Net S ν}
    {G : Graph S ν}
    (h : N.HasGraph G)
    -- a name
    (y : ν) :
    -- `y` ends as many wires in `G` as it has occurrences in `N`, up to parity
    G.ends.count (.name y) % 2 = N.vars.count y % 2 := by
  obtain ⟨L, k, rfl, hc, -⟩ := h
  rw [← Graph.contracts_count_name_mod_two hc, Graph.raw_count_name]

/-- **The free ports of a graph of a linear rule** (Lafont 1997, page 73): every auxiliary port of
the two cells is a free port of the graph of the right-hand side, and no internal wire is. -/
theorem Rule.Linear.count_name_graph
    -- a linear rule
    {a b : ℕ}
    {r : Rule S a b}
    (hr : r.Linear)
    -- a graph of its right-hand side
    {R : Graph S (Fin a ⊕ Fin b ⊕ Fin r.internal)}
    (hR : r.net.HasGraph R)
    -- a name of the rule
    (w : Fin a ⊕ Fin b ⊕ Fin r.internal) :
    -- an auxiliary port of either cell ends one wire of `R`, an internal name ends none
    R.ends.count (.name w) = match w with
      | .inl _ => 1
      | .inr (.inl _) => 1
      | .inr (.inr _) => 0 := by
  have h2 := hR.count_name_mod_two w
  have h1 : R.ends.count (.name w) ≤ 1 := by
    obtain ⟨-, -, -, -, h⟩ := hR
    exact h w
  rcases w with i | j | v
  · rw [hr.left i] at h2
    change _ = 1
    omega
  · rw [hr.right j] at h2
    change _ = 1
    omega
  · rw [hr.internal v] at h2
    change _ = 0
    omega

namespace Graph

-- ============================================================================================
-- 2. Counting through a map
-- ============================================================================================

/-- Counting the image of a map: `b` is the image of exactly the elements equal to `a`. -/
theorem count_map_eq_of_iff
    -- a map and a multiset
    {α β : Type}
    [DecidableEq α]
    [DecidableEq β]
    {f : α → β}
    {M : Multiset α}
    -- an element of `M` is sent to `b` exactly when it is `a`
    {a : α}
    {b : β}
    (h : ∀ z ∈ M, b = f z ↔ z = a) :
    -- `b` occurs in the image as often as `a` occurs in `M`
    (M.map f).count b = M.count a := by
  rw [Multiset.count_map, Multiset.count_eq_card_filter_eq]
  congr 1
  apply Multiset.filter_congr
  intro z hz
  rw [h z hz, eq_comm]

/-- Counting the image of a map: `b` is the image of no element. -/
theorem count_map_eq_zero_of
    -- a map and a multiset
    {α β : Type}
    [DecidableEq β]
    {f : α → β}
    {M : Multiset α}
    -- no element of `M` is sent to `b`
    {b : β}
    (h : ∀ z ∈ M, f z ≠ b) :
    -- `b` does not occur in the image
    (M.map f).count b = 0 := by
  rw [Multiset.count_eq_zero]
  intro hm
  obtain ⟨z, hz, e⟩ := Multiset.mem_map.1 hm
  exact h z hz e

/-- Two maps that agree on the ends of some wires map these wires alike. -/
theorem map_wires_congr_ends
    -- some wires
    {μ : Type}
    {W : Multiset (Sym2 (End ν))}
    -- two maps of ends that agree on their ends
    {f f' : End ν → End μ}
    (h : ∀ z ∈ W.bind wireEnds, f z = f' z) :
    -- the two images of the wires are equal
    W.map (Sym2.map f) = W.map (Sym2.map f') := by
  apply Multiset.map_congr rfl
  intro e he
  induction e using Sym2.ind with
  | _ p q =>
    simp only [Sym2.map_mk]
    rw [h p (Multiset.mem_bind.2 ⟨_, he, by simp⟩), h q (Multiset.mem_bind.2 ⟨_, he, by simp⟩)]

/-- Maps that keep the ends of some wires keep these wires. -/
theorem map_wires_eq_self
    -- some wires
    {W : Multiset (Sym2 (End ν))}
    -- a map of ends that keeps their ends
    {f : End ν → End ν}
    (h : ∀ z ∈ W.bind wireEnds, f z = z) :
    -- the image of the wires is the wires
    W.map (Sym2.map f) = W := by
  conv_rhs => rw [← Multiset.map_id W]
  rw [show (id : Sym2 (End ν) → Sym2 (End ν)) = Sym2.map id from Sym2.map_id.symm]
  exact map_wires_congr_ends h

-- ============================================================================================
-- 3. Definition: the graph before contraction
-- ============================================================================================

/-- **The graph of an interaction before contraction** (Lafont 1997, page 73): the rest `C`, `W`,
`n` of the graph, cut at the auxiliary ports of `c` and `d` with the names `g`, beside the graph
`R` of the rule, its cells renumbered by `σ` and its names renamed by `g`. This is the graph that
`Graph.Interact` contracts. -/
def preInteract
    -- the cells of the active pair
    (c d : ℕ)
    -- the other cells, the other wires and the cyclic wires of the graph
    (C : Multiset (ℕ × S.Sym))
    (W : Multiset (Sym2 (End ℕ)))
    (n : ℕ)
    -- a graph of the right-hand side of the rule
    {a b m : ℕ}
    (R : Graph S (Fin a ⊕ Fin b ⊕ Fin m))
    -- the renumbering of its cells and the names of its free ports and internal wires
    (σ : ℕ → ℕ)
    (g : Fin a ⊕ Fin b ⊕ Fin m → ℕ) :
    Graph S ℕ :=
  ⟨C + R.cells.map (Prod.map σ id),
    W.map (Sym2.map (cutEnd c d (fun i => g (.inl i)) (fun j => g (.inr (.inl j))))) +
      R.wires.map (Sym2.map (End.map σ g)),
    n + R.loops⟩

/-- The ends of the graph before contraction: the ends of the other wires, cut, and the ends of
the graph of the rule, renamed. -/
theorem preInteract_ends
    -- the cells of the active pair
    (c d : ℕ)
    -- the other cells, the other wires and the cyclic wires of the graph
    (C : Multiset (ℕ × S.Sym))
    (W : Multiset (Sym2 (End ℕ)))
    (n : ℕ)
    -- a graph of the right-hand side of the rule
    {a b m : ℕ}
    (R : Graph S (Fin a ⊕ Fin b ⊕ Fin m))
    -- the renumbering of its cells and the names of its free ports and internal wires
    (σ : ℕ → ℕ)
    (g : Fin a ⊕ Fin b ⊕ Fin m → ℕ) :
    (preInteract c d C W n R σ g).ends
      = (W.bind wireEnds).map (cutEnd c d (fun i => g (.inl i)) (fun j => g (.inr (.inl j))))
        + R.ends.map (End.map σ g) := by
  rw [ends_eq_bind, preInteract, Multiset.add_bind, bind_wireEnds_map_end, bind_wireEnds_map_end]
  rfl

-- ============================================================================================
-- 4. The well-formed graph of an interaction
-- ============================================================================================

section wf

-- the cells `c : α` and `d : β` of the active pair, the other cells, the other wires and the
-- cyclic wires of the graph
variable {c d : ℕ} {α β : S.Sym} {C : Multiset (ℕ × S.Sym)} {W : Multiset (Sym2 (End ℕ))}
  {n : ℕ}

/-- The ends of a graph with an active pair. -/
theorem ends_pair
    -- the cells of the active pair and their symbols
    (c d : ℕ)
    (α β : S.Sym)
    -- the other cells, the other wires and the cyclic wires
    (C : Multiset (ℕ × S.Sym))
    (W : Multiset (Sym2 (End ℕ)))
    (n : ℕ) :
    -- the ends are the two principal ports and the ends of the other wires
    Graph.ends (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ : Graph S ℕ)
      = .port c 0 ::ₘ .port d 0 ::ₘ W.bind wireEnds := by
  rw [ends_eq_bind, Multiset.cons_bind, wireEnds_mk, Multiset.insert_eq_cons, Multiset.cons_add,
    Multiset.singleton_add]

-- the graph is well-formed, and its cells `c` and `d` are joined by their principal ports
variable (hG : Graph.WF (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ :
  Graph S ℕ))
include hG

/-- The two cells of an active pair of a well-formed graph are distinct. -/
theorem WF.pair_ne : c ≠ d := by
  have hnd := hG.nodup
  simp only [Multiset.map_cons, Multiset.nodup_cons, Multiset.mem_cons, not_or] at hnd
  exact hnd.1.1

/-- The first cell of an active pair is not one of the other cells. -/
theorem WF.pair_notMem_left : c ∉ C.map Prod.fst := by
  have hnd := hG.nodup
  simp only [Multiset.map_cons, Multiset.nodup_cons, Multiset.mem_cons, not_or] at hnd
  exact hnd.1.2

/-- The second cell of an active pair is not one of the other cells. -/
theorem WF.pair_notMem_right : d ∉ C.map Prod.fst := by
  have hnd := hG.nodup
  simp only [Multiset.map_cons, Multiset.nodup_cons, Multiset.mem_cons, not_or] at hnd
  exact hnd.2.1

/-- In a well-formed graph, the `i`-th auxiliary port of the first cell of an active pair ends
exactly one of the other wires. -/
theorem WF.count_left
    -- an auxiliary port of `c`
    (i : Fin (S.arity α)) :
    -- it ends exactly one of the other wires
    (W.bind wireEnds).count (.port c ((i : ℕ) + 1)) = 1 := by
  have := hG.port c α (Multiset.mem_cons_self _ _) ((i : ℕ) + 1) (by omega)
  rw [ends_pair, Multiset.count_cons_of_ne (by simp), Multiset.count_cons_of_ne (by
    simp)] at this
  exact this

/-- In a well-formed graph, the `j`-th auxiliary port of the second cell of an active pair ends
exactly one of the other wires. -/
theorem WF.count_right
    -- an auxiliary port of `d`
    (j : Fin (S.arity β)) :
    -- it ends exactly one of the other wires
    (W.bind wireEnds).count (.port d ((j : ℕ) + 1)) = 1 := by
  have := hG.port d β (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)) ((j : ℕ) + 1)
    (by omega)
  rw [ends_pair, Multiset.count_cons_of_ne (by simp), Multiset.count_cons_of_ne
    (by simp)] at this
  exact this

/-- In a well-formed graph, a name ends at most one of the other wires of an active pair. -/
theorem WF.count_name_rest
    -- a name
    (y : ℕ) :
    -- it ends at most one of the other wires
    (W.bind wireEnds).count (.name y) ≤ 1 := by
  have := hG.name y
  rw [ends_pair, Multiset.count_cons_of_ne (by simp), Multiset.count_cons_of_ne (by simp)] at this
  exact this

/-- The principal ports of an active pair end no other wire. -/
theorem WF.port_zero_notMem :
    -- the principal port of `c` ends no other wire
    End.port c 0 ∉ W.bind wireEnds ∧
    -- nor does the principal port of `d`
    End.port d 0 ∉ W.bind wireEnds := by
  have hc := hG.port c α (Multiset.mem_cons_self _ _) 0 (Nat.zero_le _)
  have hd := hG.port d β (Multiset.mem_cons_of_mem (Multiset.mem_cons_self _ _)) 0
    (Nat.zero_le _)
  rw [ends_pair, Multiset.count_cons_self, Multiset.count_cons_of_ne (by simp [hG.pair_ne])] at hc
  rw [ends_pair, Multiset.count_cons_of_ne (by simp [Ne.symm hG.pair_ne]),
    Multiset.count_cons_self] at hd
  exact ⟨Multiset.count_eq_zero.1 (by omega), Multiset.count_eq_zero.1 (by omega)⟩

/-- The ports at the ends of the other wires of an active pair, once cut, are ports of the other
cells (Lafont 1997, page 73). -/
theorem WF.cut_port
    -- the names that replace the auxiliary ports of `c` and `d`
    {u : Fin (S.arity α) → ℕ}
    {v : Fin (S.arity β) → ℕ}
    -- a port that ends one of the other wires once cut
    {e i : ℕ}
    (hm : End.port e i ∈ (W.bind wireEnds).map (cutEnd c d u v)) :
    -- it is a port of one of the other cells
    ∃ γ, (e, γ) ∈ C ∧ i ≤ S.arity γ := by
  obtain ⟨z, hz, hze⟩ := Multiset.mem_map.1 hm
  have hz' := cutEnd_eq_port hze
  subst hz'
  obtain ⟨γ, hγ, hi⟩ := hG.cell e i (by
    rw [ends_pair]; exact Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem hz))
  rcases Multiset.mem_cons.1 hγ with he | he
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    cases i with
    | zero => exact absurd hz hG.port_zero_notMem.1
    | succ k =>
      have hk : k < S.arity γ := by omega
      simp [cutEnd, hk] at hze
  · rcases Multiset.mem_cons.1 he with he | he
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      cases i with
      | zero => exact absurd hz hG.port_zero_notMem.2
      | succ k =>
        have hk : k < S.arity γ := by omega
        simp [cutEnd, hk, Ne.symm hG.pair_ne] at hze
    · exact ⟨γ, he, hi⟩

end wf

-- ============================================================================================
-- 5. Counting the names of the graph before contraction
-- ============================================================================================

section count

-- the cells `c : α` and `d : β` of the active pair, the other cells, the other wires and the
-- cyclic wires of the graph, the number `m` of internal wires of the rule, and the names `g`
-- of the free ports and internal wires of the rule
variable {c d : ℕ} {α β : S.Sym} {C : Multiset (ℕ × S.Sym)} {W : Multiset (Sym2 (End ℕ))}
  {n m : ℕ} {g : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin m → ℕ}

/-- When the cut uses fresh injective names, each name of the cut ends as many wires as the port
it replaces. -/
theorem count_cut_name
    -- the graph is well-formed, with an active pair `c`, `d`
    (hG : Graph.WF (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ : Graph S ℕ))
    -- the names `g` are injective and end none of the other wires
    (hg : Function.Injective g)
    (hgW : ∀ w, End.name (g w) ∉ W.bind wireEnds)
    -- a name of the rule
    (w : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin m) :
    -- once cut, the other wires have one end `g w` for an auxiliary port, none for an internal
    -- name
    ((W.bind wireEnds).map (cutEnd c d (fun i => g (.inl i)) (fun j => g (.inr (.inl j))))).count
      (.name (g w)) = match w with
        | .inl _ => 1
        | .inr (.inl _) => 1
        | .inr (.inr _) => 0 := by
  have hcd := hG.pair_ne
  -- the ends that the cut sends to `g w`
  have key : ∀ z ∈ W.bind wireEnds,
      cutEnd c d (fun i => g (.inl i)) (fun j => g (.inr (.inl j))) z = .name (g w) ↔
        (∃ i : Fin (S.arity α), w = .inl i ∧ z = .port c ((i : ℕ) + 1)) ∨
          (∃ j : Fin (S.arity β), w = .inr (.inl j) ∧ z = .port d ((j : ℕ) + 1)) := by
    intro z hz
    match z with
    | .name y =>
      simp only [cutEnd, End.name.injEq, reduceCtorEq, and_false, exists_false, or_self,
        iff_false]
      rintro rfl
      exact hgW w hz
    | .port e 0 => simp [cutEnd]
    | .port e (k + 1) =>
      simp only [cutEnd]
      split_ifs with h1 h2
      · obtain ⟨rfl, hk⟩ := h1
        constructor
        · intro e'
          exact Or.inl ⟨⟨k, hk⟩, (hg (End.name.inj e')).symm, rfl⟩
        · rintro (⟨i, rfl, hz'⟩ | ⟨j, rfl, hz'⟩)
          · obtain ⟨-, hk'⟩ := End.port.inj hz'
            have : (⟨k, hk⟩ : Fin _) = i := Fin.ext (show k = (i : ℕ) by omega)
            rw [this]
          · exact absurd (End.port.inj hz').1 hcd
      · obtain ⟨rfl, hk⟩ := h2
        constructor
        · intro e'
          exact Or.inr ⟨⟨k, hk⟩, (hg (End.name.inj e')).symm, rfl⟩
        · rintro (⟨i, rfl, hz'⟩ | ⟨j, rfl, hz'⟩)
          · obtain ⟨he, hk'⟩ := End.port.inj hz'
            exact absurd ⟨he, by omega⟩ h1
          · obtain ⟨-, hk'⟩ := End.port.inj hz'
            have : (⟨k, hk⟩ : Fin _) = j := Fin.ext (show k = (j : ℕ) by omega)
            rw [this]
      · constructor
        · intro e'
          cases e'
        · rintro (⟨i, -, hz'⟩ | ⟨j, -, hz'⟩)
          · obtain ⟨he, hk'⟩ := End.port.inj hz'
            exact absurd ⟨he, by omega⟩ h1
          · obtain ⟨he, hk'⟩ := End.port.inj hz'
            exact absurd ⟨he, by omega⟩ h2
  rcases w with i | j | v
  · change _ = 1
    rw [count_map_eq_of_iff (a := End.port c ((i : ℕ) + 1)), hG.count_left i]
    intro z hz
    rw [eq_comm, key z hz]
    simp only [Sum.inl.injEq, reduceCtorEq, false_and, exists_false, or_false]
    constructor
    · rintro ⟨i', rfl, rfl⟩; rfl
    · rintro rfl; exact ⟨i, rfl, rfl⟩
  · change _ = 1
    rw [count_map_eq_of_iff (a := End.port d ((j : ℕ) + 1)), hG.count_right j]
    intro z hz
    rw [eq_comm, key z hz]
    simp only [reduceCtorEq, false_and, exists_false, Sum.inr.injEq, Sum.inl.injEq, false_or]
    constructor
    · rintro ⟨j', rfl, rfl⟩; rfl
    · rintro rfl; exact ⟨j, rfl, rfl⟩
  · change _ = 0
    refine count_map_eq_zero_of fun z hz e => ?_
    rcases (key z hz).1 e with ⟨i, h, -⟩ | ⟨j, h, -⟩ <;> cases h

/-- A name that is not fresh ends as many wires after the cut as before. -/
theorem count_cut_name_of_notMem
    -- a name that is none of the names `g`
    (y : ℕ)
    (hy : ∀ w, g w ≠ y) :
    -- it ends as many of the other wires after the cut as before
    ((W.bind wireEnds).map (cutEnd c d (fun i => g (.inl i)) (fun j => g (.inr (.inl j))))).count
      (.name y) = (W.bind wireEnds).count (.name y) := by
  refine count_map_eq_of_iff fun z _ => ?_
  match z with
  | .name x => simp [cutEnd, eq_comm]
  | .port e 0 => simp [cutEnd]
  | .port e (k + 1) =>
    simp only [cutEnd]
    split_ifs
    · simp only [End.name.injEq, iff_false]
      exact fun e' => hy _ e'.symm
    · simp only [End.name.injEq, iff_false]
      exact fun e' => hy _ e'.symm
    · simp

/-- The names of the renamed graph of the rule. -/
theorem count_rule_name
    -- a graph of a rule, the renumbering of its cells and injective names
    {a b : ℕ}
    {R : Graph S (Fin a ⊕ Fin b ⊕ Fin m)}
    {σ : ℕ → ℕ}
    {g : Fin a ⊕ Fin b ⊕ Fin m → ℕ}
    (hg : Function.Injective g)
    -- a name of the rule
    (w : Fin a ⊕ Fin b ⊕ Fin m) :
    -- `g w` ends as many wires of the renamed graph as `w` ends wires of `R`
    (R.ends.map (End.map σ g)).count (.name (g w)) = R.ends.count (.name w) := by
  refine count_map_eq_of_iff fun z _ => ?_
  cases z with
  | port _ _ => simp [End.map]
  | name x =>
    simp only [End.map, End.name.injEq]
    exact ⟨fun e => by rw [hg e], fun e => by rw [e]⟩

/-- A name that is not fresh ends no wire of the renamed graph of the rule. -/
theorem count_rule_name_of_notMem
    -- a graph of a rule, the renumbering of its cells and its names
    {a b : ℕ}
    {R : Graph S (Fin a ⊕ Fin b ⊕ Fin m)}
    {σ : ℕ → ℕ}
    {g : Fin a ⊕ Fin b ⊕ Fin m → ℕ}
    -- a name that is none of the names `g`
    (y : ℕ)
    (hy : ∀ w, g w ≠ y) :
    -- it ends no wire of the renamed graph
    (R.ends.map (End.map σ g)).count (.name y) = 0 := by
  refine count_map_eq_zero_of fun z _ e => ?_
  cases z with
  | port _ _ => cases e
  | name x => exact hy x (End.name.inj e)

end count

-- ============================================================================================
-- 6. Uniqueness for a fixed graph of the rule
-- ============================================================================================

section unique

-- the cells `c : α` and `d : β` of the active pair, the other cells, the other wires and the
-- cyclic wires of the graph, a rule `r` for `α`, `β` and a graph `R` of its right-hand side
variable {c d : ℕ} {α β : S.Sym} {C : Multiset (ℕ × S.Sym)} {W : Multiset (Sym2 (End ℕ))}
  {n : ℕ} {r : Rule S (S.arity α) (S.arity β)}
  {R : Graph S (Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal)}

/-- **A name ends at most two wires before the contraction of an interaction**, and a fresh name
of the cut ends exactly two or none (Lafont 1997, page 73). -/
theorem preInteract_count_name
    -- the graph is well-formed, with an active pair `c`, `d`
    (hG : Graph.WF (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ : Graph S ℕ))
    -- the rule is linear and `R` is a graph of its right-hand side
    (hrl : r.Linear)
    (hR : r.net.HasGraph R)
    -- a renumbering of the cells of the rule
    {σ : ℕ → ℕ}
    -- injective names that end none of the other wires
    {g : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal → ℕ}
    (hg : Function.Injective g)
    (hgW : ∀ w, End.name (g w) ∉ W.bind wireEnds) :
    -- every fresh name ends an even number of wires, at most two,
    (∀ w, (preInteract c d C W n R σ g).ends.count (.name (g w)) % 2 = 0 ∧
      (preInteract c d C W n R σ g).ends.count (.name (g w)) ≤ 2) ∧
    -- and every other name ends at most one wire
    (∀ y, (∀ w, g w ≠ y) → (preInteract c d C W n R σ g).ends.count (.name y) ≤ 1) := by
  refine ⟨fun w => ?_, fun y hy => ?_⟩
  · rw [preInteract_ends, Multiset.count_add, count_cut_name hG hg hgW, count_rule_name hg,
      hrl.count_name_graph hR]
    rcases w with i | j | v <;> simp
  · rw [preInteract_ends, Multiset.count_add, count_cut_name_of_notMem y hy,
      count_rule_name_of_notMem y hy, add_zero]
    exact hG.count_name_rest y

/-- The renamed fresh names: `g w` becomes `g' w`, every other name is kept. -/
noncomputable def freshRename
    -- the old fresh names and the new ones
    {ι : Type}
    (g g' : ι → ℕ)
    -- the name to rename
    (y : ℕ) :
    ℕ :=
  open Classical in if h : ∃ w, g w = y then g' h.choose else y

/-- The renaming sends an old fresh name to the new one. -/
theorem freshRename_apply
    -- injective old fresh names, and the new ones
    {ι : Type}
    {g : ι → ℕ}
    (hg : Function.Injective g)
    (g' : ι → ℕ)
    -- an index
    (w : ι) :
    -- `g w` becomes `g' w`
    freshRename g g' (g w) = g' w := by
  have h : ∃ w', g w' = g w := ⟨w, rfl⟩
  simp only [freshRename, h, dite_true]
  rw [hg h.choose_spec]

/-- The renaming keeps a name that is not an old fresh name. -/
theorem freshRename_of_notMem
    -- the old fresh names and the new ones
    {ι : Type}
    (g g' : ι → ℕ)
    -- a name that is none of the old fresh names
    {y : ℕ}
    (hy : ∀ w, g w ≠ y) :
    -- it is kept
    freshRename g g' y = y := by
  have h : ¬ ∃ w, g w = y := fun ⟨w, hw⟩ => hy w hw
  simp only [freshRename, h, dite_false]

/-- **Other fresh names give the graph renamed** (Lafont 1997, page 73). -/
theorem preInteract_mapEnd
    -- a renumbering of the cells of the rule
    {σ : ℕ → ℕ}
    -- two choices of fresh names, the first injective and ending none of the other wires
    {g g' : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal → ℕ}
    (hg : Function.Injective g)
    (hgW : ∀ w, End.name (g w) ∉ W.bind wireEnds) :
    -- renaming `g` to `g'` in the graph built with `g` gives the graph built with `g'`
    (preInteract c d C W n R σ g).mapEnd (End.map id (freshRename g g'))
      = preInteract c d C W n R σ g' := by
  simp only [preInteract, mapEnd, Multiset.map_add, Multiset.map_map]
  congr 2
  · rw [← Sym2.map_comp]
    apply map_wires_congr_ends
    intro z hz
    simp only [Function.comp_apply]
    match z with
    | .name y =>
      simp only [cutEnd, End.map, End.name.injEq]
      exact freshRename_of_notMem g g' fun w e => hgW w (e ▸ hz)
    | .port e 0 => rfl
    | .port e (k + 1) =>
      simp only [cutEnd]
      split_ifs <;> simp [End.map, freshRename_apply hg]
  · apply Multiset.map_congr rfl
    intro e _
    simp only [Function.comp_apply, Sym2.map_map]
    congr 1
    funext z
    cases z <;> simp [End.map, freshRename_apply hg]

/-- The renumbering of the cells of the rule from `σ` to `σ'`, keeping every other cell. -/
noncomputable def cellRename
    -- the cells of the rule, the old renumbering and the new one
    (s : Multiset ℕ)
    (σ σ' : ℕ → ℕ)
    -- the cell to renumber
    (y : ℕ) :
    ℕ :=
  open Classical in if h : ∃ x ∈ s, σ x = y then σ' h.choose else y

/-- The renumbering sends the old number of a cell of the rule to the new one. -/
theorem cellRename_apply
    -- the cells of the rule, an old renumbering injective on them, and a new one
    {s : Multiset ℕ}
    {σ : ℕ → ℕ}
    (hσ : Set.InjOn σ {x | x ∈ s})
    (σ' : ℕ → ℕ)
    -- a cell of the rule
    {x : ℕ}
    (hx : x ∈ s) :
    -- `σ x` becomes `σ' x`
    cellRename s σ σ' (σ x) = σ' x := by
  have h : ∃ x' ∈ s, σ x' = σ x := ⟨x, hx, rfl⟩
  simp only [cellRename, h, dite_true]
  rw [hσ h.choose_spec.1 hx h.choose_spec.2]

/-- The renumbering keeps a cell that is not an old number of a cell of the rule. -/
theorem cellRename_of_notMem
    -- the cells of the rule, the old renumbering and the new one
    (s : Multiset ℕ)
    (σ σ' : ℕ → ℕ)
    -- a cell that is no old number of a cell of the rule
    {y : ℕ}
    (hy : ∀ x ∈ s, σ x ≠ y) :
    -- it is kept
    cellRename s σ σ' y = y := by
  have h : ¬ ∃ x ∈ s, σ x = y := fun ⟨x, hx, e⟩ => hy x hx e
  simp only [cellRename, h, dite_false]

/-- **Another renumbering of the cells of the rule gives an isomorphic graph** (Lafont 1997,
page 73). -/
theorem preInteract_iso_cells
    -- the graph is well-formed, with an active pair `c`, `d`
    (hG : Graph.WF (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ : Graph S ℕ))
    -- the graph of the rule is well-formed
    (hRwf : R.WF)
    -- two renumberings of the cells of the rule, each injective on them and avoiding the
    -- cells of the graph
    {σ σ' : ℕ → ℕ}
    (hσ : Set.InjOn σ {x | x ∈ R.cells.map Prod.fst})
    (hσG : ∀ x ∈ R.cells.map Prod.fst, σ x ∉ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst)
    (hσ' : Set.InjOn σ' {x | x ∈ R.cells.map Prod.fst})
    (hσG' : ∀ x ∈ R.cells.map Prod.fst, σ' x ∉ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst)
    -- the fresh names
    (g : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal → ℕ) :
    -- the two graphs before contraction are isomorphic
    (preInteract c d C W n R σ g).Iso (preInteract c d C W n R σ' g) := by
  set s := R.cells.map Prod.fst with hs
  set κ := cellRename s σ σ' with hκ
  have hCs : ∀ e ∈ C.map Prod.fst, κ e = e := fun e he =>
    cellRename_of_notMem s σ σ' fun x hx hxe => hσG x hx (by
      rw [hxe]; simp only [Multiset.map_cons, Multiset.mem_cons]; exact Or.inr (Or.inr he))
  have hκσ : ∀ x ∈ s, κ (σ x) = σ' x := fun x hx => cellRename_apply hσ σ' hx
  refine ⟨κ, ?_, ?_, ?_, rfl⟩
  · -- `κ` is injective on the cells
    intro y hy y' hy' e
    simp only [preInteract, Multiset.map_add, Multiset.map_map, Multiset.mem_add,
      Set.mem_ofPred_eq] at hy hy'
    have hR : ∀ {y}, y ∈ R.cells.map (Prod.fst ∘ Prod.map σ id) → ∃ x ∈ s, σ x = y := by
      intro y hy
      obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hy
      exact ⟨p.1, Multiset.mem_map_of_mem _ hp, rfl⟩
    have hC' : ∀ {x}, x ∈ s → ∀ {y}, y ∈ C.map Prod.fst → σ' x ≠ y := fun hx y hy e => by
      refine hσG' _ hx ?_
      rw [e]
      simp only [Multiset.map_cons, Multiset.mem_cons]
      exact Or.inr (Or.inr hy)
    rcases hy with hy | hy <;> rcases hy' with hy' | hy'
    · rwa [hCs y hy, hCs y' hy'] at e
    · obtain ⟨x', hx', rfl⟩ := hR hy'
      rw [hCs y hy, hκσ x' hx'] at e
      exact absurd e.symm (hC' hx' hy)
    · obtain ⟨x, hx, rfl⟩ := hR hy
      rw [hCs y' hy', hκσ x hx] at e
      exact absurd e (hC' hx hy')
    · obtain ⟨x, hx, rfl⟩ := hR hy
      obtain ⟨x', hx', rfl⟩ := hR hy'
      rw [hκσ x hx, hκσ x' hx'] at e
      rw [hσ' hx hx' e]
  · -- the cells
    symm
    simp only [preInteract, Multiset.map_add, Multiset.map_map]
    congr 1
    · conv_lhs => rw [show C.map (Prod.map κ id) = C.map id from Multiset.map_congr rfl
        fun p hp => Prod.ext (hCs p.1 (Multiset.mem_map_of_mem _ hp)) rfl]
      exact Multiset.map_id C
    · refine Multiset.map_congr rfl fun p hp => ?_
      simp only [Function.comp_apply, Prod.map, id]
      rw [hκσ p.1 (Multiset.mem_map_of_mem _ hp)]
  · -- the wires
    simp only [preInteract, Multiset.map_add, Multiset.map_map]
    congr 1
    · rw [← Function.comp_def, ← Multiset.map_map]
      symm
      refine map_wires_eq_self fun z hz => ?_
      rw [bind_wireEnds_map_end] at hz
      cases z with
      | name _ => rfl
      | port e i =>
        obtain ⟨γ, hγ, -⟩ := hG.cut_port hz
        change End.port (κ e) i = End.port e i
        rw [hCs e (Multiset.mem_map_of_mem Prod.fst hγ)]
    · simp only [← Sym2.map_comp]
      symm
      apply map_wires_congr_ends
      intro z hz
      cases z with
      | name _ => rfl
      | port x i =>
        obtain ⟨γ, hγ, -⟩ := hRwf.cell x i hz
        change End.port (κ (σ x)) i = End.port (σ' x) i
        rw [hκσ x (Multiset.mem_map_of_mem Prod.fst hγ)]

/-- **The result of an interaction does not depend on the renumbering of the cells of the rule
nor on the fresh names** (Lafont 1997, page 73), for a fixed graph `R` of a linear rule. -/
theorem preInteract_unique
    -- the graph is well-formed, with an active pair `c`, `d`
    (hG : Graph.WF (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ : Graph S ℕ))
    -- the rule is linear and `R` is a graph of its right-hand side
    (hrl : r.Linear)
    (hR : r.net.HasGraph R)
    -- two renumberings of the cells of the rule, each injective on them and avoiding the
    -- cells of the graph
    {σ σ' : ℕ → ℕ}
    (hσ : Set.InjOn σ {x | x ∈ R.cells.map Prod.fst})
    (hσG : ∀ x ∈ R.cells.map Prod.fst, σ x ∉ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst)
    (hσ' : Set.InjOn σ' {x | x ∈ R.cells.map Prod.fst})
    (hσG' : ∀ x ∈ R.cells.map Prod.fst, σ' x ∉ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst)
    -- two choices of fresh names, each injective and ending none of the other wires
    {g g' : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal → ℕ}
    (hg : Function.Injective g)
    (hgW : ∀ w, End.name (g w) ∉ W.bind wireEnds)
    (hg' : Function.Injective g')
    (hgW' : ∀ w, End.name (g' w) ∉ W.bind wireEnds)
    -- the two graphs before contraction, contracted until every name ends at most one wire
    {H H' : Graph S ℕ}
    (hH : Relation.ReflTransGen Contract (preInteract c d C W n R σ g) H)
    (hH1 : ∀ x, H.ends.count (.name x) ≤ 1)
    (hH' : Relation.ReflTransGen Contract (preInteract c d C W n R σ' g') H')
    (hH1' : ∀ x, H'.ends.count (.name x) ≤ 1) :
    -- the two results are isomorphic
    H.Iso H' := by
  classical
  obtain ⟨hcg, hcy⟩ := preInteract_count_name hG hrl hR (σ := σ) hg hgW
  -- no fresh name is left in `H`
  have hHg : ∀ w, End.name (g w) ∉ H.ends := fun w hm => by
    have h1 := hH1 (g w)
    have h2 := contracts_count_name_mod_two hH (g w)
    have h3 := (hcg w).1
    have h4 := Multiset.count_pos.2 hm
    omega
  have hHρ : H.mapEnd (End.map id (freshRename g g')) = H := by
    obtain ⟨HC, HW, Hn⟩ := H
    simp only [mapEnd, Graph.mk.injEq, and_true, true_and]
    refine map_wires_eq_self fun z hz => ?_
    cases z with
    | port _ _ => rfl
    | name y =>
      simp only [End.map, End.name.injEq]
      exact freshRename_of_notMem g g' fun w e => hHg w (by rw [e]; exact hz)
  -- with the fresh names `g'`
  have hHg' := contracts_mapEnd (f := End.map id (freshRename g g')) (h := freshRename g g')
    (fun _ => rfl) hH
  rw [preInteract_mapEnd hg hgW, hHρ] at hHg'
  -- with the renumbering `σ'`
  obtain ⟨X, hX, iX⟩ := (preInteract_iso_cells hG hR.wf hσ hσG hσ' hσG' g').contracts hHg'
  have hX1 : ∀ x, X.ends.count (.name x) ≤ 1 := fun x => (iX.count_name x).trans_le (hH1 x)
  obtain ⟨hcg', hcy'⟩ := preInteract_count_name hG hrl hR (σ := σ') hg' hgW'
  have h2 : ∀ x, (preInteract c d C W n R σ' g').ends.count (.name x) ≤ 2 := fun x => by
    by_cases hx : ∃ w, g' w = x
    · obtain ⟨w, rfl⟩ := hx
      exact (hcg' w).2
    · exact (hcy' x fun w e => hx ⟨w, e⟩).trans (by omega)
  rw [contracts_unique h2 hX hH' hX1 hH1'] at iX
  exact iX

end unique

-- ============================================================================================
-- 7. Main result
-- ============================================================================================

/-- **The result of an interaction is unique** (Lafont 1997, Section 1.2, page 73). Let `G` be a
well-formed graph with cells `c : α` and `d : β` joined by their principal ports, and `r` a
linear rule for `α`, `β`. Two interactions of this pair, with any graphs `R₁`, `R₂` of the rule,
any renumberings `σ₁`, `σ₂` of their cells and any fresh names `g₁`, `g₂`, as in
`Graph.Interact`, give isomorphic graphs. -/
theorem interact_unique
    -- a well-formed graph whose cells `c : α` and `d : β` are joined by their principal ports,
    -- with the other cells `C`, the other wires `W` and `n` cyclic wires
    {c d : ℕ}
    {α β : S.Sym}
    {C : Multiset (ℕ × S.Sym)}
    {W : Multiset (Sym2 (End ℕ))}
    {n : ℕ}
    (hG : Graph.WF (⟨(c, α) ::ₘ (d, β) ::ₘ C, s(.port c 0, .port d 0) ::ₘ W, n⟩ : Graph S ℕ))
    -- a linear rule for `α`, `β`
    {r : Rule S (S.arity α) (S.arity β)}
    (hrl : r.Linear)
    -- two graphs of its right-hand side
    {R₁ R₂ : Graph S (Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal)}
    (hR₁ : r.net.HasGraph R₁)
    (hR₂ : r.net.HasGraph R₂)
    -- a renumbering of the cells of each, injective on them and avoiding the cells of the graph
    {σ₁ σ₂ : ℕ → ℕ}
    (hσ₁ : Set.InjOn σ₁ {x | x ∈ R₁.cells.map Prod.fst})
    (hσG₁ : ∀ x ∈ R₁.cells.map Prod.fst, σ₁ x ∉ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst)
    (hσ₂ : Set.InjOn σ₂ {x | x ∈ R₂.cells.map Prod.fst})
    (hσG₂ : ∀ x ∈ R₂.cells.map Prod.fst, σ₂ x ∉ ((c, α) ::ₘ (d, β) ::ₘ C).map Prod.fst)
    -- two choices of fresh names, each injective and ending none of the other wires
    {g₁ g₂ : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin r.internal → ℕ}
    (hg₁ : Function.Injective g₁)
    (hgW₁ : ∀ w, End.name (g₁ w) ∉ W.bind wireEnds)
    (hg₂ : Function.Injective g₂)
    (hgW₂ : ∀ w, End.name (g₂ w) ∉ W.bind wireEnds)
    -- the two graphs before contraction, contracted until every name ends at most one wire
    {H₁ H₂ : Graph S ℕ}
    (hH₁ : Relation.ReflTransGen Contract (preInteract c d C W n R₁ σ₁ g₁) H₁)
    (n₁ : ∀ x, H₁.ends.count (.name x) ≤ 1)
    (hH₂ : Relation.ReflTransGen Contract (preInteract c d C W n R₂ σ₂ g₂) H₂)
    (n₂ : ∀ x, H₂.ends.count (.name x) ≤ 1) :
    -- the two results are isomorphic
    H₁.Iso H₂ := by
  obtain ⟨τ, hτ, hc, hw, hl⟩ := Net.Linear.hasGraph_iso hrl.net_linear hR₁ hR₂
  have e : preInteract c d C W n R₂ σ₂ g₂ = preInteract c d C W n R₁ (σ₂ ∘ τ) g₂ := by
    simp only [preInteract, hc, hw, hl, Multiset.map_map, Prod.map_comp_map, Function.comp_id]
    congr 2
    refine Multiset.map_congr rfl fun e _ => ?_
    simp only [Function.comp_apply, Sym2.map_map]
    congr 1
    funext z
    cases z <;> rfl
  rw [e] at hH₂
  have hmem : ∀ x ∈ R₁.cells.map Prod.fst, τ x ∈ R₂.cells.map Prod.fst := fun x hx => by
    rw [hc, Multiset.map_map]
    obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.1 hx
    exact Multiset.mem_map.2 ⟨p, hp, rfl⟩
  exact preInteract_unique hG hrl hR₁ hσ₁ hσG₁
    (fun x hx y hy e => hτ hx hy (hσ₂ (hmem x hx) (hmem y hy) e))
    (fun x hx => hσG₂ _ (hmem x hx)) hg₁ hgW₁ hg₂ hgW₂ hH₁ n₁ hH₂ n₂

end Graph

end INet
