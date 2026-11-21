/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.RecursionFree
public import LeanPool.InteractionCombinators.Text.RenameInj
public import Mathlib.Data.Multiset.DershowitzManna

/-!
# Reduction terminates in a recursion-free system (page 86)

Lafont 1997, Section 2.4, journal page 86 (PDF page 18), after the definition of a
recursion-free system:

> It is easy to see that the process of reduction always terminates in such a system.

The measure is the multiset of the ranks of the cells of the net, `N.cells.map D.rank`, ordered
by the multiset order of Dershowitz and Manna (`Multiset.IsDershowitzMannaLT`). An interaction
`α`–`β` removes the two cells `α` and `β`, keeps the cells of the trees on their auxiliary ports
and of the rest of the net, and adds the cells of the right-hand side, which are those of the
sides `φ` and `ψ` of the chosen decomposition (`cells_rule`): every cell of `φ` is below `β`,
every cell of `ψ` below `α`. The multiset order on `ℕ` is well founded.

No linearity or well-formedness hypothesis on the system or on the net is needed: the
decomposition of a rule plugs back to the rule through linear sides (`Decomposition.Plugs`), so
every auxiliary port occurs once in the right-hand side, and the trees on the ports are neither
copied nor erased.

Contents, in the order of the file:

1. Definition: `System.RecursionFreeData.measure`, the multiset of the ranks of the cells.
2. Auxiliary lemmas on cells: `Net.cells_add`, `Net.cells_bind` (the cells of a net in which
   trees are plugged into the names), `Rule.cells_inst` (the cells of an instance of a rule whose
   ports occur once).
3. Auxiliary lemmas on a recursion-free system: `count_left`, `count_right` (every auxiliary port
   occurs once in a rule), `cells_rule` (the cells of a rule are those of its two sides),
   `measure_eq_of_equiv`, and `measure_step`: the measure decreases at every `Step`.
4. Main results: `System.RecursionFree.step_wellFounded`, `System.RecursionFree.stepE_wellFounded`
   (there is no infinite reduction, literal or up to `Equiv`), and the same stated with sequences,
   `not_step_seq`, `not_stepE_seq`.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Definition: the measure
-- ============================================================================================

namespace System.RecursionFreeData

-- the system and its ranks with decompositions
variable {I : System S} (D : I.RecursionFreeData)

/-- The measure of page 86: the multiset of the ranks of the cells of the net. -/
def measure
    -- the net
    (N : Net S ℕ) :
    Multiset ℕ :=
  N.cells.map D.rank

end System.RecursionFreeData

-- ============================================================================================
-- 2. Auxiliary lemmas: the cells of a net
-- ============================================================================================

/-- The cells of the union of two nets. -/
theorem Net.cells_add
    -- the two nets
    {ν : Type}
    (N M : Net S ν) :
    (N + M).cells = N.cells + M.cells :=
  Multiset.add_bind _ _ _

/-- The cells of a net in which the tree `g x` is plugged into each name `x`: those of the net
and, for each occurrence of a name, those of the tree plugged into it. -/
theorem Net.cells_bind
    -- the trees plugged into the names
    {ν μ : Type}
    (g : ν → Term S μ)
    -- the net
    (N : Net S ν) :
    (N.bind g).cells = N.cells + N.vars.bind fun x => (g x).cells := by
  unfold Net.cells Net.bind Net.vars
  rw [Multiset.bind_map, Multiset.bind_assoc, ← Multiset.bind_add]
  congr 1
  funext e
  induction e using Sym2.ind with
  | _ u v =>
    change eqCells s(u.bind g, v.bind g) = _
    simp only [eqCells_mk, eqVars_mk, Term.cells_bind, Multiset.add_bind]
    abel

/-- The cells of an instance of a rule whose auxiliary ports each occur once (page 72): the
cells of the right-hand side and those of the trees plugged into the ports. The internal wires
carry no cell. -/
theorem Rule.cells_inst
    -- the rule, in which every auxiliary port of either cell occurs once
    {a b : ℕ}
    (r : Rule S a b)
    (hl : ∀ i, r.net.vars.count (.inl i) = 1)
    (hr : ∀ j, r.net.vars.count (.inr (.inl j)) = 1)
    -- the trees on the auxiliary ports of the two cells
    (as : Fin a → Term S ℕ)
    (bs : Fin b → Term S ℕ)
    -- the names of the internal wires
    (f : Fin r.internal → ℕ) :
    (r.inst as bs f).cells = r.net.cells + ((∑ i, (as i).cells) + ∑ j, (bs j).cells) := by
  classical
  rw [Rule.inst, Net.cells_bind]
  congr 1
  ext c
  rw [Multiset.count_bind_fintype, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Multiset.count_add, Multiset.count_sum', Multiset.count_sum']
  simp [hl, hr]

-- ============================================================================================
-- 3. Auxiliary lemmas: the rules of a recursion-free system, and the measure decreases
-- ============================================================================================

namespace System.RecursionFreeData

-- the system and its ranks with decompositions
variable {I : System S} (D : I.RecursionFreeData)

include D in
/-- In a rule of a recursion-free system, every auxiliary port of the first cell occurs once
(page 86): the rule is plugged from linear sides (`Decomposition.Plugs`, `Rule.plug_linear`), and
`Equiv` keeps the free ports. -/
theorem count_left
    -- the rule `α`–`β` of the system
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r)
    -- an auxiliary port of `α`
    (i : Fin (S.arity α)) :
    r.net.vars.count (.inl i) = 1 := by
  obtain ⟨ι, hι, hE⟩ := D.plug α β r h
  have hp := (Rule.plug_linear (D.dec α β r h).σ (D.linear α β r h).1 (D.linear α β r h).2).left i
  have := (hE.free_iff (.inl i)).1 hp
  rwa [show (Sum.inl i : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin _) =
      Sum.map id (Sum.map id ι) (.inl i) from rfl,
    Net.count_vars_bind_var _ (Sum.map_injective.2 ⟨Function.injective_id,
      Sum.map_injective.2 ⟨Function.injective_id, hι⟩⟩)] at this

include D in
/-- In a rule of a recursion-free system, every auxiliary port of the second cell occurs once
(page 86). -/
theorem count_right
    -- the rule `α`–`β` of the system
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r)
    -- an auxiliary port of `β`
    (j : Fin (S.arity β)) :
    r.net.vars.count (.inr (.inl j)) = 1 := by
  obtain ⟨ι, hι, hE⟩ := D.plug α β r h
  have hp := (Rule.plug_linear (D.dec α β r h).σ (D.linear α β r h).1
    (D.linear α β r h).2).right j
  have := (hE.free_iff (.inr (.inl j))).1 hp
  rwa [show (Sum.inr (Sum.inl j) : Fin (S.arity α) ⊕ Fin (S.arity β) ⊕ Fin _) =
      Sum.map id (Sum.map id ι) (.inr (.inl j)) from rfl,
    Net.count_vars_bind_var _ (Sum.map_injective.2 ⟨Function.injective_id,
      Sum.map_injective.2 ⟨Function.injective_id, hι⟩⟩)] at this

/-- **The cells of a rule** (page 86): in a recursion-free system, the right-hand side of the rule
`α`–`β` has the cells of the two sides `φ` and `ψ` of its decomposition. -/
theorem cells_rule
    -- the rule `α`–`β` of the system
    {α β : S.Sym}
    {r : Rule S (S.arity α) (S.arity β)}
    (h : I.rule α β = some r) :
    r.net.cells = (D.dec α β r h).φ.net.cells + (D.dec α β r h).ψ.net.cells := by
  obtain ⟨ι, -, hE⟩ := D.plug α β r h
  have hc := hE.cells_eq
  rw [Rule.cells_plug, Net.cells_bind_var] at hc
  exact hc.symm

/-- `Equiv` keeps the measure: it keeps the cells (`Equiv.cells_eq`). -/
theorem measure_eq_of_equiv
    -- two nets that are the same graph
    {N M : Net S ℕ}
    (h : Equiv N M) :
    D.measure N = D.measure M := by
  unfold measure
  rw [h.cells_eq]

/-- **The measure decreases** (page 86): at an interaction `α`–`β`, the ranks of `α` and `β` are
replaced by the ranks of the cells of `φ` and `ψ`, each below `rank β` or `rank α`; the other
cells are kept. -/
theorem measure_step
    -- an interaction from `N` to `M`
    {N M : Net S ℕ}
    (h : Step I N M) :
    -- the measure of `M` is below that of `N` in the multiset order
    Multiset.IsDershowitzMannaLT (D.measure M) (D.measure N) := by
  obtain ⟨α, β, r, hr, as, bs, Δ, f, -, -⟩ := h
  refine ⟨((∑ i, (as i).cells + ∑ j, (bs j).cells) + Δ.cells).map D.rank,
    ((D.dec α β r hr).φ.net.cells + (D.dec α β r hr).ψ.net.cells).map D.rank,
    D.rank α ::ₘ D.rank β ::ₘ 0, Multiset.cons_ne_zero, ?_, ?_, ?_⟩
  · unfold measure
    rw [Net.cells_add, Rule.cells_inst r (D.count_left hr) (D.count_right hr), D.cells_rule hr,
      ← Multiset.map_add]
    congr 1
    abel
  · unfold measure
    rw [Net.cells_cons, eqCells_mk, Term.cells_app, Term.cells_app]
    simp only [Multiset.map_add, Multiset.map_cons, Multiset.cons_add, Multiset.add_cons,
      Multiset.add_zero]
    exact Multiset.cons_swap _ _ _
  · intro y hy
    obtain ⟨γ, hγ, rfl⟩ := Multiset.mem_map.1 hy
    rcases Multiset.mem_add.1 hγ with hγ | hγ
    · exact ⟨D.rank β, by simp, D.rank_φ α β r hr γ hγ⟩
    · exact ⟨D.rank α, by simp, D.rank_ψ α β r hr γ hγ⟩

end System.RecursionFreeData

-- ============================================================================================
-- 4. Main results: reduction terminates
-- ============================================================================================

/-- **Reduction terminates in a recursion-free system** (Lafont 1997, page 86: "It is easy to see
that the process of reduction always terminates in such a system"): there is no infinite
sequence of interactions. -/
theorem System.RecursionFree.step_wellFounded
    -- a recursion-free system
    {I : System S}
    (hI : I.RecursionFree) :
    -- the converse of `Step` is well founded
    WellFounded (fun N' N => Step I N N') := by
  obtain ⟨D⟩ := hI
  exact Subrelation.wf (fun h => D.measure_step h)
    (InvImage.wf D.measure Multiset.wellFounded_isDershowitzMannaLT)

/-- **Reduction of graphs terminates in a recursion-free system** (page 86): there is no infinite
sequence of interactions, even with a wire substitution before each (`StepE`), since `Equiv`
keeps the cells. -/
theorem System.RecursionFree.stepE_wellFounded
    -- a recursion-free system
    {I : System S}
    (hI : I.RecursionFree) :
    -- the converse of `StepE` is well founded
    WellFounded (fun N' N => StepE I N N') := by
  obtain ⟨D⟩ := hI
  refine Subrelation.wf (fun h => ?_)
    (InvImage.wf D.measure Multiset.wellFounded_isDershowitzMannaLT)
  obtain ⟨K, hE, hs⟩ := h
  change Multiset.IsDershowitzMannaLT _ _
  rw [D.measure_eq_of_equiv hE]
  exact D.measure_step hs

/-- **No infinite reduction** (page 86): in a recursion-free system, no sequence of nets
`N 0, N 1, …` has an interaction from each net to the next. -/
theorem System.RecursionFree.not_step_seq
    -- a recursion-free system
    {I : System S}
    (hI : I.RecursionFree)
    -- a sequence of nets
    (N : ℕ → Net S ℕ) :
    -- it is not the case that each net reduces in one interaction to the next
    ¬ ∀ n, Step I (N n) (N (n + 1)) :=
  fun h => (wellFounded_iff_isEmpty_descending_chain.1 hI.step_wellFounded).false ⟨N, h⟩

/-- **No infinite reduction of graphs** (page 86): in a recursion-free system, no sequence of nets
has a `StepE` from each net to the next. -/
theorem System.RecursionFree.not_stepE_seq
    -- a recursion-free system
    {I : System S}
    (hI : I.RecursionFree)
    -- a sequence of nets
    (N : ℕ → Net S ℕ) :
    -- it is not the case that each net reduces by a `StepE` to the next
    ¬ ∀ n, StepE I (N n) (N (n + 1)) :=
  fun h => (wellFounded_iff_isEmpty_descending_chain.1 hI.stepE_wellFounded).false ⟨N, h⟩

end INet
