/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.RecursionFree.DecompositionLemmas
public import LeanPool.InteractionCombinators.Universality.RecursionFree.Decomposition

/-!
# Recursion-free interaction systems (pages 85–87)

Lafont 1997, Section 2.4, pages 85–87 (PDF pages 17–19). Every rule `α_i`–`α_j` is decomposed
(page 85) into a net `φ_{i,j}` on the auxiliary ports of `α_i`, a net `ψ_{i,j}` on those of `α_j`,
and a permutation `σ_{i,j}` of the wires between them (`Decomposition`, `Rule.plug`). Page 86:

> To sum up, one can assume that in all cases, `φ_{j,i} = ψ_{i,j}`, `σ_{j,i} = σ_{i,j}`, and
> `σ_{i,j}` is involutive. Now, assume that the alphabet can be ordered in such a way that the net
> `φ_{i,j}`, when defined, contains only symbols which are strictly smaller than `α_j` (and
> symmetrically, `ψ_{i,j} = φ_{j,i}` contains only symbols which are strictly smaller than `α_i`).

and, just before, "If `i ≠ j`, it is always possible to include the permutation into `φ_{i,j}`
(or into `φ_{j,i}`), so that the decomposition is no longer canonical, but `σ_{i,j}` is an
identity."

## The definition

`System.RecursionFreeData I` gives an order on the alphabet (`rank`) and, for every rule
`I.rule α β = some r`, a decomposition `dec α β r h` such that

* plugging its sides through `σ` gives back `r`, up to `Equiv` and an injective renaming of the
  internal wires of `r` (`Decomposition.Plugs`, the form of `Rule.plug_decompose`);
* its sides are linear and reduced;
* `σ` is involutive; for a rule `α`–`α`, `ψ = φ`; for a rule `α`–`β` with `α ≠ β`, `σ = 1`;
* every cell of `φ` has rank `< rank β`, every cell of `ψ` has rank `< rank α`.

In this development a system has at most one of the rules `α`–`β`, `β`–`α` (`System.WellFormed`),
so the equations `φ_{j,i} = ψ_{i,j}` and `σ_{j,i} = σ_{i,j}` of the paper for `i ≠ j` say only how
to read the one existing rule from the other cell; they become conditions only for `i = j`, where
they read `ψ_{i,i} = φ_{i,i}` and `σ_{i,i}` involutive. The decomposition is data and need not be
the canonical one: the example of page 87 needs a non-canonical one.

`System.RecursionFree I` is `Nonempty I.RecursionFreeData`.

## The example of page 87

"A typical example is our system of interaction combinators without the rule `γδ` (using an
ordering such that `ε < γ` and `ε < δ`, and a non-canonical decomposition for `γε` and `δε`)."
`systemNoConDup` is `Comb.system` without `con`–`dup`; `systemNoConDup_recursionFree` proves it
recursion-free with ranks `era = 0`, `con = 1`, `dup = 2`.

The rules for an eraser are given in this development as `era`–`con` and `era`–`dup`
(`Comb.system`), so the eraser is the first cell `α` and `con` (or `dup`) the second cell `β`.
The canonical decomposition puts the two `era` cells into `ψ`, on the side of the ports of `con`;
the order would then ask `era < era`. The non-canonical decomposition of page 87 puts them into
`φ`, on the side of the eraser, which has no auxiliary port, with two middle wires: `φ` is
`era = m₀, era = m₁` and `ψ` joins the port `i` of `con` to `m_i`. The order asks `era < con`.

## The full system is not recursion-free

`system_not_recursionFree`: in the rule `con`–`dup`, the two `dup` cells and the two `con` cells
are shared between `φ` and `ψ` by any decomposition (`Equiv` keeps the cells). A `dup` cell in
`φ` would need `dup < dup`, so it is in `ψ` and `dup < con`; symmetrically `con < dup`.

Contents, in the order of the file:

1. Definitions: `Decomposition.Plugs`, `System.RecursionFreeData`, `System.RecursionFree`
   (page 86).
2. Definitions for the example of page 87: the system `systemNoConDup`; the sides `idSide`,
   `eraSide`, `emptySide`; the decompositions `decConCon`, `decDupDup`, `decEraEra`, `decEraBin`,
   `decNoConDup`; the order `rankNoConDup`.
3. Auxiliary lemmas on `systemNoConDup`: `systemNoConDup_rule`, `systemNoConDup_conDup`,
   `systemNoConDup_wellFormed`.
4. Auxiliary lemmas on the decompositions: the sides are linear and reduced (`idSide_linear`,
   …, `emptySide_reduced`); the sides plug back the rules (`decConCon_plugs`, `decDupDup_plugs`,
   `decEraEra_plugs`, `decEraBin_plugs`); the canonical decomposition of `era`–`con` would not
   do (`eraBin_decompose`).
5. Auxiliary lemmas on the cells of `con`–`dup`: `Rule.cells_plug`, `dup_mem_cells_conDup`,
   `con_mem_cells_conDup`.
6. Main results: `recursionFreeDataNoConDup` and `systemNoConDup_recursionFree`, the combinators
   without `con`–`dup` are recursion-free (page 87); `system_not_recursionFree`, the full system
   is not.
-/

@[expose] public section

namespace INet

variable {S : Signature}

open Term

-- ============================================================================================
-- 1. Definitions: recursion-free systems
-- ============================================================================================

/-- Plugging the two sides of `D` through its permutation gives back the rule `r`, up to `Equiv`
and an injective renaming of the internal wires of `r`: the form in which
`Rule.plug_decompose` states it for the canonical decomposition (page 85). -/
def Decomposition.Plugs
    -- the numbers of auxiliary ports of the two cells
    {a b : ℕ}
    -- the decomposition and the rule
    (D : Decomposition S a b)
    (r : Rule S a b) :
    Prop :=
  -- there is a renaming `ι` of the internal wires of `r` into those of the plugged sides
  ∃ ι : Fin r.internal → Fin (Rule.plug D.φ D.ψ D.σ).internal,
    -- that is injective,
    Function.Injective ι ∧
    -- and the plugged sides are the same graph as `r` renamed by `ι`
    Equiv (Rule.plug D.φ D.ψ D.σ).net (r.net.bind fun x => var (Sum.map id (Sum.map id ι) x))

/-- The data that makes an interaction system recursion-free (Lafont 1997, page 86): an order on
the alphabet, and a decomposition of every rule (page 85) normalised as on page 86, whose side
`φ_{i,j}` on the ports of `α_i` contains only symbols smaller than `α_j`, and whose side `ψ_{i,j}`
on the ports of `α_j` contains only symbols smaller than `α_i`. -/
structure System.RecursionFreeData
    -- the interaction system
    (I : System S) where
  /-- The order on the alphabet: `α < β` when `rank α < rank β`. -/
  rank : S.Sym → ℕ
  /-- The decomposition chosen for each rule. -/
  dec :
    ∀ α β (r : Rule S (S.arity α) (S.arity β)), I.rule α β = some r →
      Decomposition S (S.arity α) (S.arity β)
  /-- Plugging the sides gives back the rule (page 85). -/
  plug :
    ∀ α β r (h : I.rule α β = some r),
      (dec α β r h).Plugs r
  /-- The sides are linear. -/
  linear :
    ∀ α β r (h : I.rule α β = some r),
      (dec α β r h).φ.Linear ∧ (dec α β r h).ψ.Linear
  /-- The sides are reduced nets (page 85). -/
  reduced :
    ∀ α β r (h : I.rule α β = some r),
      (dec α β r h).φ.Reduced ∧ (dec α β r h).ψ.Reduced
  /-- `σ_{i,j}` is involutive (page 86). -/
  involutive :
    ∀ α β r (h : I.rule α β = some r),
      Function.Involutive (dec α β r h).σ
  /-- For a rule `α_i`–`α_i`, `φ_{i,i} = ψ_{i,i}` (page 86, `φ_{j,i} = ψ_{i,j}` with `i = j`). -/
  self :
    ∀ α r (h : I.rule α α = some r),
      (dec α α r h).ψ = (dec α α r h).φ
  /-- For a rule `α_i`–`α_j` with `i ≠ j`, `σ_{i,j}` is an identity (page 86). -/
  ne :
    ∀ α β r (h : I.rule α β = some r),
      α ≠ β → (dec α β r h).σ = 1
  /-- `φ_{i,j}` contains only symbols strictly smaller than `α_j` (page 86). -/
  rank_φ :
    ∀ α β r (h : I.rule α β = some r),
      ∀ γ ∈ (dec α β r h).φ.net.cells, rank γ < rank β
  /-- `ψ_{i,j}` contains only symbols strictly smaller than `α_i` (page 86). -/
  rank_ψ :
    ∀ α β r (h : I.rule α β = some r),
      ∀ γ ∈ (dec α β r h).ψ.net.cells, rank γ < rank α

/-- An interaction system is recursion-free (Lafont 1997, page 86) if its alphabet can be ordered
and its rules decomposed so that `φ_{i,j}` contains only symbols smaller than `α_j` and `ψ_{i,j}`
only symbols smaller than `α_i`. -/
def System.RecursionFree
    -- the interaction system
    (I : System S) :
    Prop :=
  Nonempty I.RecursionFreeData

namespace Comb

open DecompositionReview

-- ============================================================================================
-- 2. Definitions: the combinators without `con`–`dup` and their decompositions (page 87)
-- ============================================================================================

/-- Lafont's combinators without the rule `con`–`dup` (`γδ`), page 87. -/
def systemNoConDup : System sig where
  rule
    | .con, .con => some ruleConCon
    | .dup, .dup => some ruleDupDup
    | .era, .era => some ruleEraEra
    | .era, .con => some ruleEraBin
    | .era, .dup => some ruleEraBin
    | _, _ => none

/-- The side that joins each auxiliary port `i` to the middle wire `i`. -/
def idSide : Rule sig 2 2 := ⟨0, s(pl 0, pr 0) ::ₘ {s(pl 1, pr 1)}⟩

/-- The side of the eraser in `era`–`con` and `era`–`dup` (page 87, non-canonical): an eraser on
each of the two middle wires. -/
def eraSide : Rule sig 0 2 := ⟨0, s(mkEra, pr 0) ::ₘ {s(mkEra, pr 1)}⟩

/-- The empty side. -/
def emptySide : Rule sig 0 0 := ⟨0, 0⟩

/-- `con`–`con`: both sides are `idSide`, and `σ` exchanges the two middle wires. -/
def decConCon : Decomposition sig 2 2 := ⟨2, idSide, idSide, Equiv.swap 0 1⟩

/-- `dup`–`dup`: both sides are `idSide`, and `σ` is the identity. -/
def decDupDup : Decomposition sig 2 2 := ⟨2, idSide, idSide, 1⟩

/-- `era`–`era`: nothing. -/
def decEraEra : Decomposition sig 0 0 := ⟨0, emptySide, emptySide, 1⟩

/-- `era`–`con` and `era`–`dup` (page 87, non-canonical): the erasers go into `φ`, on the side of
the eraser; `ψ` joins the ports of the binary cell to the middle wires. -/
def decEraBin : Decomposition sig 0 2 := ⟨2, eraSide, idSide, 1⟩

/-- The decomposition of each rule of `systemNoConDup`; arbitrary where there is no rule. -/
def decNoConDup :
    -- for the two cells `α`, `β`, a decomposition between their auxiliary ports
    (α β : sig.Sym) → Decomposition sig (sig.arity α) (sig.arity β)
  | .con, .con => decConCon
  | .dup, .dup => decDupDup
  | .era, .era => decEraEra
  | .era, .con => decEraBin
  | .era, .dup => decEraBin
  | _, _ => ⟨0, ⟨0, 0⟩, ⟨0, 0⟩, 1⟩

/-- The order of page 87: `era < con < dup`. -/
def rankNoConDup : sig.Sym → ℕ
  | .era => 0
  | .con => 1
  | .dup => 2

-- ============================================================================================
-- 3. Auxiliary lemmas: the combinators without `con`–`dup` form an interaction system
-- ============================================================================================

/-- `systemNoConDup` has the rules of `system` for every pair other than `con`–`dup`. -/
theorem systemNoConDup_rule
    -- two symbols that are not `con`, `dup` in this order
    (α β : sig.Sym)
    (h : ¬ (α = Comb.con ∧ β = Comb.dup)) :
    -- the rule for `α`–`β` is that of the full system
    systemNoConDup.rule α β = system.rule α β := by
  cases α <;> cases β <;> first | rfl | exact absurd ⟨rfl, rfl⟩ h

/-- `systemNoConDup` has no rule for `con`–`dup`, where `system` has `ruleConDup`. -/
theorem systemNoConDup_conDup :
    -- `systemNoConDup` has no rule for `con`–`dup`,
    systemNoConDup.rule Comb.con Comb.dup = none ∧
      -- and `system` has `ruleConDup`
      system.rule Comb.con Comb.dup = some ruleConDup := ⟨rfl, rfl⟩

/-- The combinators without `con`–`dup` form an interaction system. -/
theorem systemNoConDup_wellFormed : systemNoConDup.WellFormed where
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first
        | exact ruleConCon_linear | exact ruleDupDup_linear | exact ruleEraEra_linear
        | exact ruleEraBin_linear
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first
        | exact ruleConCon_reduced | exact ruleDupDup_reduced | exact ruleEraEra_reduced
        | exact ruleEraBin_reduced
  unique := by
    intro α β hne h
    cases α <;> cases β <;> first | rfl | exact absurd rfl hne | cases h
  symm := by
    refine fun α r h => Rule.symm_of_equiv ?_
    revert α r h
    intro α r h
    cases α <;> cases h <;>
      first
        | exact Equiv.of_eq ruleConCon_swap | exact Equiv.of_eq ruleDupDup_swap
        | exact Equiv.of_eq ruleEraEra_swap

-- ============================================================================================
-- 4. Auxiliary lemmas: the decompositions of the rules without `con`–`dup`
-- ============================================================================================

-- The sides are linear.

theorem idSide_linear : idSide.Linear := ⟨by decide, by decide, by decide⟩

theorem eraSide_linear : eraSide.Linear := ⟨by decide, by decide, by decide⟩

theorem emptySide_linear : emptySide.Linear := ⟨by decide, by decide, by decide⟩

-- The sides are reduced.

theorem idSide_reduced : idSide.Reduced := by
  change ∀ e ∈ (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0) from idSide.net),
    ∃ (p : Fin 2 ⊕ Fin 2 ⊕ Fin 0) (t : Term sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0)),
      e = s(Term.var p, t) ∧ ∀ w : Fin 0, p ≠ .inr (.inr w)
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 0) from idSide.net),
      e ∈ [s(pl 0, pr 0), s(pl 1, pr 1)] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact ⟨_, _, rfl, fun w => w.elim0⟩

theorem eraSide_reduced : eraSide.Reduced := by
  change ∀ e ∈ (show Net sig (Fin 0 ⊕ Fin 2 ⊕ Fin 0) from eraSide.net),
    ∃ (p : Fin 0 ⊕ Fin 2 ⊕ Fin 0) (t : Term sig (Fin 0 ⊕ Fin 2 ⊕ Fin 0)),
      e = s(Term.var p, t) ∧ ∀ w : Fin 0, p ≠ .inr (.inr w)
  intro e he
  have key : ∀ e ∈ (show Net sig (Fin 0 ⊕ Fin 2 ⊕ Fin 0) from eraSide.net),
      e ∈ [s(mkEra, pr 0), s(mkEra, pr 1)] := by decide
  have h := key e he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl <;> exact ⟨_, _, Sym2.eq_swap, fun w => w.elim0⟩

theorem emptySide_reduced : emptySide.Reduced :=
  fun e he => (Multiset.notMem_zero e he).elim

-- The sides plug back the rules.

/-- Plugging the sides of `decConCon` gives `ruleConCon`: the port `0` of the first cell meets
the port `1` of the second, and the port `1` the port `0`. -/
theorem decConCon_plugs : decConCon.Plugs ruleConCon := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  have h₁ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
    (N := (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from
      (Rule.plug decConCon.φ decConCon.ψ decConCon.σ).net))
    (M := s(pr 1, pl 0) ::ₘ s(pl 1, pw 1) ::ₘ {s(pr 0, pw 1)})
    (.inr (.inr 0)) (pl 0) (pr 1) (pw 0) (s(pl 1, pw 1) ::ₘ {s(pr 0, pw 1)})
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₂ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
    (N := s(pr 1, pl 0) ::ₘ s(pl 1, pw 1) ::ₘ {s(pr 0, pw 1)})
    (M := s(pr 0, pl 1) ::ₘ {s(pr 1, pl 0)})
    (.inr (.inr 1)) (pl 1) (pr 0) (pw 1) {s(pr 1, pl 0)}
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have e : (s(pr 0, pl 1) ::ₘ {s(pr 1, pl 0)} : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2)) =
      (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from ruleConCon.net.bind
        fun x => var (Sum.map id (Sum.map id (Fin.elim0 : Fin 0 → Fin 2)) x)) := by decide
  exact h₁.trans (h₂.trans (Equiv.of_eq e))

/-- Plugging the sides of `decDupDup` gives `ruleDupDup`: the ports are joined in order. -/
theorem decDupDup_plugs : decDupDup.Plugs ruleDupDup := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  have h₁ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
    (N := (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from
      (Rule.plug decDupDup.φ decDupDup.ψ decDupDup.σ).net))
    (M := s(pr 0, pl 0) ::ₘ s(pl 1, pw 1) ::ₘ {s(pr 1, pw 1)})
    (.inr (.inr 0)) (pl 0) (pr 0) (pw 0) (s(pl 1, pw 1) ::ₘ {s(pr 1, pw 1)})
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₂ := equiv_wire_of_eq (ν := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
    (N := s(pr 0, pl 0) ::ₘ s(pl 1, pw 1) ::ₘ {s(pr 1, pw 1)})
    (M := s(pr 1, pl 1) ::ₘ {s(pr 0, pl 0)})
    (.inr (.inr 1)) (pl 1) (pr 1) (pw 1) {s(pr 0, pl 0)}
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have e : (s(pr 1, pl 1) ::ₘ {s(pr 0, pl 0)} : Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2)) =
      (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 2) from ruleDupDup.net.bind
        fun x => var (Sum.map id (Sum.map id (Fin.elim0 : Fin 0 → Fin 2)) x)) := by decide
  exact h₁.trans (h₂.trans (Equiv.of_eq e))

/-- Plugging the sides of `decEraEra` gives `ruleEraEra`, the empty net. -/
theorem decEraEra_plugs : decEraEra.Plugs ruleEraEra :=
  ⟨Fin.elim0, fun i => i.elim0, Equiv.of_eq (by decide)⟩

/-- Plugging the sides of `decEraBin` gives `ruleEraBin`: an eraser on each port of the binary
cell. -/
theorem decEraBin_plugs : decEraBin.Plugs ruleEraBin := by
  refine ⟨Fin.elim0, fun i => i.elim0, ?_⟩
  have h₁ := equiv_wire_of_eq (ν := Fin 0 ⊕ Fin 2 ⊕ Fin 2)
    (N := (show Net sig (Fin 0 ⊕ Fin 2 ⊕ Fin 2) from
      (Rule.plug decEraBin.φ decEraBin.ψ decEraBin.σ).net))
    (M := s(pr 0, mkEra) ::ₘ s(mkEra, pw 1) ::ₘ {s(pr 1, pw 1)})
    (.inr (.inr 0)) mkEra (pr 0) (pw 0) (s(mkEra, pw 1) ::ₘ {s(pr 1, pw 1)})
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have h₂ := equiv_wire_of_eq (ν := Fin 0 ⊕ Fin 2 ⊕ Fin 2)
    (N := s(pr 0, mkEra) ::ₘ s(mkEra, pw 1) ::ₘ {s(pr 1, pw 1)})
    (M := s(pr 1, mkEra) ::ₘ {s(pr 0, mkEra)})
    (.inr (.inr 1)) mkEra (pr 1) (pw 1) {s(pr 0, mkEra)}
    (by unfold Net.Linear; decide) (by decide) (by decide) (by decide)
  have e : (s(pr 1, mkEra) ::ₘ {s(pr 0, mkEra)} : Net sig (Fin 0 ⊕ Fin 2 ⊕ Fin 2)) =
      (show Net sig (Fin 0 ⊕ Fin 2 ⊕ Fin 2) from ruleEraBin.net.bind
        fun x => var (Sum.map id (Sum.map id (Fin.elim0 : Fin 0 → Fin 2)) x)) := by decide
  exact h₁.trans (h₂.trans (Equiv.of_eq e))

-- The canonical decomposition of `era`–`con` would not do.

/-- Why page 87 needs a non-canonical decomposition for `era`–`con` and `era`–`dup`: the
canonical decomposition (`Rule.decompose`) of `ruleEraBin` has no middle wire, an empty `φ`, and
puts both erasers into `ψ`, on the ports of the binary cell. The order would then ask that `era`,
a cell of `ψ_{era,con}`, be smaller than `era`. -/
theorem eraBin_decompose :
    -- the canonical decomposition of `ruleEraBin` has no middle wire,
    ruleEraBin.decompose.k = 0 ∧
    -- its side `φ` is empty,
    (show Net sig (Fin 0 ⊕ Fin 0 ⊕ Fin 0) from ruleEraBin.decompose.φ.net) = 0 ∧
    -- and its side `ψ` puts an `era` on each port of the binary cell
    (show Net sig (Fin 2 ⊕ Fin 0 ⊕ Fin 0) from ruleEraBin.decompose.ψ.net) =
      s(.var (.inl 0), mkEra) ::ₘ {s(.var (.inl 1), mkEra)} :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

-- ============================================================================================
-- 5. Auxiliary lemmas: the cells of the rule `con`–`dup`
-- ============================================================================================

/-- The cells of a plugged rule are those of its two sides. -/
theorem _root_.INet.Rule.cells_plug
    -- the numbers of auxiliary ports of the two cells, and of middle wires
    {a b k : ℕ}
    -- the two sides and the permutation of the middle wires
    (φ : Rule S a k)
    (ψ : Rule S b k)
    (σ : Equiv.Perm (Fin k)) :
    -- the cells of the plugged rule are the cells of `φ` and those of `ψ`
    (Rule.plug φ ψ σ).net.cells = φ.net.cells + ψ.net.cells := by
  change Net.cells (ν := Fin a ⊕ Fin b ⊕ Fin (k + φ.internal + ψ.internal))
    (φ.net.bind (fun x => var (Rule.plugL x)) + ψ.net.bind (fun x => var (Rule.plugR σ x))) = _
  unfold Net.cells
  rw [Multiset.add_bind]
  exact congrArg₂ (· + ·) (Net.cells_bind_var _ _) (Net.cells_bind_var _ _)

/-- The rule `con`–`dup` has a `dup` cell. -/
theorem dup_mem_cells_conDup : (Comb.dup : sig.Sym) ∈ ruleConDup.net.cells := by
  change (Comb.dup : sig.Sym) ∈ Net.cells (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 4) from ruleConDup.net)
  refine Multiset.mem_bind.2 ⟨s(.var (.inl 0), mkDup (.var (.inr (.inr 0))) (.var (.inr (.inr 1)))),
    by decide, ?_⟩
  rw [eqCells_mk]
  exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons.2 (Or.inl rfl)))

/-- The rule `con`–`dup` has a `con` cell. -/
theorem con_mem_cells_conDup : (Comb.con : sig.Sym) ∈ ruleConDup.net.cells := by
  change (Comb.con : sig.Sym) ∈ Net.cells (show Net sig (Fin 2 ⊕ Fin 2 ⊕ Fin 4) from ruleConDup.net)
  refine Multiset.mem_bind.2 ⟨s(.var (.inr (.inl 0)),
    mkCon (.var (.inr (.inr 0))) (.var (.inr (.inr 2)))), by decide, ?_⟩
  rw [eqCells_mk]
  exact Multiset.mem_add.2 (Or.inr (Multiset.mem_cons.2 (Or.inl rfl)))

-- ============================================================================================
-- 6. Main results: the combinators without `con`–`dup` are recursion-free, the full system is not
-- ============================================================================================

/-- The combinators without `con`–`dup` are recursion-free (Lafont 1997, page 87), with the order
`era < con < dup` and the non-canonical decomposition `decEraBin` for `era`–`con` and
`era`–`dup`. -/
def recursionFreeDataNoConDup : systemNoConDup.RecursionFreeData where
  rank := rankNoConDup
  dec α β _ _ := decNoConDup α β
  plug := by
    intro α β r h
    cases α <;> cases β <;> cases h
    · exact decConCon_plugs
    · exact decDupDup_plugs
    · exact decEraBin_plugs
    · exact decEraBin_plugs
    · exact decEraEra_plugs
  linear := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first
        | exact ⟨idSide_linear, idSide_linear⟩ | exact ⟨eraSide_linear, idSide_linear⟩
        | exact ⟨emptySide_linear, emptySide_linear⟩
  reduced := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first
        | exact ⟨idSide_reduced, idSide_reduced⟩ | exact ⟨eraSide_reduced, idSide_reduced⟩
        | exact ⟨emptySide_reduced, emptySide_reduced⟩
  involutive := by
    intro α β r h
    cases α <;> cases β <;> cases h <;>
      first | exact fun l => rfl | exact fun l => Equiv.swap_apply_self _ _ l
  self := by
    intro α r h
    cases α <;> cases h <;> rfl
  ne := by
    intro α β r h hne
    cases α <;> cases β <;> cases h <;> first | rfl | exact absurd rfl hne
  rank_φ := by
    intro α β r h
    cases α <;> cases β <;> cases h <;> decide
  rank_ψ := by
    intro α β r h
    cases α <;> cases β <;> cases h <;> decide

/-- **Page 87.** The interaction combinators without the rule `con`–`dup` (`γδ`) form a
recursion-free system. -/
theorem systemNoConDup_recursionFree : systemNoConDup.RecursionFree :=
  ⟨recursionFreeDataNoConDup⟩

/-- The full system of interaction combinators is not recursion-free (page 87 removes the rule
`con`–`dup` for this reason): in any decomposition of `con`–`dup`, the `dup` cells must go into
`ψ`, which needs `dup < con`, and the `con` cells into `φ`, which needs `con < dup`. -/
theorem system_not_recursionFree : ¬ system.RecursionFree := by
  rintro ⟨R⟩
  obtain ⟨ι, -, hE⟩ := R.plug Comb.con Comb.dup ruleConDup rfl
  have hc := hE.cells_eq
  rw [Rule.cells_plug, Net.cells_bind_var] at hc
  have hφ := R.rank_φ Comb.con Comb.dup ruleConDup rfl
  have hψ := R.rank_ψ Comb.con Comb.dup ruleConDup rfl
  have hd : (Comb.dup : sig.Sym) ∈ (R.dec Comb.con Comb.dup ruleConDup rfl).φ.net.cells +
      (R.dec Comb.con Comb.dup ruleConDup rfl).ψ.net.cells :=
    hc ▸ dup_mem_cells_conDup
  have hk : (Comb.con : sig.Sym) ∈ (R.dec Comb.con Comb.dup ruleConDup rfl).φ.net.cells +
      (R.dec Comb.con Comb.dup ruleConDup rfl).ψ.net.cells :=
    hc ▸ con_mem_cells_conDup
  rcases Multiset.mem_add.1 hd with h | h <;> rcases Multiset.mem_add.1 hk with h' | h'
  · exact absurd (hφ _ h) (lt_irrefl _)
  · exact absurd (hφ _ h) (lt_irrefl _)
  · have := hψ _ h; have := hφ _ h'; omega
  · exact absurd (hψ _ h') (lt_irrefl _)

end Comb

end INet
