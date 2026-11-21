/-
Copyright (c) 2026 Lorenzo Battistela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lorenzo Battistela
-/

/- Modified for Lean Pool: module declarations, imports, and repository lint. -/

module

public import LeanPool.InteractionCombinators.Universality.General.CodeCellsPlug
public import LeanPool.InteractionCombinators.Universality.General.CodeDataSides
public import LeanPool.InteractionCombinators.Universality.RecursionFree.PlugsNetTr
public import LeanPool.InteractionCombinators.Universality.General.CodeTr

/-!
# The translation of Fig. 10 is compatible for sides given as data (pages 86, 89–90)

Lafont 1997, page 86 (PDF page 18): a decomposition in normal form has `φ_{j,i} = ψ_{i,j}`,
`σ_{j,i} = σ_{i,j}` and `σ_{i,j}` involutive, and plugging its two sides gives back the rule;
Fig. 10, page 89 (PDF page 21), and page 90: the translation built from these sides.

The results are stated first with the symbols numbered by any `e : S.Sym ≃ Fin n` (names ending in
`E`), then for `e := symEnum S` under the names without `E`.

Contents, in the order of the file:

1. Definition: `System.SidesPlug` — the property of a family of expanded sides that the
   compatibility proof uses: for every rule `α`–`β`, the sides `side α β` and `side β α` are both
   defined, share `k` and `σ`, and plug back the rule. It is the conclusion of
   `System.DecData.sides_expand`.
2. Auxiliary lemmas.
   * `System.DecData.sidesPlug` — the sides `D.side` of decomposition data of a well-formed system
     have the property.
   * `codeTranslationE_strict` — for any `e`, the translation is strict.
3. Main results.
   * `codeTranslationE_compatible_of_sides` — the translation of Fig. 10 built from any sides with
     the property, for any numbering `e : S.Sym ≃ Fin n` of the symbols, is compatible
     (`Translation.Compatible`). No well-formedness is assumed.
   * `codeTranslation_compatible_of_sides` — the case `e := symEnum S`.
   * `System.DecData.codeTranslationE_compatible` — for decomposition data of a well-formed system
     and any `e`, the translation is compatible.
-/

@[expose] public section

namespace INet

-- ============================================================================================
-- 1. Definition
-- ============================================================================================

/-- **The sides plug back into the rules** (Lafont 1997, page 86, normal form of a
decomposition; Fig. 10, page 89, and page 90). For every rule `α`–`β` of `I`, the expanded side
`side α β` of `α` against `β` and the expanded side `side β α` of `β` against `α` are both
defined, have the same number `k` of middle wires and the same involution `σ`
(`σ_{j,i} = σ_{i,j}`), and plugging the first against the second through `σ` gives back the
rule. This is the conclusion of `System.DecData.sides_expand`. -/
def System.SidesPlug
    -- the interaction system
    {S : Signature}
    (I : System S)
    -- the family of expanded sides: `side α β` is the side of `α` against `β`, if any
    (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α))) :
    Prop :=
  -- for every rule `r` of `I` between `α` and `β`,
  ∀ {α β : S.Sym} {r : Rule S (S.arity α) (S.arity β)}, I.rule α β = some r →
    -- there are `k` middle wires, two linear expanded sides `φ`, `ψ` and an involution `σ`
    ∃ (k : ℕ) (φ : Rule S (S.arity α) k) (ψ : Rule S (S.arity β) k) (σ : Equiv.Perm (Fin k))
      (hσ : Function.Involutive σ) (hl : φ.Linear) (he : φ.Expanded)
      (hl' : ψ.Linear) (he' : ψ.Expanded),
      -- such that the side of `α` against `β` is `φ` with `σ`,
      side α β = some ⟨k, φ, σ, hl, he, hσ⟩ ∧
      -- the side of `β` against `α` is `ψ` with the same `σ`,
      side β α = some ⟨k, ψ, σ, hl', he', hσ⟩ ∧
      -- and plugging `φ` against `ψ` through `σ` gives back `r`
      (⟨k, φ, ψ, σ⟩ : Decomposition S (S.arity α) (S.arity β)).Plugs r

-- ============================================================================================
-- 2. Auxiliary lemmas
-- ============================================================================================

/-- **The sides of decomposition data plug back into the rules** (Lafont 1997, page 86 and
Fig. 10, pages 89–90): in a well-formed system, the expanded sides `D.side` of any decomposition
data `D` satisfy `System.SidesPlug`. This is `System.DecData.sides_expand`. -/
theorem System.DecData.sidesPlug
    -- a well-formed interaction system
    {S : Signature}
    {I : System S}
    (hI : I.WellFormed)
    -- decomposition data of its rules
    (D : I.DecData) :
    -- its sides plug back into the rules
    I.SidesPlug D.side :=
  fun h => D.sides_expand hI h

namespace Comb

open Term

/-- **The translation of Fig. 10 is strict for any numbering `e` of the symbols** (Lafont 1997,
definition page 80, Fig. 10 pages 89–90): no `[α]` of `codeTranslationE e side` is a wire. -/
theorem codeTranslationE_strict
    -- a numbering of the symbols
    {S : Signature}
    {n : ℕ}
    (e : S.Sym ≃ Fin n)
    -- any family of expanded sides
    (side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α))) :
    -- the translation built from them is strict
    (codeTranslationE e side).Strict :=
  codeNetE_strict e side

-- ============================================================================================
-- 3. Main results: the translation is compatible
-- ============================================================================================

/-- **The translation of Fig. 10 is compatible with reduction, for sides given as data and any
numbering `e` of the symbols** (Lafont 1997, Section 2.7, Fig. 10, pages 89–90, the analogue of
Fig. 7, pages 85–86; page 90: no order on the symbols is needed). For any `e : S.Sym ≃ Fin n` and
any family `side` of expanded sides that plug back into the rules of `I` (`System.SidesPlug`), the
cells `[α]` and `[β]` of `codeTranslationE e side` plugged by their roots reduce, up to wires
(`StepsE system`), to a translation of an instance of the rule. Neither finiteness of the
alphabet beyond `e` nor well-formedness of `I` is assumed. -/
theorem codeTranslationE_compatible_of_sides
    -- the interaction system, and a numbering of its symbols
    {S : Signature}
    {I : System S}
    {n : ℕ}
    (e : S.Sym ≃ Fin n)
    -- a family of expanded sides that plug back into the rules of `I`
    {side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α))}
    (hside : I.SidesPlug side) :
    -- the translation built from them is compatible with the reduction of the combinators
    (codeTranslationE e side).Compatible I system := by
  intro α β r h xs ys f g hlin
  obtain ⟨k, φ, ψ, σ, hσ, hl, he, hl', he', hs, hs', hP⟩ := hside h
  obtain ⟨k₀, k₁, M, tφ, tψ, hS, hE, htφ, htψ⟩ :=
    codeCells_plugE e side α β xs ys f g 0 φ ψ σ hσ hl he hl' he' hs hs' hlin
  have hL : Net.Linear (plugTermTarget σ tφ tψ xs ys) := by
    have := hE.linear (hS.linear system_wellFormed.linear hlin)
    rwa [add_zero] at this
  obtain ⟨h₁, N', hN', hE'⟩ :=
    netTr_plug_termTr (codeTranslationE e side) he hl he' hl' σ k₀ k₁ tφ tψ htφ htψ xs ys hL
  obtain ⟨h₂, N'', hN'', hE''⟩ := Decomposition.Plugs.netTr_inst_of_sides
    (D := ⟨k, φ, ψ, σ⟩) hP hl hl' xs ys h₁ hN'
  refine ⟨M, N'', h₂, hS, ?_, hN''⟩
  rw [add_zero] at hE
  exact hE.trans (hE'.symm.trans hE'')

/-- **The translation of Fig. 10 is compatible with reduction, for sides given as data**
(Lafont 1997, Section 2.7, Fig. 10, pages 89–90, the analogue of Fig. 7, pages 85–86). For any
family `side` of expanded sides that plug back into the rules of `I` (`System.SidesPlug`), the
cells `[α]` and `[β]` of Fig. 10 plugged by their roots reduce, up to wires (`StepsE system`), to a
translation of an instance of the rule. The system `I` need not be well formed: well-formedness
is used only to obtain such sides from decomposition data (`System.DecData.sidesPlug`). -/
theorem codeTranslation_compatible_of_sides
    -- the interaction system, on a finite alphabet
    {S : Signature}
    [Finite S.Sym]
    {I : System S}
    -- a family of expanded sides that plug back into the rules of `I`
    {side : ∀ α : S.Sym, S.Sym → Option (ExpSide S (S.arity α))}
    (hside : I.SidesPlug side) :
    -- the translation built from them is compatible with the reduction of the combinators
    (codeTranslation side).Compatible I system :=
  codeTranslationE_compatible_of_sides (symEnum S) hside

/-- **The translation of Fig. 10 is compatible with reduction, for any numbering `e` of the
symbols** (Lafont 1997, Section 2.7, Fig. 10, pages 89–90; page 90). For every rule `α`–`β` of a
well-formed system, any decomposition data `D` and any `e : S.Sym ≃ Fin n`, the cells `[α]` and
`[β]` of `codeTranslationE e D.side` plugged by their roots reduce, up to wires
(`StepsE system`), to a translation of an instance of the rule. -/
theorem _root_.INet.System.DecData.codeTranslationE_compatible
    -- the interaction system, and a numbering of its symbols
    {S : Signature}
    {I : System S}
    {n : ℕ}
    (e : S.Sym ≃ Fin n)
    -- the system is well formed, with decomposition data `D`
    (hI : I.WellFormed)
    (D : I.DecData) :
    -- the translation built from the sides of `D` is compatible
    (codeTranslationE e D.side).Compatible I system :=
  codeTranslationE_compatible_of_sides e (D.sidesPlug hI)

end Comb

end INet
