/-
Copyright (c) 2026 Formalized Formal Logic contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalized Formal Logic contributors
-/

module

-- Ported and adapted for Lean Pool from the upstream revision recorded in the project card.

public import LeanPool.PointwiseComposition.Foundation.FirstOrder.Syntax.Classical.BinderNotation
public import LeanPool.PointwiseComposition.Foundation.Vorspiel.Finset.Card

/-!
Supporting results for pointwise provable equality. -/

namespace PointwiseComposition

@[expose] public section

namespace Matrix

open _root_.Matrix

variable {α : Type*}

/-- The iget construction in `Matrix`. -/
def iget [Inhabited α] (v : Fin k → α) (x : ℕ) : α :=
  if h : x < k then v ⟨x, h⟩ else default

end Matrix

namespace FFL

namespace FirstOrder

variable {L : Language} {ξ : Type*} [Semiformula.Operator.Eq L]

namespace Theory

section Eq

variable (L)

/-- The refl construction in `FFL.FirstOrder.Theory.Eq`. -/
abbrev Eq.refl : Sentence L :=
  “∀ x, x = x”

/-- The symm construction in `FFL.FirstOrder.Theory.Eq`. -/
abbrev Eq.symm : Sentence L :=
  “∀ x y, x = y → y = x”

/-- The trans construction in `FFL.FirstOrder.Theory.Eq`. -/
abbrev Eq.trans : Sentence L :=
  “∀ x y z, x = y → y = z → x = z”

variable {L}

/-- The func Ext construction in `FFL.FirstOrder.Theory.Eq`. -/
abbrev Eq.funcExt {k} (f : L.Func k) : Sentence L :=
  let σ : Semisentence L (k + k) :=
    (Matrix.conj fun i : Fin k ↦ “#((Fin.addCast k i)) = #(i.addNat k)”) ⇒ₗ
      op(=).operator
        ![Semiterm.func f (fun i ↦ #((Fin.addCast k i))),
          Semiterm.func f (fun i ↦ #(i.addNat k))]
  ∀¹* σ

/-- The rel Ext construction in `FFL.FirstOrder.Theory.Eq`. -/
abbrev Eq.relExt {k} (r : L.Rel k) : Sentence L :=
  let σ : Semisentence L (k + k) :=
    (Matrix.conj fun i : Fin k ↦ “#((Fin.addCast k i)) = #(i.addNat k)”) ⇒ₗ
      Semiformula.rel r (fun i ↦ #((Fin.addCast k i))) ⇒ₗ
        Semiformula.rel r (fun i ↦ #(i.addNat k))
  ∀¹* σ

variable (L)

/-- Data and laws for 𝐄𝐐 in `𝐄𝐐`. -/
inductive eqAxiom : Theory L
  | refl : eqAxiom (Eq.refl L)
  | symm : eqAxiom (Eq.symm L)
  | trans : eqAxiom (Eq.trans L)
  | funcExt {k} (f : L.Func k) : eqAxiom (Eq.funcExt f)
  | relExt {k} (r : L.Rel k) : eqAxiom (Eq.relExt r)

/-- The «term𝐄𝐐» construction in `FFL.FirstOrder.Theory`. -/
notation "𝐄𝐐" => eqAxiom

variable {L}

lemma Eq.defeq :
    𝐄𝐐 L =
      {Eq.refl L, Eq.symm L, Eq.trans L} ∪
          Set.range (fun f : (k : ℕ) × L.Func k ↦ Eq.funcExt f.2) ∪
        Set.range (fun f : (k : ℕ) × L.Rel k ↦ Eq.relExt f.2) :=
  by
  ext φ; constructor
  · rintro ⟨⟩
    case refl => simp
    case symm => simp
    case trans => simp
    case funcExt k f => left; right; exact ⟨⟨k, f⟩, rfl⟩
    case relExt k r => right; exact ⟨⟨k, r⟩, rfl⟩
  · rintro (((rfl | rfl | rfl) | ⟨f, rfl⟩) | ⟨r, rfl⟩)
    · exact eqAxiom.refl
    · exact eqAxiom.symm
    · exact eqAxiom.trans
    · exact eqAxiom.funcExt _
    · exact eqAxiom.relExt _

@[simp]
lemma EqAxiom.finite [L.Finite] : Set.Finite (𝐄𝐐 L) :=
  by
  have : Fintype ((k : ℕ) × L.Func k) := Language.Finite.func
  have : Fintype ((k : ℕ) × L.Rel k) := Language.Finite.rel
  rw [Eq.defeq]
  simp [Set.finite_range]

end Eq

end Theory

namespace Semiformula

/-- The exists Unique construction in `FFL.FirstOrder.Semiformula`. -/
def existsUnique {ξ} (φ : Semiformula L ξ (n + 1)) : Semiformula L ξ n :=
  “∃ y, !φ y⋯ ∧ ∀ z, !φ z⋯ → z = y”

/-- The «term∃¹! » construction in `FFL.FirstOrder.Semiformula`. -/
prefix:64 "∃¹! " => existsUnique

end Semiformula

namespace BinderNotation

open _root_.Lean Lean PrettyPrinter Delaborator SubExpr

/-- The «first order formula∃! » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∃! " firstOrderFormula:0 : firstOrderFormula

/-- The «first order formula∃! , » construction in `FFL.FirstOrder.BinderNotation`. -/
syntax :max "∃! " ident ", " firstOrderFormula:0 : firstOrderFormula

macro_rules
  | `(quoteformula($type)[$binders* | $fbinders* | ∃! $φ:firstOrderFormula]) => do
    let v := mkIdent (Name.mkSimple ("var" ++ toString binders.size))
    let binders' := binders.insertIdx 0 v
    `(∃¹! quoteformula($type)[$binders'* | $fbinders* | $φ])
  | `(quoteformula($type)[$binders* | $fbinders* | ∃! $x, $φ]) => do
    if binders.elem x then
      Macro.throwErrorAt x "error: variable is duplicated."
    else
      let binders' := binders.insertIdx 0 x
      `(∃¹! quoteformula($type)[$binders'* | $fbinders* | $φ])

end BinderNotation

end FirstOrder

end FFL

end

end PointwiseComposition
