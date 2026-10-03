/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.SemanticCore.PartialLowering
public import Mathlib.Data.Finset.Lattice.Fold

/-! NF weak partition development: ReplaySupport.Basic. -/


public section

namespace NFChoice.ReplaySupport

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.PartialLowering

/-- A deterministic supply of nominal variables strictly above a finite support. -/
@[expose]
def freshVar (support : Finset Var) (offset : Nat := 0) : Var :=
  support.sup id + offset + 1

theorem mem_lt_freshVar {support : Finset Var} {x : Var} (hx : x ∈ support)
    (offset : Nat := 0) : x < freshVar support offset :=
  by
  have hle : x ≤ support.sup id := Finset.le_sup (f := id) hx
  exact lt_of_le_of_lt (hle.trans (Nat.le_add_right _ _)) (Nat.lt_succ_self _)

theorem freshVar_not_mem (support : Finset Var) (offset : Nat := 0) :
    freshVar support offset ∉ support := by
  intro h
  exact (Nat.lt_irrefl _) (mem_lt_freshVar h offset)

theorem freshVar_not_mem_of_subset {small support : Finset Var}
    (hsubset : small ⊆ support) (offset : Nat := 0) : freshVar support offset ∉ small :=
  fun hmem => freshVar_not_mem support offset (hsubset hmem)

theorem freshVar_injective (support : Finset Var) {i j : Nat} (hij : i ≠ j) :
    freshVar support i ≠ freshVar support j :=
  by
  intro h
  apply hij
  simp only [freshVar] at h
  exact Nat.add_left_cancel (Nat.add_right_cancel h)

/-- Every exact Hailperin axiom is available in a model of the literal theory. -/
theorem realizes_literal_axiom {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF) (name : HailperinAxiomName) :
    Fol.realize_sentence S (literalAxiomFormula name) :=
  hNF (literalAxiom_mem name)

/-- Extensionality extracted from the exact `ax-ext` member of the theory. -/
theorem extensional_of_literal_model {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF) : Extensional S :=
  (extensional_iff_literal_axExt S).2 (realizes_literal_axiom hNF .axExt)

/-- Generic bridge used by generated concrete NF-leaf certificates.  The generated
file supplies only a finite support inclusion and a reduction-checkable
lowering equation for the universally closed source instance.
-/
theorem valid_literal_leaf {S : Fol.Structure LNF}
    (hNF : Fol.all_realize_sentence S LiteralHailperinNF) (name : HailperinAxiomName)
    (names : List Var) (p : Wff) (hcover : p.fv ⊆ names.toFinset)
    (hlower : lowerClosed (closeNames names p) = some (literalAxiomSyntax name)) :
    Wff.Valid S p :=
  valid_open_of_closed_lowering names p (literalAxiomSyntax name) hcover hlower
    (realizes_literal_axiom hNF name)

/-- Completeness boundary for the control experiment.  Once the generated replay
has proved nominal validity of `neg p` in every literal-Hailperin model, this
theorem produces the requested object-level first-order derivability result.
-/
theorem derives_not_of_nominal_validity (p : Wff) (f : Sentence) (hpClosed : p.fv = ∅)
    (hlower : lowerClosed p = some f)
    (hsemantic : ∀ (S : Fol.Structure LNF), Nonempty S →
          Fol.all_realize_sentence S LiteralHailperinNF → Wff.Valid S (Wff.neg p)) :
    LiteralHailperinNF ⊢ₛ' Fol.bd_not (Formula.toFlypitch f) :=
  by
  apply (Fol.completeness LiteralHailperinNF (Fol.bd_not (Formula.toFlypitch f))).2
  intro S hNonempty hNF
  let a : S := Classical.choice hNonempty
  let v : Var → S := fun _ => a
  have hnot : Wff.Holds S v (Wff.neg p) := hsemantic S hNonempty hNF v
  have hiff := lowerClosed_realize_iff p f hpClosed hlower v
  change ¬Fol.realize_sentence S (Formula.toFlypitch f)
  intro hrealize
  exact hnot (hiff.mpr hrealize)


end NFChoice.ReplaySupport
