/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalNFLiteralHandlers

/-! NF weak partition development: NominalNFLiteralBaseFour. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.DirectNominalPrf.Nominal.NFLiteralHandlers


theorem axExtLowering (x y z : Var) (_hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∀ rho,
      lowerWff rho (axExtGoal x y z) =
        openAll2 (literalAxiomFormula .axExt).fst (&(rho x)) (&(rho y)) :=
  by
  intro rho
  simp [axExtGoal, synWb, openAll, openAll2, literalAxiomFormula, literalAxiomSyntax,
    literalAxExt, lowerWff, bindRho, Wff.neg, Formula.toFlypitch, Formula.biimp,
    Formula.conj, Formula.neg, GenericLogicalHandlers.nfMem, hxz, hyz]
  aesop

/-- Proof-translation construction identified upstream as `axExt`. -/
@[expose]
noncomputable def axExt (x y z : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    NPrf (axExtGoal x y z) :=
  axExtOfLowering x y z hxy hxz hyz (axExtLowering x y z hxy hxz hyz)

theorem axNinLowering (x y z w : Var) (_hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    ∀ rho,
      lowerWff rho (axNinGoal x y z w) =
        openAll2 (literalAxiomFormula .axNin).fst (&(rho x)) (&(rho y)) :=
  by
  intro rho
  simp [axNinGoal, synWex, synWb, synWnan, synWa, openAll, openAll2,
    literalAxiomFormula, literalAxiomSyntax, literalAxNin, lowerWff, bindRho, Wff.neg,
    Formula.toFlypitch, Formula.ex, Formula.biimp, Formula.conj, Formula.neg,
    GenericLogicalHandlers.nfMem, hxz, hxw, hyz, hyw, hzw]
  aesop

/-- Proof-translation construction identified upstream as `axNin`. -/
@[expose]
noncomputable def axNin (x y z w : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) : NPrf (axNinGoal x y z w) :=
  axNinOfLowering x y z w hxy hxz hxw hyz hyw hzw
    (axNinLowering x y z w hxy hxz hxw hyz hyw hzw)

theorem axSnLowering (x y z : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    ∀ rho,
      lowerWff rho (axSnGoal x y z) =
        openAll (literalAxiomFormula .axSn).fst (&(rho x)) :=
  by
  intro rho
  simp [axSnGoal, synWex, synWb, openAll, literalAxiomFormula, literalAxiomSyntax,
    literalAxSn, lowerWff, bindRho, Wff.neg, Formula.toFlypitch, Formula.ex,
    Formula.biimp, Formula.conj, Formula.neg, hxy, hxz, hyz]
  aesop

/-- Proof-translation construction identified upstream as `axSn`. -/
@[expose]
noncomputable def axSn (x y z : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    NPrf (axSnGoal x y z) :=
  axSnOfLowering x y z hxy hxz hyz (axSnLowering x y z hxy hxz hyz)

theorem ax1cLowering (x y z w : Var) (hxy : x ≠ y) (_hxz : x ≠ z) (_hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    ∀ rho, lowerWff rho (ax1cGoal x y z w) = (literalAxiomFormula .ax1c).fst :=
  by
  intro rho
  simp [ax1cGoal, synWex, synWb, literalAxiomFormula, literalAxiomSyntax, literalAx1c,
    lowerWff, bindRho, Wff.neg, Formula.toFlypitch, Formula.ex, Formula.biimp,
    Formula.conj, Formula.neg, GenericLogicalHandlers.nfMem, hxy, hyz, hyw, hzw]
  aesop

/-- Proof-translation construction identified upstream as `ax1c`. -/
@[expose]
noncomputable def ax1c (x y z w : Var) (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
    (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) : NPrf (ax1cGoal x y z w) :=
  ax1cOfLowering x y z w hxy hxz hxw hyz hyw hzw
    (ax1cLowering x y z w hxy hxz hxw hyz hyw hzw)


end NFChoice.DirectNominalPrf.Nominal.NFLiteralBaseFour
