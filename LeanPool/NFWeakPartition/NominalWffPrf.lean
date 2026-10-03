/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.SemanticCore.Basic
public import LeanPool.NFWeakPartition.GenericLogicalHandlers

/-! NF weak partition development: NominalWffPrf. -/


public section

namespace NFChoice.DirectNominalPrf

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore

namespace Nominal

@[expose]
def liftRho (rho : Var → Nat) : Var → Nat := fun x => rho x + 1

@[expose]
def bindRho (rho : Var → Nat) (x : Var) : Var → Nat := fun y =>
  if y = x then 0 else rho y + 1

@[expose]
def updateRho (rho : Var → Nat) (x : Var) (value : Nat) : Var → Nat := fun y =>
  if y = x then value else rho y

@[expose]
def neg (p : Fol.formula LNF) : Fol.formula LNF :=
  Fol.preformula.imp p Fol.preformula.falsum

@[expose]
def conj (p q : Fol.formula LNF) : Fol.formula LNF :=
  neg (Fol.preformula.imp p (neg q))

@[expose]
def biimp (p q : Fol.formula LNF) : Fol.formula LNF :=
  conj (Fol.preformula.imp p q) (Fol.preformula.imp q p)

@[expose]
def ex (p : Fol.formula LNF) : Fol.formula LNF :=
  neg (Fol.preformula.all (neg p))

mutual
  @[expose]
  def lowerClassPred (rho : Var → Nat) (candidate : Nat) : Class → Fol.formula LNF
    | .cv x => GenericLogicalHandlers.nfMem (&candidate) (&(rho x))
    | .cab x p => lowerWff (updateRho rho x candidate) p
  @[expose]
  def lowerWff (rho : Var → Nat) : Wff → Fol.formula LNF
    | .falsum => Fol.preformula.falsum
    | .imp p q => Fol.preformula.imp (lowerWff rho p) (lowerWff rho q)
    | .all x p => Fol.preformula.all (lowerWff (bindRho rho x) p)
    | .objEq x y => Fol.preformula.equal (&(rho x)) (&(rho y))
    | .objMem x y => GenericLogicalHandlers.nfMem (&(rho x)) (&(rho y))
    | .classEq A B =>
      Fol.preformula.all
        (biimp (lowerClassPred (liftRho rho) 0 A) (lowerClassPred (liftRho rho) 0 B))
    | .classMem A B =>
      ex
        (conj (Fol.preformula.all (biimp (GenericLogicalHandlers.nfMem (&0) (&1))
              (lowerClassPred (liftRho (liftRho rho)) 0 A))) (lowerClassPred (liftRho rho) 0 B))
end

@[expose]
def NPrf (p : Wff) : Type :=
  ∀ rho : Var → Nat, Fol.prf LiteralHailperinNF.fst (lowerWff rho p)

@[expose]
def mp {p q : Wff} (hp : NPrf p) (hpq : NPrf (.imp p q)) : NPrf q := fun rho =>
  GenericLogicalHandlers.mp (hp rho) (hpq rho)

@[expose]
def ax1 (p q : Wff) : NPrf (.imp p (.imp q p)) := fun rho =>
  GenericLogicalHandlers.ax1 LiteralHailperinNF.fst (lowerWff rho p) (lowerWff rho q)

@[expose]
def ax2 (p q r : Wff) : NPrf (.imp (.imp p (.imp q r)) (.imp (.imp p q) (.imp p r))) :=
  fun rho =>
  GenericLogicalHandlers.ax2 LiteralHailperinNF.fst (lowerWff rho p) (lowerWff rho q)
    (lowerWff rho r)

@[expose]
def ax3 (p q : Wff) : NPrf (.imp (.imp (Wff.neg p) (Wff.neg q)) (.imp q p)) := fun rho =>
  GenericLogicalHandlers.ax3 LiteralHailperinNF.fst (lowerWff rho p) (lowerWff rho q)

@[expose]
def axMeredith (p q r s t : Wff) :
    NPrf
      (.imp (.imp (.imp (.imp (.imp p q) (.imp (Wff.neg r) (Wff.neg s))) r) t)
        (.imp (.imp t p) (.imp s p))) :=
  fun rho =>
  GenericLogicalHandlers.axMeredith LiteralHailperinNF.fst (lowerWff rho p)
    (lowerWff rho q) (lowerWff rho r) (lowerWff rho s) (lowerWff rho t)

/-- A source definition becomes reflexivity after its constructor is unfolded. -/
@[expose]
noncomputable def biimpRefl (p : Wff) : NPrf (Wff.biimp p p) := fun rho => by
  simpa [Wff.biimp, Wff.conj, Wff.neg, lowerWff, Fol.biimp, Fol.and', Fol.not'] using
    (Fol.biimp_refl LiteralHailperinNF.fst (lowerWff rho p))


end Nominal
end NFChoice.DirectNominalPrf
