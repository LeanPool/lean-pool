/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWffPrf

/-! NF weak partition development: NominalLogicalWrappers. -/


public section

namespace NFChoice.DirectNominalPrf

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore

namespace Nominal

/-! Nominal-syntax wrappers for the remaining primitive logical steps used by
the Metamath replay.  The wrappers whose source axiom carries a freshness or
substitution side condition take the corresponding *syntactic lowering
identity* explicitly.  The certificate emitter can discharge these
identities from its already checked `$d`/substitution data, without adding a
formula axiom to the Flypitch theory.
-/


/-- Metamath `ax-gen`: generalization of a closed nominal proof. -/
@[expose]
def gen {p : Wff} (hp : NPrf p) (x : Var) : NPrf (.all x p) := fun rho =>
  by
  apply Fol.prf.allI
  rw [Fol.SentTheory.lift_irrel LiteralHailperinNF]
  exact hp (bindRho rho x)

/-- Metamath `ax-5` (quantified implication). -/
@[expose]
def ax5 (x : Var) (p q : Wff) :
    NPrf (.imp (.all x (.imp p q)) (.imp (.all x p) (.all x q))) := fun rho =>
  GenericLogicalHandlers.ax5 LiteralHailperinNF.fst (lowerWff (bindRho rho x) p)
    (lowerWff (bindRho rho x) q)

/-- Fresh-variable introduction at nominal syntax.  The equality is exactly the
de-Bruijn shift certificate induced by the source `$d x p` condition.
-/
@[expose]
def freshIntroOfShift (p : Wff) (x : Var)
    (hShift : ∀ rho, lowerWff (bindRho rho x) p = Fol.lift_formula1 (lowerWff rho p)) :
    NPrf (.imp p (.all x p)) := fun rho =>
  by
  change
    Fol.prf LiteralHailperinNF.fst
      (Fol.preformula.imp (lowerWff rho p) (Fol.preformula.all (lowerWff (bindRho rho x) p)))
  rw [hShift rho]
  exact GenericLogicalHandlers.freshIntro LiteralHailperinNF.fst (lowerWff rho p)

/-- Metamath `ax-17`, with its checked `$d x p` evidence compiled to shift. -/
@[expose]
def ax17OfShift (p : Wff) (x : Var)
    (hShift : ∀ rho, lowerWff (bindRho rho x) p = Fol.lift_formula1 (lowerWff rho p)) :
    NPrf (.imp p (.all x p)) :=
  freshIntroOfShift p x hShift

/-- Metamath `ax-6`.  Its matrix `¬∀x.p` is syntactically fresh for `x`; the
separate identity keeps that structural fact kernel-visible.
-/
@[expose]
def ax6OfShift (x : Var) (p : Wff)
    (hShift : ∀ rho, lowerWff (bindRho rho x) (Wff.neg (.all x p)) =
          Fol.lift_formula1 (lowerWff rho (Wff.neg (.all x p)))) :
    NPrf (.imp (Wff.neg (.all x p)) (.all x (Wff.neg (.all x p)))) :=
  freshIntroOfShift (Wff.neg (.all x p)) x hShift

/-- Metamath `ax-7`.  `hSwap` is the exact named-binder/de-Bruijn swap identity
for the instantiated matrix.
-/
@[expose]
def ax7OfSwap (x y : Var) (p : Wff)
    (hSwap : ∀ rho, lowerWff (bindRho (bindRho rho y) x) p =
          GenericLogicalHandlers.swap01 (lowerWff (bindRho (bindRho rho x) y) p)) :
    NPrf (.imp (.all x (.all y p)) (.all y (.all x p))) := fun rho =>
  by
  change
    Fol.prf LiteralHailperinNF.fst
      (Fol.preformula.imp
        (Fol.preformula.all (Fol.preformula.all (lowerWff (bindRho (bindRho rho x) y) p)))
        (Fol.preformula.all (Fol.preformula.all (lowerWff (bindRho (bindRho rho y) x) p))))
  rw [hSwap rho]
  exact
    GenericLogicalHandlers.ax7Core LiteralHailperinNF.fst
      (lowerWff (bindRho (bindRho rho x) y) p)

/-- Metamath `ax-8` (equality transitivity in its bundled orientation). -/
@[expose]
noncomputable def ax8 (x y z : Var) :
    NPrf (.imp (.objEq x y) (.imp (.objEq x z) (.objEq y z))) := fun rho =>
  GenericLogicalHandlers.ax8 LiteralHailperinNF.fst (&(rho x)) (&(rho y)) (&(rho z))

/-- `ax-9` when the two source variable names are distinct. -/
@[expose]
def ax9OfNe (x y : Var) (hxy : y ≠ x) : NPrf (Wff.neg (.all x (Wff.neg (.objEq x y)))) :=
  fun rho => by
  simpa [Wff.neg, lowerWff, neg, Fol.not', bindRho, hxy, Fol.lift_term1,
    Fol.lift_term_at] using (GenericLogicalHandlers.ax9 LiteralHailperinNF.fst (&(rho y)))

/-- Metamath `ax-13` (left equality for membership). -/
@[expose]
def ax13 (x y z : Var) : NPrf (.imp (.objEq x y) (.imp (.objMem x z) (.objMem y z))) :=
  fun rho =>
  GenericLogicalHandlers.ax13 LiteralHailperinNF.fst (&(rho x)) (&(rho y)) (&(rho z))

/-- Metamath `ax-14` (right equality for membership). -/
@[expose]
def ax14 (x y z : Var) : NPrf (.imp (.objEq x y) (.imp (.objMem z x) (.objMem z y))) :=
  fun rho =>
  GenericLogicalHandlers.ax14 LiteralHailperinNF.fst (&(rho x)) (&(rho y)) (&(rho z))

/-- Metamath `ax-12`, with the freshness of `y = z` for `x` represented by its
lowering/shift identity.  This is the nondegenerate branch used after `$d`
checking; coincident bundled-variable branches can be emitted separately.
-/
@[expose]
def ax12OfShift (x y z : Var)
    (hShift : ∀ rho, lowerWff (bindRho rho x) (.objEq y z) =
          Fol.lift_formula1 (lowerWff rho (.objEq y z))) :
    NPrf (.imp (Wff.neg (.objEq x y)) (.imp (.objEq y z) (.all x (.objEq y z)))) :=
  fun rho =>
  by
  change
    Fol.prf LiteralHailperinNF.fst
      (Fol.preformula.imp (lowerWff rho (Wff.neg (.objEq x y)))
        (Fol.preformula.imp (lowerWff rho (.objEq y z))
          (Fol.preformula.all (lowerWff (bindRho rho x) (.objEq y z)))))
  rw [hShift rho]
  exact
    GenericLogicalHandlers.ax12Core LiteralHailperinNF.fst
      (lowerWff rho (Wff.neg (.objEq x y))) (lowerWff rho (.objEq y z))

/-- Metamath `ax-11`.  The two equalities are the exact source-instantiation and
target-binder identities for the chosen one-hole de-Bruijn template.
-/
@[expose]
noncomputable def ax11OfTemplate (x y : Var) (p : Wff) (hxy : y ≠ x)
    (template : (Var → Nat) → Fol.formula LNF)
    (hSource : ∀ rho, GenericLogicalHandlers.ax11Inst (lowerWff (bindRho rho y) p) (&(rho y)) =
          (template rho) [Fol.lift_term1 (&(rho x)) // 0]f)
    (hTarget : ∀ rho, (template rho) [(&0) // 0]f = lowerWff (bindRho rho x) p) :
    NPrf (.imp (.objEq x y) (.imp (.all y p) (.all x (.imp (.objEq x y) p)))) :=
  fun rho => by
  simpa [lowerWff, bindRho, hxy, Fol.lift_term1, Fol.lift_term_at] using
    (GenericLogicalHandlers.ax11Core LiteralHailperinNF.fst (&(rho x)) (&(rho y))
      (lowerWff (bindRho rho y) p) (lowerWff (bindRho rho x) p) (template rho)
      (hSource rho) (hTarget rho))


end Nominal
end NFChoice.DirectNominalPrf
