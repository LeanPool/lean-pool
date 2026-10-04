/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalLogicalWrappers
public import LeanPool.NFWeakPartition.ClassBoundaryRawHandlersDev010

/-! NF weak partition development: NominalClassHandlersDev011. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.DirectCertificate.ClassBoundaryNormalizationDev005
open NFChoice.DirectCertificate.ClassBoundaryCoreDev006
open NFChoice.DirectCertificate.ClassBoundaryRawHandlersDev010

/-- Proof-translation construction identified upstream as `Theory`. -/
abbrev Theory : Fol.SentTheory LNF :=
  LiteralHailperinNF

/-- The candidate-slot predicate used for a nominal class at valuation `rho`. -/
@[expose]
def classPred (rho : Var → Nat) (A : Class) : Fol.formula LNF :=
  lowerClassPred (liftRho rho) 0 A

/-- Exact normalized source conclusion of `df-clab`. -/
@[expose]
def dfClabGoal (x y : Var) (p : Wff) : Wff :=
  Wff.biimp (.classMem (.cv x) (.cab y p)) (sbDefiniens x y p)

/-- Exact normalized source conclusion of `df-cleq`. -/
@[expose]
def dfCleqGoal (x : Var) (A B : Class) : Wff :=
  Wff.biimp (.classEq A B)
    (.all x (Wff.biimp (.classMem (.cv x) A) (.classMem (.cv x) B)))

/-- Exact normalized source conclusion of `df-clel`. -/
@[expose]
def dfClelGoal (x : Var) (A B : Class) : Wff :=
  Wff.biimp (.classMem A B)
    (Wff.ex x (Wff.conj (.classEq (.cv x) A) (.classMem (.cv x) B)))

/-- Sound `df-clab` handler.  `hClassMem` is structural lowering; `hSubst` is
the compiler's checked normalization equation identifying application of a
class abstraction with the already-expanded proper-substitution definiens.
-/
@[expose]
noncomputable def dfClabOfLowering (x y : Var) (p : Wff)
    (hClassMem : ∀ rho, lowerWff rho (.classMem (.cv x) (.cab y p)) =
          classMem (cvPred (&(rho x))) (classPred rho (.cab y p)))
    (hSubst : ∀ rho, lowerWff rho (sbDefiniens x y p) =
          applyPred (classPred rho (.cab y p)) (&(rho x))) :
    NPrf (dfClabGoal x y p) := fun rho =>
  by
  change
    Theory.fst ⊢
      lowerWff rho (.classMem (.cv x) (.cab y p)) ⇔ lowerWff rho (sbDefiniens x y p)
  rw [hClassMem rho, hSubst rho]
  exact classMemCv (&(rho x)) (classPred rho (.cab y p))

/-- Sound `df-cleq` handler.  The first proof argument preserves the original
MM0/Metamath exporter signature.  The exact theory already contains ax-ext;
the two bridge equations are the kernel-visible images of `$d x A` and
`$d x B`.
-/
@[expose]
noncomputable def dfCleqOfShift (x y z : Var) (A B : Class)
    (_hAxExt : NPrf
        (.imp (.all x (Wff.biimp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z))))
          (.classEq (.cv y) (.cv z))))
    (hClassEq :
      ∀ rho, lowerWff rho (.classEq A B) = classEq (classPred rho A) (classPred rho B))
    (hMemA : ∀ rho,
        lowerWff (bindRho rho x) (.classMem (.cv x) A) = liftedClassMem (classPred rho A))
    (hMemB : ∀ rho, lowerWff (bindRho rho x) (.classMem (.cv x) B) =
          liftedClassMem (classPred rho B)) :
    NPrf (dfCleqGoal x A B) := fun rho =>
  by
  change
    Theory.fst ⊢
      lowerWff rho (.classEq A B) ⇔
        ∀'(lowerWff (bindRho rho x) (.classMem (.cv x) A) ⇔
            lowerWff (bindRho rho x) (.classMem (.cv x) B))
  rw [hClassEq rho, hMemA rho, hMemB rho]
  exact rawDfCleq (classPred rho A) (classPred rho B)

/-- Sound `df-clel` handler.  The three identities expose the source DV facts
and the structural class lowering rather than hiding them in an axiom.
-/
@[expose]
noncomputable def dfClelOfShift (x : Var) (A B : Class)
    (hClassMem :
      ∀ rho, lowerWff rho (.classMem A B) = classMem (classPred rho A) (classPred rho B))
    (hEqA : ∀ rho, lowerWff (bindRho rho x) (.classEq (.cv x) A) =
          represents (&0) (Fol.liftFormulaAt (classPred rho A) 1 1))
    (hMemB : ∀ rho, lowerWff (bindRho rho x) (.classMem (.cv x) B) =
          liftedClassMem (classPred rho B)) :
    NPrf (dfClelGoal x A B) := fun rho =>
  by
  change
    Theory.fst ⊢
      lowerWff rho (.classMem A B) ⇔
        ∃'(lowerWff (bindRho rho x) (.classEq (.cv x) A) ⊓'
            lowerWff (bindRho rho x) (.classMem (.cv x) B))
  rw [hClassMem rho, hEqA rho, hMemB rho]
  exact rawDfClel (classPred rho A) (classPred rho B)


end NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011
