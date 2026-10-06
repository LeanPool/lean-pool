/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalDfClabStructuralDev005

/-! NF weak partition development: NominalDefinitionLeafHandlersCanonical001. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001

open NFChoice.Foundation
open NFChoice.SemanticCore

/-! One canonical import surface for the only three Metamath definition labels
that do not reduce to reflexivity after deep source expansion.
-/


/-- Proof-translation construction identified upstream as `dfClabStructural`. -/
@[expose]
noncomputable def dfClabStructural (x y : Var) (p : Wff) :
    NPrf (NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClabGoal x y p) :=
  NFChoice.DirectNominalPrf.Nominal.DfClabStructuralDev005.dfClabStructural x y p

/-- Proof-translation construction identified upstream as `dfCleqOfDV`. -/
@[expose]
noncomputable def dfCleqOfDV (x y z : Var) (A B : Class)
    (hAxExt : NPrf
        (.imp (.all x (Wff.biimp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z))))
          (.classEq (.cv y) (.cv z))))
    (hxA : x ∉ A.fv) (hxB : x ∉ B.fv) :
    NPrf (NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfCleqGoal x A B) :=
  NFChoice.DirectNominalPrf.Nominal.DefinitionLeafAdapterDev014.dfCleqOfDV x y z A B
    hAxExt hxA hxB

/-- Proof-translation construction identified upstream as `dfClelOfDV`. -/
@[expose]
noncomputable def dfClelOfDV (x : Var) (A B : Class) (hxA : x ∉ A.fv) (hxB : x ∉ B.fv) :
    NPrf (NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfClelGoal x A B) :=
  NFChoice.DirectNominalPrf.Nominal.DefinitionLeafAdapterDev014.dfClelOfDV x A B hxA hxB


end NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001
