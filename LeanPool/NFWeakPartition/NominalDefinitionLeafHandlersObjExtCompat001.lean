/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalNFLiteralHandlers
public import LeanPool.NFWeakPartition.NominalDefinitionLeafHandlersCanonical001
public import LeanPool.NFWeakPartition.NominalRecanonTransportDev

/-! NF weak partition development: NominalDefinitionLeafHandlersObjExtCompat001. -/


public section

namespace NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersObjExtCompat001

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.Compiler.CompactSourceSyntax

/-! `ax-ext` is replayed in the primitive object-language presentation, while
`df-cleq`'s historical exporter-facing adapter expected the definitionally
expanded class-language presentation.  The variable permutation in the
replay is already the right one: `axExtGoal y z x` binds `x` and compares
membership in `y` and `z`.

This type-valued certificate records only the object-to-class atomic
recanonicalization.  It introduces no logical assumption.
-/

@[expose]
def axExtObjClassRecanon (x y z : Var) :
    RecanonTransportDev.TRecanonWff (NFLiteralHandlers.axExtGoal y z x)
      (.imp (.all x (Wff.biimp (.classMem (.cv x) (.cv y)) (.classMem (.cv x) (.cv z))))
        (.classEq (.cv y) (.cv z))) :=
  by
  unfold NFLiteralHandlers.axExtGoal syn_wb Wff.biimp Wff.conj Wff.neg
  apply RecanonTransportDev.TRecanonWff.imp
  · apply RecanonTransportDev.TRecanonWff.all
    apply RecanonTransportDev.TRecanonWff.imp
    · apply RecanonTransportDev.TRecanonWff.imp
      · apply RecanonTransportDev.TRecanonWff.imp
        · exact RecanonTransportDev.TRecanonWff.objMem_classMem _ _
        · exact RecanonTransportDev.TRecanonWff.objMem_classMem _ _
      · apply RecanonTransportDev.TRecanonWff.imp
        · apply RecanonTransportDev.TRecanonWff.imp
          · exact RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · exact RecanonTransportDev.TRecanonWff.objMem_classMem _ _
        · exact RecanonTransportDev.TRecanonWff.same _
    · exact RecanonTransportDev.TRecanonWff.same _
  · exact RecanonTransportDev.TRecanonWff.objEq_classEq _ _

/-! Exact source-signature adapter for the generated `df-cleq` call.  Unlike the
older `dfCleqOfDV`, this accepts the object-language `axExtGoal y z x` proof
that the literal-axiom handler actually produces, transports it through the
explicit certificate above, and then calls the already-audited class handler.
-/

@[expose]
noncomputable def dfCleqOfDVObjExt (x y z : Var) (A B : Class)
    (hAxExt : NPrf (NFLiteralHandlers.axExtGoal y z x)) (hxA : x ∉ A.fv)
    (hxB : x ∉ B.fv) :
    NPrf (NFChoice.DirectNominalPrf.Nominal.ClassHandlersDev011.dfCleqGoal x A B) :=
  DefinitionLeafHandlersCanonical001.dfCleqOfDV x y z A B
    (RecanonTransportDev.transport (axExtObjClassRecanon x y z) hAxExt) hxA hxB


end NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersObjExtCompat001
