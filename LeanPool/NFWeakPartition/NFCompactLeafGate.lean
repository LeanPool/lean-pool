/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NFLeafWrappers.Basic
public import LeanPool.NFWeakPartition.CompactSyntaxFVDisable

/-! NF weak partition development: NFCompactLeafGate. -/


public section

namespace NFChoice.Compiler.NFCompactLeafGate

open scoped Fol
open NFChoice.Foundation
open NFChoice.Foundation.ExactLiteralTrial
open NFChoice.SemanticCore
open NFChoice.SemanticCore.PartialLowering
open NFChoice.Compiler.CompactSourceSyntax
open NFChoice.Compiler.CompactSyntaxFVExplicit

theorem axNinCompact {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Wff.Valid S
      (synWex z (.all w (synWb (.objMem w z) (synWnan (.objMem w x) (.objMem w y))))) :=
  by
  apply
    NFChoice.NFLeafWrappers.source_ax_nin hNF x y z w hxy hxz hxw hyz hyw hzw
      (synWex z (.all w (synWb (.objMem w z) (synWnan (.objMem w x) (.objMem w y)))))
  · intro a ha
    simp only [fv_syn_wex, fv_syn_wb, fv_syn_wnan, Wff.fv, Finset.mem_erase,
      Finset.mem_union, ] at ha
    simp_all; aesop
  · simp [synWex, synWb, synWnan, synWa, closeNames, lowerClosed, lowerWffOption, bindRhoOption,
      liftRhoOption, Function.update, hxy, hxz, hxw, hyz, hyw, hzw, Wff.neg, Formula.ex,
      Formula.biimp, Formula.conj, Formula.neg, literalAxNin]

theorem axSnCompact {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (hyz : y ≠ z) :
    Wff.Valid S (synWex y (.all z (synWb (.objMem z y) (.objEq z x)))) :=
  by
  apply
    NFChoice.NFLeafWrappers.source_ax_sn hNF x y z hxy hxz hyz
      (synWex y (.all z (synWb (.objMem z y) (.objEq z x))))
  · intro a ha
    simp only [fv_syn_wex, fv_syn_wb, Wff.fv, Finset.mem_erase, Finset.mem_union] at ha
    simp_all; aesop
  · simp [synWex, synWb, closeNames, lowerClosed, lowerWffOption, bindRhoOption, liftRhoOption,
      Function.update, hxy, hxz, hyz, Wff.neg, Formula.ex, Formula.biimp, Formula.conj,
      Formula.neg, literalAxSn]

theorem ax1cCompact {S : Fol.Structure LNF}
    (hNF : Fol.allRealizeSentence S LiteralHailperinNF) (x y z w : Var) (hxy : x ≠ y)
    (hxz : x ≠ z) (hxw : x ≠ w) (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
    Wff.Valid S
      (synWex x (.all y (synWb (.objMem y x)
            (synWex z (.all w (synWb (.objMem w y) (.objEq w z))))))) :=
  by
  apply
    NFChoice.NFLeafWrappers.source_ax_1c hNF x y z w hxy hxz hxw hyz hyw hzw
      (synWex x (.all y (synWb (.objMem y x)
            (synWex z (.all w (synWb (.objMem w y) (.objEq w z)))))))
  · intro a ha
    simp only [fv_syn_wex, fv_syn_wb, Wff.fv, Finset.mem_erase, Finset.mem_union] at ha
    simp_all; aesop
  · simp [synWex, synWb, closeNames, lowerClosed, lowerWffOption, bindRhoOption, liftRhoOption,
      Function.update, hxy, hyz, hyw, hzw, Wff.neg, Formula.ex, Formula.biimp,
      Formula.conj, Formula.neg, Formula.isSomeSingleton, Formula.singleton, literalAx1c]


end NFChoice.Compiler.NFCompactLeafGate
