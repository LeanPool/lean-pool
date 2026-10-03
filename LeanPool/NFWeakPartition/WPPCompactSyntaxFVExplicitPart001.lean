/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.WPPCompactSourceSyntax
public import LeanPool.NFWeakPartition.CompactSyntaxFVDisable

/-! NF weak partition development: WPPCompactSyntaxFVExplicitPart001. -/


public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/


theorem fv_syn_wiso (H : Class) (R : Class) (S : Class) (A : Class) (B : Class) :
    (syn_wiso H R S A B).fv = (A.fv) ∪ (B.fv) ∪ (H.fv) ∪ (R.fv) ∪ (S.fv) :=
  by
  have fresh_x :
    freshVar (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 0 ∉ (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_x
  have fresh_y :
    freshVar (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 1 ∉ (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 1
  simp only [Finset.mem_union] at fresh_y
  have distinct_x_y :
    freshVar (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 0 ≠
      freshVar (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) 1 :=
    freshVar_injective (H.fv ∪ R.fv ∪ S.fv ∪ A.fv ∪ B.fv) (by decide)
  ext u
  simp [syn_wiso, Class.fv]; aesop

theorem fv_syn_cpprod (A : Class) (B : Class) : (syn_cpprod A B).fv = (A.fv) ∪ (B.fv) :=
  by
  ext u
  simp [syn_cpprod]

theorem fv_syn_ccross : (syn_ccross).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [syn_ccross, Class.fv]; aesop

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
