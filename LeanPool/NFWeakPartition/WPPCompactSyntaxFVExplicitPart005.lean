/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart004

/-! NF weak partition development: WPPCompactSyntaxFVExplicitPart005. -/


public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/


theorem fv_syn_cfdrowrel (R : Class) (A : Class) (B : Class) :
    (syn_cfdrowrel R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [syn_cfdrowrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel]

theorem fv_syn_cfdrowfib (R : Class) (A : Class) (B : Class) (C : Class) :
    (syn_cfdrowfib R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) :=
  by
  have fresh_d : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union] at fresh_d
  ext u
  simp [syn_cfdrowfib, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel,
    Wff.fv, Class.fv];
  aesop

theorem fv_syn_cfdcodemap2 (R : Class) (A : Class) (B : Class) (C : Class) :
    (syn_cfdcodemap2 R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) :=
  by
  have fresh_u : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union] at fresh_u
  ext u
  simp [syn_cfdcodemap2, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib,
    Class.fv];
  aesop

theorem fv_syn_cfdpointrel (A : Class) : (syn_cfdpointrel A).fv = A.fv :=
  by
  ext u
  simp [syn_cfdpointrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel]

theorem fv_syn_cfdglobalrowmap (R : Class) (A : Class) (B : Class) :
    (syn_cfdglobalrowmap R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  have fresh_u : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_u
  ext u
  simp [syn_cfdglobalrowmap,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, Class.fv];
  aesop

theorem fv_syn_cfdcolcodemap (R : Class) (A : Class) (B : Class) :
    (syn_cfdcolcodemap R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [syn_cfdcolcodemap,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdglobalrowmap,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel];
  aesop

theorem fv_syn_chwcodes (A : Class) : (syn_chwcodes A).fv = A.fv :=
  by
  ext u
  simp [syn_chwcodes]

theorem fv_syn_chwiso (A : Class) : (syn_chwiso A).fv = A.fv :=
  by
  have fresh_h : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_u : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have fresh_v : freshVar (A.fv) 2 ∉ (A.fv) := freshVar_not_mem (A.fv) 2
  have distinct_h_u : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_h_v : freshVar (A.fv) 0 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  have distinct_u_v : freshVar (A.fv) 1 ≠ freshVar (A.fv) 2 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [syn_chwiso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, Wff.fv, Class.fv];
  aesop

theorem fv_syn_chwrels : (syn_chwrels).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chwrels, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross]

theorem fv_syn_chwbij : (syn_chwbij).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chwbij]

theorem fv_syn_chwtrn : (syn_chwtrn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chwtrn]

theorem fv_syn_chwgen : (syn_chwgen).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chwgen, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cdomfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwtrn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cranfn]

theorem fv_syn_chwcn (A : Class) : (syn_chwcn A).fv = A.fv :=
  by
  ext u
  simp [syn_chwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwrels]

theorem fv_syn_chwniso (A : Class) : (syn_chwniso A).fv = A.fv :=
  by
  ext u
  simp [syn_chwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen]

theorem fv_syn_chnord (A : Class) : (syn_chnord A).fv = A.fv :=
  by
  ext u
  simp [syn_chnord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso]

theorem fv_syn_chncard (A : Class) : (syn_chncard A).fv = A.fv :=
  by
  ext u
  simp [syn_chncard, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord]

theorem fv_syn_chwbases (A : Class) : (syn_chwbases A).fv = A.fv :=
  by
  ext u
  simp [syn_chwbases, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn]

theorem fv_syn_chwcards (A : Class) : (syn_chwcards A).fv = A.fv :=
  by
  ext u
  simp [syn_chwcards, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbases]

theorem fv_syn_chnwcutcode (R : Class) (D : Class) (C : Class) :
    (syn_chnwcutcode R D C).fv = (C.fv) ∪ (D.fv) ∪ (R.fv) :=
  by
  ext u
  simp [syn_chnwcutcode]; aesop

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
