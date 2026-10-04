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
    (synCfdrowrel R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCfdrowrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel]

theorem fv_syn_cfdrowfib (R : Class) (A : Class) (B : Class) (C : Class) :
    (synCfdrowfib R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) :=
  by
  have fresh_d : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union] at fresh_d
  ext u
  simp [synCfdrowfib, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowrel,
    Wff.fv, Class.fv];
  aesop

theorem fv_syn_cfdcodemap2 (R : Class) (A : Class) (B : Class) (C : Class) :
    (synCfdcodemap2 R A B C).fv = (A.fv) ∪ (B.fv) ∪ (C.fv) ∪ (R.fv) :=
  by
  have fresh_u : freshVar (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv ∪ C.fv) 0
  simp only [Finset.mem_union] at fresh_u
  ext u
  simp [synCfdcodemap2, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib,
    Class.fv];
  aesop

theorem fv_syn_cfdpointrel (A : Class) : (synCfdpointrel A).fv = A.fv :=
  by
  ext u
  simp [synCfdpointrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdmem,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel]

theorem fv_syn_cfdglobalrowmap (R : Class) (A : Class) (B : Class) :
    (synCfdglobalrowmap R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  have fresh_u : freshVar (R.fv ∪ A.fv ∪ B.fv) 0 ∉ (R.fv ∪ A.fv ∪ B.fv) :=
    freshVar_not_mem (R.fv ∪ A.fv ∪ B.fv) 0
  simp only [Finset.mem_union] at fresh_u
  ext u
  simp [synCfdglobalrowmap,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdrowfib, Class.fv];
  aesop

theorem fv_syn_cfdcolcodemap (R : Class) (A : Class) (B : Class) :
    (synCfdcolcodemap R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCfdcolcodemap,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdglobalrowmap,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdpointrel];
  aesop

theorem fv_syn_chwcodes (A : Class) : (synChwcodes A).fv = A.fv :=
  by
  ext u
  simp [synChwcodes]

theorem fv_syn_chwiso (A : Class) : (synChwiso A).fv = A.fv :=
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
  simp [synChwiso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso, Wff.fv, Class.fv];
  aesop

theorem fv_syn_chwrels : (synChwrels).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChwrels, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross]

theorem fv_syn_chwbij : (synChwbij).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChwbij]

theorem fv_syn_chwtrn : (synChwtrn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChwtrn]

theorem fv_syn_chwgen : (synChwgen).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChwgen, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cdomfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwtrn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cranfn]

theorem fv_syn_chwcn (A : Class) : (synChwcn A).fv = A.fv :=
  by
  ext u
  simp [synChwcn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcodes,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwrels]

theorem fv_syn_chwniso (A : Class) : (synChwniso A).fv = A.fv :=
  by
  ext u
  simp [synChwniso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen]

theorem fv_syn_chnord (A : Class) : (synChnord A).fv = A.fv :=
  by
  ext u
  simp [synChnord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso]

theorem fv_syn_chncard (A : Class) : (synChncard A).fv = A.fv :=
  by
  ext u
  simp [synChncard, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord]

theorem fv_syn_chwbases (A : Class) : (synChwbases A).fv = A.fv :=
  by
  ext u
  simp [synChwbases, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn]

theorem fv_syn_chwcards (A : Class) : (synChwcards A).fv = A.fv :=
  by
  ext u
  simp [synChwcards, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbases]

theorem fv_syn_chnwcutcode (R : Class) (D : Class) (C : Class) :
    (synChnwcutcode R D C).fv = (C.fv) ∪ (D.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synChnwcutcode]; aesop

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
