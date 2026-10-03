/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart006

/-! NF weak partition development: WPPCompactSyntaxFVExplicitPart007. -/


public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/


theorem fv_syn_ctcnn : (syn_ctcnn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_ctcnn]

theorem fv_syn_cpwpull (F : Class) (R : Class) : (syn_cpwpull F R).fv = (F.fv) ∪ (R.fv) :=
  by
  ext u
  simp [syn_cpwpull]; aesop

theorem fv_syn_clnpwkerfn : (syn_clnpwkerfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnpwkerfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwasymfn]

theorem fv_syn_clninterop : (syn_clninterop).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clninterop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop]

theorem fv_syn_clnimagecrossfn : (syn_clnimagecrossfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnimagecrossfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross]

theorem fv_syn_clnimageresfn : (syn_clnimageresfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimagecrossfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clninterop]

theorem fv_syn_clnimageop : (syn_clnimageop).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnimageop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cranfn]

theorem fv_syn_clnpwcnvkerfn : (syn_clnpwcnvkerfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnpwcnvkerfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwkerfn]

theorem fv_syn_clnpwclasspairfn : (syn_clnpwclasspairfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnpwclasspairfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwcnvkerfn]

theorem fv_syn_clnpwclassfn : (syn_clnpwclassfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnpwclassfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclasspairfn]

theorem fv_syn_clnpwpw1secondfn : (syn_clnpwpw1secondfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnpwpw1secondfn]

theorem fv_syn_clnpwquoinputfn : (syn_clnpwquoinputfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnpwquoinputfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwpw1secondfn]

theorem fv_syn_clnpwquofn : (syn_clnpwquofn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnpwquofn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn]

theorem fv_syn_clnpairraisefn : (syn_clnpairraisefn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnpairraisefn]

theorem fv_syn_clnsifn : (syn_clnsifn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnsifn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn]

theorem fv_syn_clnpwsirelfn : (syn_clnpwsirelfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_clnpwsirelfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnsifn]

theorem fv_syn_cwppreach (F : Class) (C : Class) :
    (syn_cwppreach F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwppreach, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec]; aesop

theorem fv_syn_cwppcand (F : Class) (C : Class) :
    (syn_cwppcand F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwppcand, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreach]

theorem fv_syn_cwpppredfam (F : Class) (C : Class) :
    (syn_cwpppredfam F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwpppredfam, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec]; aesop

theorem fv_syn_cwpppostcomp (F : Class) : (syn_cwpppostcomp F).fv = F.fv :=
  by
  ext u
  simp [syn_cwpppostcomp]

theorem fv_syn_cwppupperpreop (C : Class) : (syn_cwppupperpreop C).fv = C.fv :=
  by
  ext u
  simp [syn_cwppupperpreop,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop]

theorem fv_syn_cwpppowlayerseq (F : Class) (C : Class) :
    (syn_cwpppowlayerseq F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwpppowlayerseq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppupperpreop]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
