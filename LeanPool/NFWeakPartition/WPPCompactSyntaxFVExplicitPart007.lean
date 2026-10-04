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


theorem fv_syn_ctcnn : (synCtcnn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCtcnn]

theorem fv_syn_cpwpull (F : Class) (R : Class) : (synCpwpull F R).fv = (F.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCpwpull]; aesop

theorem fv_syn_clnpwkerfn : (synClnpwkerfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnpwkerfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwasymfn]

theorem fv_syn_clninterop : (synClninterop).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClninterop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop]

theorem fv_syn_clnimagecrossfn : (synClnimagecrossfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnimagecrossfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross]

theorem fv_syn_clnimageresfn : (synClnimageresfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimagecrossfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clninterop]

theorem fv_syn_clnimageop : (synClnimageop).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnimageop, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageresfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cranfn]

theorem fv_syn_clnpwcnvkerfn : (synClnpwcnvkerfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnpwcnvkerfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwkerfn]

theorem fv_syn_clnpwclasspairfn : (synClnpwclasspairfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnpwclasspairfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwcnvkerfn]

theorem fv_syn_clnpwclassfn : (synClnpwclassfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnpwclassfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclasspairfn]

theorem fv_syn_clnpwpw1secondfn : (synClnpwpw1secondfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnpwpw1secondfn]

theorem fv_syn_clnpwquoinputfn : (synClnpwquoinputfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnpwquoinputfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwpw1secondfn]

theorem fv_syn_clnpwquofn : (synClnpwquofn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnpwquofn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwclassfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn]

theorem fv_syn_clnpairraisefn : (synClnpairraisefn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnpairraisefn]

theorem fv_syn_clnsifn : (synClnsifn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnsifn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpairraisefn]

theorem fv_syn_clnpwsirelfn : (synClnpwsirelfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnpwsirelfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnsifn]

theorem fv_syn_cwppreach (F : Class) (C : Class) :
    (synCwppreach F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwppreach, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec]; aesop

theorem fv_syn_cwppcand (F : Class) (C : Class) :
    (synCwppcand F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwppcand, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppreach]

theorem fv_syn_cwpppredfam (F : Class) (C : Class) :
    (synCwpppredfam F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwpppredfam, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec]; aesop

theorem fv_syn_cwpppostcomp (F : Class) : (synCwpppostcomp F).fv = F.fv :=
  by
  ext u
  simp [synCwpppostcomp]

theorem fv_syn_cwppupperpreop (C : Class) : (synCwppupperpreop C).fv = C.fv :=
  by
  ext u
  simp [synCwppupperpreop,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop]

theorem fv_syn_cwpppowlayerseq (F : Class) (C : Class) :
    (synCwpppowlayerseq F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwpppowlayerseq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppupperpreop]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
