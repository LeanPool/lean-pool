/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart009

/-! NF weak partition development: WPPCompactSyntaxFVExplicitPart010. -/


public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/


theorem fv_syn_chnsicodeliftfn : (synChnsicodeliftfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChnsicodeliftfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwpw1secondfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwsirelfn]

theorem fv_syn_chnsicodemap (A : Class) : (synChnsicodemap A).fv = A.fv :=
  by
  ext u
  simp [synChnsicodemap,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodeliftfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn]

theorem fv_syn_chnsiquomap (A : Class) : (synChnsiquomap A).fv = A.fv :=
  by
  ext u
  simp [synChnsiquomap, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap]

theorem fv_syn_chncodestrictfn : (synChncodestrictfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChncodestrictfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop]

theorem fv_syn_chncodepredfn : (synChncodepredfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChncodepredfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodestrictfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop]

theorem fv_syn_chncodecarrierfn : (synChncodecarrierfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChncodecarrierfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clninterop]

theorem fv_syn_chncodesquarefn : (synChncodesquarefn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChncodesquarefn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecarrierfn]

theorem fv_syn_chncoderelfn : (synChncoderelfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChncoderelfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodesquarefn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clninterop]

theorem fv_syn_chncodecutfn : (synChncodecutfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChncodecutfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecarrierfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncoderelfn]

theorem fv_syn_chncodecutpairfn : (synChncodecutpairfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synChncodecutpairfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutfn]

theorem fv_syn_chncodecutinputs (A : Class) : (synChncodecutinputs A).fv = A.fv :=
  by
  ext u
  simp [synChncodecutinputs, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn]

theorem fv_syn_chncodecutrel (A : Class) : (synChncodecutrel A).fv = A.fv :=
  by
  ext u
  simp [synChncodecutrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn]

theorem fv_syn_chncodecmpset (A : Class) : (synChncodecmpset A).fv = A.fv :=
  by
  ext u
  simp [synChncodecmpset,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso]

theorem fv_syn_chncodepredinputs (A : Class) (X : Class) (v : Var) :
    (synChncodepredinputs A X v).fv = (A.fv) ∪ (X.fv) ∪ (({ v } : Finset Var)) :=
  by
  ext u
  simp [synChncodepredinputs,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Class.fv]

theorem fv_syn_chncodepredends (A : Class) (X : Class) (v : Var) :
    (synChncodepredends A X v).fv = (A.fv) ∪ (X.fv) ∪ (({ v } : Finset Var)) :=
  by
  ext u
  simp [synChncodepredends,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredinputs]

theorem fv_syn_cwppstopact (F : Class) (C : Class) :
    (synCwppstopact F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwppstopact, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards];
  aesop

theorem fv_syn_cwppstopstep (F : Class) (C : Class) :
    (synCwppstopstep F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwppstopstep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopact];
  aesop

theorem fv_syn_cwppfreceq (F : Class) (G : Class) (I : Class) :
    (synCwppfreceq F G I).fv = (F.fv) ∪ (G.fv) ∪ (I.fv) :=
  by
  ext u
  simp [synCwppfreceq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec]; aesop

theorem fv_syn_cwppfrecprefixeq (F : Class) (G : Class) (I : Class) (k : Var) :
    (synCwppfrecprefixeq F G I k).fv =
      (F.fv) ∪ (G.fv) ∪ (I.fv) ∪ (({ k } : Finset Var)) :=
  by
  ext u
  simp [synCwppfrecprefixeq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfreceq, Class.fv]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
