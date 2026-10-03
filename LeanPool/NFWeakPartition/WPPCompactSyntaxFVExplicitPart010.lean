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


theorem fv_syn_chnsicodeliftfn : (syn_chnsicodeliftfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chnsicodeliftfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwpw1secondfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwsirelfn]

theorem fv_syn_chnsicodemap (A : Class) : (syn_chnsicodemap A).fv = A.fv :=
  by
  ext u
  simp [syn_chnsicodemap,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodeliftfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn]

theorem fv_syn_chnsiquomap (A : Class) : (syn_chnsiquomap A).fv = A.fv :=
  by
  ext u
  simp [syn_chnsiquomap, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnsicodemap]

theorem fv_syn_chncodestrictfn : (syn_chncodestrictfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chncodestrictfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop]

theorem fv_syn_chncodepredfn : (syn_chncodepredfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chncodepredfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodestrictfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop]

theorem fv_syn_chncodecarrierfn : (syn_chncodecarrierfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chncodecarrierfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clninterop]

theorem fv_syn_chncodesquarefn : (syn_chncodesquarefn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chncodesquarefn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecarrierfn]

theorem fv_syn_chncoderelfn : (syn_chncoderelfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chncoderelfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodesquarefn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clninterop]

theorem fv_syn_chncodecutfn : (syn_chncodecutfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chncodecutfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecarrierfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncoderelfn]

theorem fv_syn_chncodecutpairfn : (syn_chncodecutpairfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_chncodecutpairfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutfn]

theorem fv_syn_chncodecutinputs (A : Class) : (syn_chncodecutinputs A).fv = A.fv :=
  by
  ext u
  simp [syn_chncodecutinputs, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnpwquoinputfn]

theorem fv_syn_chncodecutrel (A : Class) : (syn_chncodecutrel A).fv = A.fv :=
  by
  ext u
  simp [syn_chncodecutrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutinputs,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutpairfn]

theorem fv_syn_chncodecmpset (A : Class) : (syn_chncodecmpset A).fv = A.fv :=
  by
  ext u
  simp [syn_chncodecmpset,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso]

theorem fv_syn_chncodepredinputs (A : Class) (X : Class) (v : Var) :
    (syn_chncodepredinputs A X v).fv = (A.fv) ∪ (X.fv) ∪ (({ v } : Finset Var)) :=
  by
  ext u
  simp [syn_chncodepredinputs,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodecutfn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Class.fv]

theorem fv_syn_chncodepredends (A : Class) (X : Class) (v : Var) :
    (syn_chncodepredends A X v).fv = (A.fv) ∪ (X.fv) ∪ (({ v } : Finset Var)) :=
  by
  ext u
  simp [syn_chncodepredends,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodepredinputs]

theorem fv_syn_cwppstopact (F : Class) (C : Class) :
    (syn_cwppstopact F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwppstopact, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards];
  aesop

theorem fv_syn_cwppstopstep (F : Class) (C : Class) :
    (syn_cwppstopstep F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwppstopstep, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopact];
  aesop

theorem fv_syn_cwppfreceq (F : Class) (G : Class) (I : Class) :
    (syn_cwppfreceq F G I).fv = (F.fv) ∪ (G.fv) ∪ (I.fv) :=
  by
  ext u
  simp [syn_cwppfreceq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec]; aesop

theorem fv_syn_cwppfrecprefixeq (F : Class) (G : Class) (I : Class) (k : Var) :
    (syn_cwppfrecprefixeq F G I k).fv =
      (F.fv) ∪ (G.fv) ∪ (I.fv) ∪ (({ k } : Finset Var)) :=
  by
  ext u
  simp [syn_cwppfrecprefixeq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ckqrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppfreceq, Class.fv]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
