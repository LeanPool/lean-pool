/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart005

/-! NF weak partition development: WPPCompactSyntaxFVExplicitPart006. -/


public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/


theorem fv_syn_chnwcutmap (R : Class) (D : Class) :
    (synChnwcutmap R D).fv = (D.fv) ∪ (R.fv) :=
  by
  have fresh_p : freshVar (R.fv ∪ D.fv) 0 ∉ (R.fv ∪ D.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv) 0
  simp only [Finset.mem_union] at fresh_p
  ext u
  simp [synChnwcutmap, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutcode,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Class.fv];
  aesop

theorem fv_syn_chnqmap1 (A : Class) : (synChnqmap1 A).fv = A.fv :=
  by
  ext u
  simp [synChnqmap1, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso]

theorem fv_syn_clntp : (synClntp).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClntp]

theorem fv_syn_clntpc (A : Class) : (synClntpc A).fv = A.fv :=
  by
  ext u
  simp [synClntpc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwrels,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clntp]

theorem fv_syn_clnker (R : Class) : (synClnker R).fv = R.fv :=
  by
  ext u
  simp [synClnker]

theorem fv_syn_clnquo (R : Class) (A : Class) : (synClnquo R A).fv = (A.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synClnquo, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnker]

theorem fv_syn_cwpphit (F : Class) (I : Class) (C : Class) :
    (synCwpphit F I C).fv = (C.fv) ∪ (F.fv) ∪ (I.fv) :=
  by
  ext u
  simp [synCwpphit, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec]; aesop

theorem fv_syn_chnwsegfn (R : Class) (D : Class) :
    (synChnwsegfn R D).fv = (D.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synChnwsegfn]

theorem fv_syn_chnwcodefn (R : Class) : (synChnwcodefn R).fv = R.fv :=
  by
  ext u
  simp [synChnwcodefn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross]

theorem fv_syn_chnwcutfn (R : Class) (D : Class) :
    (synChnwcutfn R D).fv = (D.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synChnwcutfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcodefn,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwsegfn];
  aesop

theorem fv_syn_chnwcutrel (R : Class) (D : Class) :
    (synChnwcutrel R D).fv = (D.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synChnwcutrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutfn];
  aesop

theorem fv_syn_clnqrel (R : Class) : (synClnqrel R).fv = R.fv :=
  by
  have fresh_a : freshVar (R.fv) 0 ∉ (R.fv) := freshVar_not_mem (R.fv) 0
  have fresh_b : freshVar (R.fv) 1 ∉ (R.fv) := freshVar_not_mem (R.fv) 1
  have fresh_x : freshVar (R.fv) 2 ∉ (R.fv) := freshVar_not_mem (R.fv) 2
  have fresh_y : freshVar (R.fv) 3 ∉ (R.fv) := freshVar_not_mem (R.fv) 3
  have distinct_a_b : freshVar (R.fv) 0 ≠ freshVar (R.fv) 1 :=
    freshVar_injective (R.fv) (by decide)
  have distinct_a_x : freshVar (R.fv) 0 ≠ freshVar (R.fv) 2 :=
    freshVar_injective (R.fv) (by decide)
  have distinct_a_y : freshVar (R.fv) 0 ≠ freshVar (R.fv) 3 :=
    freshVar_injective (R.fv) (by decide)
  have distinct_b_x : freshVar (R.fv) 1 ≠ freshVar (R.fv) 2 :=
    freshVar_injective (R.fv) (by decide)
  have distinct_b_y : freshVar (R.fv) 1 ≠ freshVar (R.fv) 3 :=
    freshVar_injective (R.fv) (by decide)
  have distinct_x_y : freshVar (R.fv) 2 ≠ freshVar (R.fv) 3 :=
    freshVar_injective (R.fv) (by decide)
  ext u
  simp [synClnqrel, Class.fv]; aesop

theorem fv_syn_clnqord (R : Class) (C : Class) : (synClnqord R C).fv = (C.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synClnqord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnqrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnquo];
  aesop

theorem fv_syn_clnpwc (A : Class) : (synClnpwc A).fv = A.fv :=
  by
  have fresh_d : freshVar (A.fv) 0 ∉ (A.fv) := freshVar_not_mem (A.fv) 0
  have fresh_r : freshVar (A.fv) 1 ∉ (A.fv) := freshVar_not_mem (A.fv) 1
  have distinct_d_r : freshVar (A.fv) 0 ≠ freshVar (A.fv) 1 :=
    freshVar_injective (A.fv) (by decide)
  ext u
  simp [synClnpwc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clntpc, Class.fv];
  aesop

theorem fv_syn_cfrecteq (F : Class) (G : Class) (I : Class) :
    (synCfrecteq F G I).fv = (F.fv) ∪ (G.fv) ∪ (I.fv) :=
  by
  ext u
  simp [synCfrecteq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec]; aesop

theorem fv_syn_chnqinc (D : Class) (A : Class) : (synChnqinc D A).fv = (A.fv) ∪ (D.fv) :=
  by
  ext u
  simp [synChnqinc, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1]

theorem fv_syn_clndifop : (synClndifop).fv = (∅ : Finset Var) :=
  by
  have fresh_x : freshVar ((∅ : Finset Var)) 0 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 0
  have fresh_y : freshVar ((∅ : Finset Var)) 1 ∉ ((∅ : Finset Var)) :=
    freshVar_not_mem ((∅ : Finset Var)) 1
  have distinct_x_y : freshVar ((∅ : Finset Var)) 0 ≠ freshVar ((∅ : Finset Var)) 1 :=
    freshVar_injective ((∅ : Finset Var)) (by decide)
  ext u
  simp [synClndifop, Class.fv]; aesop

theorem fv_syn_clnpwasymfn : (synClnpwasymfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synClnpwasymfn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clndifop]

theorem fv_syn_cfdord (R : Class) (A : Class) (B : Class) :
    (synCfdord R A B).fv = (A.fv) ∪ (B.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCfdord, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfdif]; aesop

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
