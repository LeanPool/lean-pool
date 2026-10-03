/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.WPPCompactSyntaxFVExplicitPart007

/-! NF weak partition development: WPPCompactSyntaxFVExplicitPart008. -/


public section

namespace NFChoice.Compiler.WPPCompactSyntaxFVExplicit

open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-! Explicit-only FV equations for the WPP extension; no global simp attributes. -/


theorem fv_syn_cwpphitfam (F : Class) (C : Class) :
    (syn_cwpphitfam F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwpphitfam,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq]

theorem fv_syn_cwpppredmemrel (F : Class) (C : Class) :
    (syn_cwpppredmemrel F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwpppredmemrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppredfam]

theorem fv_syn_cwpphitmemrel (F : Class) (C : Class) :
    (syn_cwpphitmemrel F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwpphitmemrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphitfam]

theorem fv_syn_cwppreachincb (F : Class) (C : Class) :
    (syn_cwppreachincb F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwppreachincb,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphitmemrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppredmemrel]

theorem fv_syn_cwppimageat (D : Class) : (syn_cwppimageat D).fv = D.fv :=
  by
  ext u
  simp [syn_cwppimageat, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop]

theorem fv_syn_cwpppowateq (F : Class) (D : Class) :
    (syn_cwpppowateq F D).fv = (D.fv) ∪ (F.fv) :=
  by
  ext u
  simp [syn_cwpppowateq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppimageat,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp];
  aesop

theorem fv_syn_cwppprecomp (F : Class) : (syn_cwppprecomp F).fv = F.fv :=
  by
  ext u
  simp [syn_cwppprecomp]

theorem fv_syn_cwpppowcommeq (F : Class) : (syn_cwpppowcommeq F).fv = F.fv :=
  by
  ext u
  simp [syn_cwpppowcommeq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppprecomp]

theorem fv_syn_cwecutiso (R : Class) (D : Class) (S : Class) (E : Class) :
    (syn_cwecutiso R D S E).fv = (D.fv) ∪ (E.fv) ∪ (R.fv) ∪ (S.fv) :=
  by
  have fresh_f : freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 0 ∉ (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 0
  simp only [Finset.mem_union] at fresh_f
  have fresh_u : freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 1 ∉ (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 1
  simp only [Finset.mem_union] at fresh_u
  have fresh_x : freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 2 ∉ (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 2
  simp only [Finset.mem_union] at fresh_x
  have distinct_f_u :
    freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 0 ≠ freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 1 :=
    freshVar_injective (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) (by decide)
  have distinct_f_x :
    freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 0 ≠ freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 2 :=
    freshVar_injective (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) (by decide)
  have distinct_u_x :
    freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 1 ≠ freshVar (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) 2 :=
    freshVar_injective (R.fv ∪ D.fv ∪ S.fv ∪ E.fv) (by decide)
  ext u
  simp [syn_cwecutiso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
    Class.fv];
  aesop

theorem fv_syn_cwecutisogen (R : Class) (D : Class) (S : Class) (E : Class) :
    (syn_cwecutisogen R D S E).fv = (D.fv) ∪ (E.fv) ∪ (R.fv) ∪ (S.fv) :=
  by
  ext u
  simp [syn_cwecutisogen, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen];
  aesop

theorem fv_syn_cwecutcardfn (R : Class) (D : Class) :
    (syn_cwecutcardfn R D).fv = (D.fv) ∪ (R.fv) :=
  by
  have fresh_q : freshVar (R.fv ∪ D.fv) 0 ∉ (R.fv ∪ D.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv) 0
  simp only [Finset.mem_union] at fresh_q
  ext u
  simp [syn_cwecutcardfn, Class.fv]; aesop

theorem fv_syn_cwecutcardfactor (R : Class) (D : Class) :
    (syn_cwecutcardfactor R D).fv = (D.fv) ∪ (R.fv) :=
  by
  ext u
  simp [syn_cwecutcardfactor,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel]

theorem fv_syn_cwppgamma (F : Class) (C : Class) :
    (syn_cwppgamma F C).fv = (C.fv) ∪ (F.fv) :=
  by
  have fresh_k : freshVar (F.fv ∪ C.fv) 0 ∉ (F.fv ∪ C.fv) :=
    freshVar_not_mem (F.fv ∪ C.fv) 0
  simp only [Finset.mem_union] at fresh_k
  have fresh_m : freshVar (F.fv ∪ C.fv) 1 ∉ (F.fv ∪ C.fv) :=
    freshVar_not_mem (F.fv ∪ C.fv) 1
  simp only [Finset.mem_union] at fresh_m
  have distinct_k_m : freshVar (F.fv ∪ C.fv) 0 ≠ freshVar (F.fv ∪ C.fv) 1 :=
    freshVar_injective (F.fv ∪ C.fv) (by decide)
  ext u
  simp [syn_cwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
    Wff.fv, Class.fv];
  aesop

theorem fv_syn_cwppcardtfn : (syn_cwppcardtfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppcardtfn]

theorem fv_syn_cwppcardt2fn : (syn_cwppcardt2fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [syn_cwppcardt2fn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardtfn]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
