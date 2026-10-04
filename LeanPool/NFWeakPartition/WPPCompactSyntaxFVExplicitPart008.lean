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
    (synCwpphitfam F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwpphitfam,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppowlayerseq]

theorem fv_syn_cwpppredmemrel (F : Class) (C : Class) :
    (synCwpppredmemrel F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwpppredmemrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppredfam]

theorem fv_syn_cwpphitmemrel (F : Class) (C : Class) :
    (synCwpphitmemrel F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwpphitmemrel, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphitfam]

theorem fv_syn_cwppreachincb (F : Class) (C : Class) :
    (synCwppreachincb F C).fv = (C.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwppreachincb,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphitmemrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppredmemrel]

theorem fv_syn_cwppimageat (D : Class) : (synCwppimageat D).fv = D.fv :=
  by
  ext u
  simp [synCwppimageat, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_clnimageop]

theorem fv_syn_cwpppowateq (F : Class) (D : Class) :
    (synCwpppowateq F D).fv = (D.fv) ∪ (F.fv) :=
  by
  ext u
  simp [synCwpppowateq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppimageat,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp];
  aesop

theorem fv_syn_cwppprecomp (F : Class) : (synCwppprecomp F).fv = F.fv :=
  by
  ext u
  simp [synCwppprecomp]

theorem fv_syn_cwpppowcommeq (F : Class) : (synCwpppowcommeq F).fv = F.fv :=
  by
  ext u
  simp [synCwpppowcommeq, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpppostcomp,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppprecomp]

theorem fv_syn_cwecutiso (R : Class) (D : Class) (S : Class) (E : Class) :
    (synCwecutiso R D S E).fv = (D.fv) ∪ (E.fv) ∪ (R.fv) ∪ (S.fv) :=
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
  simp [synCwecutiso, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_wiso,
    Class.fv];
  aesop

theorem fv_syn_cwecutisogen (R : Class) (D : Class) (S : Class) (E : Class) :
    (synCwecutisogen R D S E).fv = (D.fv) ∪ (E.fv) ∪ (R.fv) ∪ (S.fv) :=
  by
  ext u
  simp [synCwecutisogen, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen];
  aesop

theorem fv_syn_cwecutcardfn (R : Class) (D : Class) :
    (synCwecutcardfn R D).fv = (D.fv) ∪ (R.fv) :=
  by
  have fresh_q : freshVar (R.fv ∪ D.fv) 0 ∉ (R.fv ∪ D.fv) :=
    freshVar_not_mem (R.fv ∪ D.fv) 0
  simp only [Finset.mem_union] at fresh_q
  ext u
  simp [synCwecutcardfn, Class.fv]; aesop

theorem fv_syn_cwecutcardfactor (R : Class) (D : Class) :
    (synCwecutcardfactor R D).fv = (D.fv) ∪ (R.fv) :=
  by
  ext u
  simp [synCwecutcardfactor,
    NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnwcutrel]

theorem fv_syn_cwppgamma (F : Class) (C : Class) :
    (synCwppgamma F C).fv = (C.fv) ∪ (F.fv) :=
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
  simp [synCwppgamma, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
    Wff.fv, Class.fv];
  aesop

theorem fv_syn_cwppcardtfn : (synCwppcardtfn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppcardtfn]

theorem fv_syn_cwppcardt2fn : (synCwppcardt2fn).fv = (∅ : Finset Var) :=
  by
  ext u
  simp [synCwppcardt2fn, NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardtfn]

end NFChoice.Compiler.WPPCompactSyntaxFVExplicit
