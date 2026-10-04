/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk016Compact001Part043`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppcandleastreundv`. -/
@[expose]
noncomputable def gWppcandleastreundv (ph : Wff) (C : Class) (k : Var) (m : Var)
    (F : Class) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv)
    (dv_F_m : m ∉ F.fv) (dv_k_m : k ≠ m) (_dv_k_ph : k ∉ ph.fv) (_dv_m_ph : m ∉ ph.fv)
    (hyp_wppcandleastreundv_1 : Nominal.NPrf (.imp ph (synWrex m (synCwppcand F C)
            (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))))) :
    Nominal.NPrf
      (.imp ph (synWreu m (synCwppcand F C)
          (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))))) :=
  by
  let proofSupport : Finset Var :=
    ph.fv ∪ C.fv ∪ ({ k } : Finset Var) ∪ ({ m } : Finset Var) ∪ F.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_ne_k : n ≠ k := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_k_ne_n : k ≠ n := Ne.symm fresh_n_ne_k
  have fresh_n_ne_m : n ≠ m := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ ((Class.cv n)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_k_ne_n, not_false_eq_true])
  have dv_cache_0002 : k ∉ ((synCwppcand F C)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_k, dv_F_k, or_false, not_false_eq_true])
  have dv_cache_0003 : k ∉ ((synWbr (.cv m) (synClec) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, dv_k_m, fresh_k_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : k ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_k_m,
          not_false_eq_true])
  have dv_cache_0005 : k ∉ ((synWbr (.cv n) (synClec) (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_k_ne_n, dv_k_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 : n ∉ ((synCwppcand F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, fresh_n_not_C, fresh_n_not_F, or_false, not_false_eq_true])
  have dv_cache_0007 : m ∉ (synWtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : n ∉ (synWtru).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show m ≠ n from (by exact fresh_m_ne_n))
  have dv_cache_0010 : k ∉ ((Wff.classEq (.cv m) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_k_m, fresh_k_ne_n, or_false, not_false_eq_true])
  have dv_cache_0011 : m ∉ ((synCwppcand F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_m, dv_F_m, or_false, not_false_eq_true])
  have dv_cache_0012 :
    n ∉ ((synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_not_C, fresh_n_not_F,
          fresh_n_ne_m, fresh_n_ne_k, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0013 :
    m ∉ ((synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_C_m, dv_F_m, fresh_m_ne_n,
          (Ne.symm dv_k_m), compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gTru
  have p0001 :=
    @gSimpr
      (synWa (.classMem (.cv m) (synCwppcand F C)) (.classMem (.cv n) (synCwppcand F C)))
      (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
        (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
  have p0002 :=
    @gSimpl (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
      (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))
  have p0003 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
        (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
      (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))) p0001 p0002
  have p0004 :=
    @gSimpl
      (synWa (.classMem (.cv m) (synCwppcand F C)) (.classMem (.cv n) (synCwppcand F C)))
      (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
        (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
  have p0005 :=
    @gSimpr (.classMem (.cv m) (synCwppcand F C)) (.classMem (.cv n) (synCwppcand F C))
  have p0006 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWa (.classMem (.cv m) (synCwppcand F C)) (.classMem (.cv n) (synCwppcand F C)))
      (.classMem (.cv n) (synCwppcand F C)) p0004 p0005
  have p0007 := @gId (.classEq (.cv k) (.cv n))
  have p0008 :=
    @gBreq2d (.classEq (.cv k) (.cv n)) (.cv k) (.cv n) (.cv m) (synClec) p0007
  have p0009 :=
    @gRspcv (synWbr (.cv m) (synClec) (.cv k)) (synWbr (.cv m) (synClec) (.cv n)) k
      (.cv n) (synCwppcand F C) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0008
  have p0010 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (.classMem (.cv n) (synCwppcand F C))
      (.imp (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
        (synWbr (.cv m) (synClec) (.cv n)))
      p0006 p0009
  have p0011 :=
    @gMpd
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
      (synWbr (.cv m) (synClec) (.cv n)) p0003 p0010
  have p0013 :=
    @gSimpr (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
      (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))
  have p0014 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
        (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
      (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))) p0001 p0013
  have p0016 :=
    @gSimpl (.classMem (.cv m) (synCwppcand F C)) (.classMem (.cv n) (synCwppcand F C))
  have p0017 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWa (.classMem (.cv m) (synCwppcand F C)) (.classMem (.cv n) (synCwppcand F C)))
      (.classMem (.cv m) (synCwppcand F C)) p0004 p0016
  have p0018 := @gId (.classEq (.cv k) (.cv m))
  have p0019 :=
    @gBreq2d (.classEq (.cv k) (.cv m)) (.cv k) (.cv m) (.cv n) (synClec) p0018
  have p0020 :=
    @gRspcv (synWbr (.cv n) (synClec) (.cv k)) (synWbr (.cv n) (synClec) (.cv m)) k
      (.cv m) (synCwppcand F C) dv_cache_0004 dv_cache_0002 dv_cache_0005 p0019
  have p0021 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (.classMem (.cv m) (synCwppcand F C))
      (.imp (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))
        (synWbr (.cv n) (synClec) (.cv m)))
      p0017 p0020
  have p0022 :=
    @gMpd
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))
      (synWbr (.cv n) (synClec) (.cv m)) p0014 p0021
  have p0023 :=
    @gJca
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWbr (.cv m) (synClec) (.cv n)) (synWbr (.cv n) (synClec) (.cv m)) p0011
      p0022
  have p0027 := @gElwppcand C (.cv m) F
  have p0028 :=
    @gBiimpi (.classMem (.cv m) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv m) (synChwcards (synCvv)))
          (synWbr (.cv m) (synClec) C)) (.classMem (.cv m) (synCwppreach F C)))
      p0027
  have p0029 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (.classMem (.cv m) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv m) (synChwcards (synCvv)))
          (synWbr (.cv m) (synClec) C)) (.classMem (.cv m) (synCwppreach F C)))
      p0017 p0028
  have p0030 :=
    @gSimpl
      (synWa (.classMem (.cv m) (synChwcards (synCvv))) (synWbr (.cv m) (synClec) C))
      (.classMem (.cv m) (synCwppreach F C))
  have p0031 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWa (synWa (.classMem (.cv m) (synChwcards (synCvv)))
          (synWbr (.cv m) (synClec) C)) (.classMem (.cv m) (synCwppreach F C)))
      (synWa (.classMem (.cv m) (synChwcards (synCvv))) (synWbr (.cv m) (synClec) C))
      p0029 p0030
  have p0032 :=
    @gSimpl (.classMem (.cv m) (synChwcards (synCvv))) (synWbr (.cv m) (synClec) C)
  have p0033 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWa (.classMem (.cv m) (synChwcards (synCvv))) (synWbr (.cv m) (synClec) C))
      (.classMem (.cv m) (synChwcards (synCvv))) p0031 p0032
  have p0037 := @gElwppcand C (.cv n) F
  have p0038 :=
    @gBiimpi (.classMem (.cv n) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv n) (synChwcards (synCvv)))
          (synWbr (.cv n) (synClec) C)) (.classMem (.cv n) (synCwppreach F C)))
      p0037
  have p0039 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (.classMem (.cv n) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv n) (synChwcards (synCvv)))
          (synWbr (.cv n) (synClec) C)) (.classMem (.cv n) (synCwppreach F C)))
      p0006 p0038
  have p0040 :=
    @gSimpl
      (synWa (.classMem (.cv n) (synChwcards (synCvv))) (synWbr (.cv n) (synClec) C))
      (.classMem (.cv n) (synCwppreach F C))
  have p0041 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWa (synWa (.classMem (.cv n) (synChwcards (synCvv)))
          (synWbr (.cv n) (synClec) C)) (.classMem (.cv n) (synCwppreach F C)))
      (synWa (.classMem (.cv n) (synChwcards (synCvv))) (synWbr (.cv n) (synClec) C))
      p0039 p0040
  have p0042 :=
    @gSimpl (.classMem (.cv n) (synChwcards (synCvv))) (synWbr (.cv n) (synClec) C)
  have p0043 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWa (.classMem (.cv n) (synChwcards (synCvv))) (synWbr (.cv n) (synClec) C))
      (.classMem (.cv n) (synChwcards (synCvv))) p0041 p0042
  have p0044 :=
    @gJca
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (.classMem (.cv m) (synChwcards (synCvv)))
      (.classMem (.cv n) (synChwcards (synCvv))) p0033 p0043
  have p0045 := @gHwcardslecanti m n
  have p0046 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWa (.classMem (.cv m) (synChwcards (synCvv)))
        (.classMem (.cv n) (synChwcards (synCvv))))
      (.imp (synWa (synWbr (.cv m) (synClec) (.cv n)) (synWbr (.cv n) (synClec) (.cv m)))
        (.classEq (.cv m) (.cv n)))
      p0044 p0045
  have p0047 :=
    @gMpd
      (synWa (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C)))
        (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k)))))
      (synWa (synWbr (.cv m) (synClec) (.cv n)) (synWbr (.cv n) (synClec) (.cv m)))
      (.classEq (.cv m) (.cv n)) p0023 p0046
  have p0048 :=
    @gEx
      (synWa (.classMem (.cv m) (synCwppcand F C)) (.classMem (.cv n) (synCwppcand F C)))
      (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
        (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
      (.classEq (.cv m) (.cv n)) p0047
  have p0049 :=
    @gA1i
      (.imp (synWa (.classMem (.cv m) (synCwppcand F C))
          (.classMem (.cv n) (synCwppcand F C))) (.imp
          (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
            (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
          (.classEq (.cv m) (.cv n))))
      synWtru p0048
  have p0050 :=
    @gRalrimivv synWtru
      (.imp (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
        (.classEq (.cv m) (.cv n)))
      m n (synCwppcand F C) (synCwppcand F C) dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0049
  have p0051 := Nominal.mp p0000 p0050
  have p0052 :=
    @gA1i
      (synWral m (synCwppcand F C) (synWral n (synCwppcand F C) (.imp
            (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
              (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
            (.classEq (.cv m) (.cv n)))))
      ph p0051
  have p0053 :=
    @gJca ph
      (synWrex m (synCwppcand F C)
        (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))))
      (synWral m (synCwppcand F C) (synWral n (synCwppcand F C) (.imp
            (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
              (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
            (.classEq (.cv m) (.cv n)))))
      hyp_wppcandleastreundv_1 p0052
  have p0054 := @gId (.classEq (.cv m) (.cv n))
  have p0055 :=
    @gBreq1d (.classEq (.cv m) (.cv n)) (.cv m) (.cv n) (.cv k) (synClec) p0054
  have p0056 :=
    @gRalbidv (.classEq (.cv m) (.cv n)) (synWbr (.cv m) (synClec) (.cv k))
      (synWbr (.cv n) (synClec) (.cv k)) k (synCwppcand F C) dv_cache_0010 p0055
  have p0057_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m n)
        (synWb (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
          (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWral synCwppcand synCin synCcompl synCnin synWnan synWa
          synCwppreach synCuni synWex synCrn synCima synWrex synWbr synCop synCun
          synCvv synCfrec synCclos1 synCint synCsn synCpprod synCtxp synCcom
          synCopab synC1st synCmpt synCplc synC1c synCimage synCcnv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0056
  have p0057 :=
    @gReu4 (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
      (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))) m n
      (synCwppcand F C) dv_cache_0011 dv_cache_0006 dv_cache_0012 dv_cache_0013
      dv_cache_0009 p0057_e00_recanon
  have p0058_e00_recanon :
    Nominal.NPrf
      (synWb (synWreu m (synCwppcand F C)
          (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))) (synWa
          (synWrex m (synCwppcand F C)
            (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))))
          (synWral m (synCwppcand F C) (synWral n (synCwppcand F C) (.imp (synWa
                  (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
                  (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
                (.classEq (.cv m) (.cv n))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWreu synWeu synWex synWa synCwppcand synCin synCcompl
          synCnin synWnan synCwppreach synCuni synCrn synCima synWrex synWbr
          synCop synCun synCvv synCfrec synCclos1 synCint synCsn synCpprod
          synCtxp synCcom synCopab synC1st synCmpt synCplc synC1c synCimage
          synCcnv synWral
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0057
  have p0058 :=
    @gBiimpri
      (synWreu m (synCwppcand F C)
        (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))))
      (synWa (synWrex m (synCwppcand F C)
          (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))))
        (synWral m (synCwppcand F C) (synWral n (synCwppcand F C) (.imp
              (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
                (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
              (.classEq (.cv m) (.cv n))))))
      p0058_e00_recanon
  have p0059 :=
    @gSyl ph
      (synWa (synWrex m (synCwppcand F C)
          (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))))
        (synWral m (synCwppcand F C) (synWral n (synCwppcand F C) (.imp
              (synWa (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
                (synWral k (synCwppcand F C) (synWbr (.cv n) (synClec) (.cv k))))
              (.classEq (.cv m) (.cv n))))))
      (synWreu m (synCwppcand F C)
        (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))))
      p0053 p0058
  exact p0059

/-- Checked nominal proof certificate identified upstream as `g_wppgammaminpackndv`. -/
@[expose]
noncomputable def gWppgammaminpackndv (ph : Wff) (C : Class) (k : Var) (m : Var)
    (F : Class) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv)
    (dv_F_m : m ∉ F.fv) (dv_k_m : k ≠ m) (dv_k_ph : k ∉ ph.fv) (dv_m_ph : m ∉ ph.fv)
    (hyp_wppgammaminpackndv_1 : Nominal.NPrf (.imp ph (synWrex m (synCwppcand F C)
            (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))))) :
    Nominal.NPrf
      (.imp ph (synWa (.classMem (synCwppgamma F C) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (synCwppgamma F C) (synClec) (.cv k))))) :=
  by
  have dv_cache_0001 : k ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_k, not_false_eq_true])
  have dv_cache_0002 : m ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_m, not_false_eq_true])
  have dv_cache_0003 : k ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_k, not_false_eq_true])
  have dv_cache_0004 : m ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_m, not_false_eq_true])
  have dv_cache_0005 : k ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show k ≠ m from (by exact dv_k_m))
  have dv_cache_0006 : k ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_k_ph, not_false_eq_true])
  have dv_cache_0007 : m ∉ (ph).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_m_ph, not_false_eq_true])
  have dv_cache_0008 : k ∉ ((Wff.classEq (.cv m) (synCwppgamma F C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union,
          Finset.mem_singleton, dv_k_m, dv_C_k, dv_F_k, or_false, not_false_eq_true])
  have dv_cache_0009 : m ∉ ((synCwppgamma F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, dv_C_m, dv_F_m, or_false, not_false_eq_true])
  have dv_cache_0010 : m ∉ ((synCwppcand F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_m, dv_F_m, or_false, not_false_eq_true])
  have dv_cache_0011 :
    m ∉
      ((synWral k (synCwppcand F C) (synWbr (synCwppgamma F C) (synClec) (.cv k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_C_m, dv_F_m, (Ne.symm dv_k_m),
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfWppgamma C k m F
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @gA1i
      (.classEq (synCwppgamma F C) (synCio m (synWa (.classMem (.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))))))
      ph p0000
  have p0002 :=
    @gWppcandleastreundv ph C k m F dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_wppgammaminpackndv_1
  have p0003 :=
    @gReiotacl2 (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))) m
      (synCwppcand F C)
  have p0004 :=
    @gSyl ph
      (synWreu m (synCwppcand F C)
        (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))))
      (.classMem (synCio m (synWa (.classMem (.cv m) (synCwppcand F C))
            (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))))
        (synCrab m (synCwppcand F C)
          (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))))
      p0002 p0003
  have p0005 :=
    @gEqeltrd ph (synCwppgamma F C)
      (synCio m (synWa (.classMem (.cv m) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))))
      (synCrab m (synCwppcand F C)
        (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k))))
      p0001 p0004
  have p0006 := @gId (.classEq (.cv m) (synCwppgamma F C))
  have p0007 :=
    @gBreq1d (.classEq (.cv m) (synCwppgamma F C)) (.cv m) (synCwppgamma F C) (.cv k)
      (synClec) p0006
  have p0008 :=
    @gRalbidv (.classEq (.cv m) (synCwppgamma F C)) (synWbr (.cv m) (synClec) (.cv k))
      (synWbr (synCwppgamma F C) (synClec) (.cv k)) k (synCwppcand F C) dv_cache_0008
      p0007
  have p0009 :=
    @gElrab (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))
      (synWral k (synCwppcand F C) (synWbr (synCwppgamma F C) (synClec) (.cv k))) m
      (synCwppgamma F C) (synCwppcand F C) dv_cache_0009 dv_cache_0010 dv_cache_0011
      p0008
  have p0010 :=
    @gBiimpi
      (.classMem (synCwppgamma F C) (synCrab m (synCwppcand F C)
          (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))))
      (synWa (.classMem (synCwppgamma F C) (synCwppcand F C))
        (synWral k (synCwppcand F C) (synWbr (synCwppgamma F C) (synClec) (.cv k))))
      p0009
  have p0011 :=
    @gSyl ph
      (.classMem (synCwppgamma F C) (synCrab m (synCwppcand F C)
          (synWral k (synCwppcand F C) (synWbr (.cv m) (synClec) (.cv k)))))
      (synWa (.classMem (synCwppgamma F C) (synCwppcand F C))
        (synWral k (synCwppcand F C) (synWbr (synCwppgamma F C) (synClec) (.cv k))))
      p0005 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_wppgammaminhwndv`. -/
@[expose]
noncomputable def gWppgammaminhwndv (C : Class) (k : Var) (F : Class) (dv_C_k : k ∉ C.fv)
    (dv_F_k : k ∉ F.fv) :
    Nominal.NPrf
      (.imp (synWa (.classMem F (synCvv)) (.classMem C (synChwcards (synCvv))))
        (synWa (.classMem (synCwppgamma F C) (synCwppcand F C))
          (synWral k (synCwppcand F C) (synWbr (synCwppgamma F C) (synClec) (.cv k))))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ ({ k } : Finset Var) ∪ F.fv
  let m : Var := freshVar proofSupport 0
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact fresh_m (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_m_ne_k : m ≠ k := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_k_ne_m : k ≠ m := Ne.symm fresh_m_ne_k
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have dv_cache_0001 : m ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_C, not_false_eq_true])
  have dv_cache_0002 : k ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_k, not_false_eq_true])
  have dv_cache_0003 : m ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_F, not_false_eq_true])
  have dv_cache_0004 : k ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_k, not_false_eq_true])
  have dv_cache_0005 : m ≠ k :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show m ≠ k from (by exact fresh_m_ne_k))
  have dv_cache_0006 : k ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show k ≠ m from (by exact fresh_k_ne_m))
  have dv_cache_0007 :
    k ∉ ((synWa (.classMem F (synCvv)) (.classMem C (synChwcards (synCvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, Finset.mem_union,
          dv_F_k, dv_C_k, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    m ∉ ((synWa (.classMem F (synCvv)) (.classMem C (synChwcards (synCvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards, Finset.mem_union,
          fresh_m_not_F, fresh_m_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @gWppcandminhwndv k C m F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @gWppgammaminpackndv
      (synWa (.classMem F (synCvv)) (.classMem C (synChwcards (synCvv)))) C k m F
      dv_cache_0002 dv_cache_0001 dv_cache_0004 dv_cache_0003 dv_cache_0006 dv_cache_0007
      dv_cache_0008 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_wppcardtfnexndv`. -/
@[expose]
noncomputable def gWppcardtfnexndv :
    Nominal.NPrf (.classMem (synCwppcardtfn) (synCvv)) :=
  by
  have p0000 := @gTcfnex
  have p0001 := @gNcsex
  have p0002 := @gPw1ex (synCncs) p0001
  have p0003 := @gResex (synCtcfn) (synCpw1 (synCncs)) p0000 p0002
  have p0004 := (Nominal.classEqRefl (synCwppcardtfn))
  have p0005 :=
    @gEleq1i (synCwppcardtfn) (synCres (synCtcfn) (synCpw1 (synCncs))) (synCvv)
      p0004
  have p0006 :=
    @gMpbir (.classMem (synCwppcardtfn) (synCvv))
      (.classMem (synCres (synCtcfn) (synCpw1 (synCncs))) (synCvv)) p0003 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_wppcardtfnvalndv`. -/
@[expose]
noncomputable def gWppcardtfnvalndv (q : Var) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (synCpw1 (synCncs)))
        (.classEq (synCfv (synCwppcardtfn) (.cv q)) (synCtc (synCuni (.cv q))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppcardtfn))
  have p0001 :=
    @gFveq1i (.cv q) (synCwppcardtfn) (synCres (synCtcfn) (synCpw1 (synCncs))) p0000
  have p0002 :=
    @gA1i
      (.classEq (synCfv (synCwppcardtfn) (.cv q))
        (synCfv (synCres (synCtcfn) (synCpw1 (synCncs))) (.cv q)))
      (.classMem (.cv q) (synCpw1 (synCncs))) p0001
  have p0003 := @gFvres (.cv q) (synCpw1 (synCncs)) (synCtcfn)
  have p0004 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCncs))) (synCfv (synCwppcardtfn) (.cv q))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCncs))) (.cv q))
      (synCfv (synCtcfn) (.cv q)) p0002 p0003
  have p0005 := @gHnwpw1argcl (synCncs) q
  have p0006 :=
    @gSimprd (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classMem (synCuni (.cv q)) (synCncs))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0005
  have p0007 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synCncs))) (.cv q)
      (synCsn (synCuni (.cv q))) (synCtcfn) p0006
  have p0008 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCncs))) (synCfv (synCwppcardtfn) (.cv q))
      (synCfv (synCtcfn) (.cv q)) (synCfv (synCtcfn) (synCsn (synCuni (.cv q))))
      p0004 p0007
  have p0010 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classMem (synCuni (.cv q)) (synCncs))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0005
  have p0011 := @gElex (synCuni (.cv q)) (synCncs)
  have p0012 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classMem (synCuni (.cv q)) (synCncs)) (.classMem (synCuni (.cv q)) (synCvv))
      p0010 p0011
  have p0013 := @gTcfnfvcl (synCuni (.cv q))
  have p0014 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classMem (synCuni (.cv q)) (synCvv))
      (.classEq (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q))))
      p0012 p0013
  have p0015 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCncs))) (synCfv (synCwppcardtfn) (.cv q))
      (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q)))
      p0008 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_wppcardtfnmapndv`. -/
@[expose]
noncomputable def gWppcardtfnmapndv :
    Nominal.NPrf (synWf (synCwppcardtfn) (synCpw1 (synCncs)) (synCncs)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let q : Var := freshVar proofSupport 0
  have dv_cache_0001 : q ∉ ((synCpw1 (synCncs))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((synCncs)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((synCwppcardtfn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardtfn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @gFntcfn
  have p0001 := @gPw1ss1c (synCncs)
  have p0002 :=
    @gPm32i (synWfn (synCtcfn) (synC1c)) (synWss (synCpw1 (synCncs)) (synC1c))
      p0000 p0001
  have p0003 := @gFnssres (synC1c) (synCpw1 (synCncs)) (synCtcfn)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := (Nominal.classEqRefl (synCwppcardtfn))
  have p0006 :=
    @gFneq1i (synCpw1 (synCncs)) (synCwppcardtfn)
      (synCres (synCtcfn) (synCpw1 (synCncs))) p0005
  have p0007 :=
    @gMpbir (synWfn (synCwppcardtfn) (synCpw1 (synCncs)))
      (synWfn (synCres (synCtcfn) (synCpw1 (synCncs))) (synCpw1 (synCncs))) p0004
      p0006
  have p0009 :=
    @gFveq1i (.cv q) (synCwppcardtfn) (synCres (synCtcfn) (synCpw1 (synCncs))) p0005
  have p0010 :=
    @gA1i
      (.classEq (synCfv (synCwppcardtfn) (.cv q))
        (synCfv (synCres (synCtcfn) (synCpw1 (synCncs))) (.cv q)))
      (.classMem (.cv q) (synCpw1 (synCncs))) p0009
  have p0011 := @gFvres (.cv q) (synCpw1 (synCncs)) (synCtcfn)
  have p0012 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCncs))) (synCfv (synCwppcardtfn) (.cv q))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCncs))) (.cv q))
      (synCfv (synCtcfn) (.cv q)) p0010 p0011
  have p0013 := @gHnwpw1argcl (synCncs) q
  have p0014 :=
    @gSimprd (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classMem (synCuni (.cv q)) (synCncs))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0013
  have p0015 :=
    @gFveq2d (.classMem (.cv q) (synCpw1 (synCncs))) (.cv q)
      (synCsn (synCuni (.cv q))) (synCtcfn) p0014
  have p0016 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCncs))) (synCfv (synCwppcardtfn) (.cv q))
      (synCfv (synCtcfn) (.cv q)) (synCfv (synCtcfn) (synCsn (synCuni (.cv q))))
      p0012 p0015
  have p0018 :=
    @gSimpld (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classMem (synCuni (.cv q)) (synCncs))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0013
  have p0019 := @gElex (synCuni (.cv q)) (synCncs)
  have p0020 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classMem (synCuni (.cv q)) (synCncs)) (.classMem (synCuni (.cv q)) (synCvv))
      p0018 p0019
  have p0021 := @gTcfnfvcl (synCuni (.cv q))
  have p0022 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classMem (synCuni (.cv q)) (synCvv))
      (.classEq (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q))))
      p0020 p0021
  have p0023 :=
    @gEqtrd (.classMem (.cv q) (synCpw1 (synCncs))) (synCfv (synCwppcardtfn) (.cv q))
      (synCfv (synCtcfn) (synCsn (synCuni (.cv q)))) (synCtc (synCuni (.cv q)))
      p0016 p0022
  have p0026 := @gTccl (synCuni (.cv q))
  have p0027 :=
    @gSyl (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classMem (synCuni (.cv q)) (synCncs))
      (.classMem (synCtc (synCuni (.cv q))) (synCncs)) p0018 p0026
  have p0028 :=
    @gEqeltrd (.classMem (.cv q) (synCpw1 (synCncs)))
      (synCfv (synCwppcardtfn) (.cv q)) (synCtc (synCuni (.cv q))) (synCncs) p0023
      p0027
  have p0029 :=
    @gRgen (.classMem (synCfv (synCwppcardtfn) (.cv q)) (synCncs)) q
      (synCpw1 (synCncs)) p0028
  have p0030 :=
    @gPm32i (synWfn (synCwppcardtfn) (synCpw1 (synCncs)))
      (synWral q (synCpw1 (synCncs))
        (.classMem (synCfv (synCwppcardtfn) (.cv q)) (synCncs)))
      p0007 p0029
  have p0031 :=
    @gFfnfv q (synCpw1 (synCncs)) (synCncs) (synCwppcardtfn) dv_cache_0001
      dv_cache_0002 dv_cache_0003
  have p0032 :=
    @gMpbir (synWf (synCwppcardtfn) (synCpw1 (synCncs)) (synCncs))
      (synWa (synWfn (synCwppcardtfn) (synCpw1 (synCncs)))
        (synWral q (synCpw1 (synCncs))
          (.classMem (synCfv (synCwppcardtfn) (.cv q)) (synCncs))))
      p0030 p0031
  exact p0032


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part044`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppcardtfnf1ndv`. -/
@[expose]
noncomputable def gWppcardtfnf1ndv :
    Nominal.NPrf (synWf1 (synCwppcardtfn) (synCpw1 (synCncs)) (synCncs)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : q ∉ ((Wff.classMem (.cv p) (synCpw1 (synCncs)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 : p ∉ ((synCpw1 (synCncs))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 : q ∉ ((synCpw1 (synCncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0004 : p ∉ ((synCwppcardtfn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardtfn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : q ∉ ((synCwppcardtfn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcardtfn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have p0000 := @gWppcardtfnmapndv
  have p0001 :=
    @gSimp1 (.classMem (.cv p) (synCpw1 (synCncs)))
      (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classEq (synCfv (synCwppcardtfn) (.cv p)) (synCfv (synCwppcardtfn) (.cv q)))
  have p0002 := @gHnwpw1argcl (synCncs) p
  have p0003 :=
    @gSyl
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classMem (.cv p) (synCpw1 (synCncs)))
      (synWa (.classMem (synCuni (.cv p)) (synCncs))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))))
      p0001 p0002
  have p0004 :=
    @gSimprd
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classMem (synCuni (.cv p)) (synCncs))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0003
  have p0005 :=
    @gSimp3 (.classMem (.cv p) (synCpw1 (synCncs)))
      (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classEq (synCfv (synCwppcardtfn) (.cv p)) (synCfv (synCwppcardtfn) (.cv q)))
  have p0007 := @gWppcardtfnvalndv p
  have p0008 :=
    @gSyl
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classMem (.cv p) (synCpw1 (synCncs)))
      (.classEq (synCfv (synCwppcardtfn) (.cv p)) (synCtc (synCuni (.cv p)))) p0001
      p0007
  have p0009 :=
    @gSimp2 (.classMem (.cv p) (synCpw1 (synCncs)))
      (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classEq (synCfv (synCwppcardtfn) (.cv p)) (synCfv (synCwppcardtfn) (.cv q)))
  have p0010 := @gWppcardtfnvalndv q
  have p0011 :=
    @gSyl
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classEq (synCfv (synCwppcardtfn) (.cv q)) (synCtc (synCuni (.cv q)))) p0009
      p0010
  have p0012 :=
    @gN3eqtr3d
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (synCfv (synCwppcardtfn) (.cv p)) (synCfv (synCwppcardtfn) (.cv q))
      (synCtc (synCuni (.cv p))) (synCtc (synCuni (.cv q))) p0005 p0008 p0011
  have p0016 :=
    @gSimpld
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classMem (synCuni (.cv p)) (synCncs))
      (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0003
  have p0018 := @gHnwpw1argcl (synCncs) q
  have p0019 :=
    @gSyl
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classMem (.cv q) (synCpw1 (synCncs)))
      (synWa (.classMem (synCuni (.cv q)) (synCncs))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))))
      p0009 p0018
  have p0020 :=
    @gSimpld
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classMem (synCuni (.cv q)) (synCncs))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0019
  have p0021 :=
    @gJca
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classMem (synCuni (.cv p)) (synCncs)) (.classMem (synCuni (.cv q)) (synCncs))
      p0016 p0020
  have p0022 := @gTc11 (synCuni (.cv p)) (synCuni (.cv q))
  have p0023 :=
    @gSyl
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (synWa (.classMem (synCuni (.cv p)) (synCncs))
        (.classMem (synCuni (.cv q)) (synCncs)))
      (synWb (.classEq (synCtc (synCuni (.cv p))) (synCtc (synCuni (.cv q))))
        (.classEq (synCuni (.cv p)) (synCuni (.cv q))))
      p0021 p0022
  have p0024 :=
    @gBiimpd
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classEq (synCtc (synCuni (.cv p))) (synCtc (synCuni (.cv q))))
      (.classEq (synCuni (.cv p)) (synCuni (.cv q))) p0023
  have p0025 :=
    @gMpd
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classEq (synCtc (synCuni (.cv p))) (synCtc (synCuni (.cv q))))
      (.classEq (synCuni (.cv p)) (synCuni (.cv q))) p0012 p0024
  have p0026 :=
    @gSneqd
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (synCuni (.cv p)) (synCuni (.cv q)) p0025
  have p0027 :=
    @gEqtrd
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.cv p) (synCsn (synCuni (.cv p))) (synCsn (synCuni (.cv q))) p0004 p0026
  have p0031 :=
    @gSimprd
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.classMem (synCuni (.cv q)) (synCncs))
      (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0019
  have p0032 :=
    @gEqcomd
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.cv q) (synCsn (synCuni (.cv q))) p0031
  have p0033 :=
    @gEqtrd
      (synW3a (.classMem (.cv p) (synCpw1 (synCncs)))
        (.classMem (.cv q) (synCpw1 (synCncs))) (.classEq (synCfv (synCwppcardtfn) (.cv p))
          (synCfv (synCwppcardtfn) (.cv q))))
      (.cv p) (synCsn (synCuni (.cv q))) (.cv q) p0027 p0032
  have p0034 :=
    @gN3exp (.classMem (.cv p) (synCpw1 (synCncs)))
      (.classMem (.cv q) (synCpw1 (synCncs)))
      (.classEq (synCfv (synCwppcardtfn) (.cv p)) (synCfv (synCwppcardtfn) (.cv q)))
      (.classEq (.cv p) (.cv q)) p0033
  have p0035 :=
    @gRalrimiv (.classMem (.cv p) (synCpw1 (synCncs)))
      (.imp (.classEq (synCfv (synCwppcardtfn) (.cv p)) (synCfv (synCwppcardtfn) (.cv q)))
        (.classEq (.cv p) (.cv q)))
      q (synCpw1 (synCncs)) dv_cache_0001 p0034
  have p0036 :=
    @gRgen
      (synWral q (synCpw1 (synCncs)) (.imp (.classEq (synCfv (synCwppcardtfn) (.cv p))
            (synCfv (synCwppcardtfn) (.cv q))) (.classEq (.cv p) (.cv q))))
      p (synCpw1 (synCncs)) p0035
  have p0037 :=
    @gPm32i (synWf (synCwppcardtfn) (synCpw1 (synCncs)) (synCncs))
      (synWral p (synCpw1 (synCncs)) (synWral q (synCpw1 (synCncs)) (.imp
            (.classEq (synCfv (synCwppcardtfn) (.cv p)) (synCfv (synCwppcardtfn) (.cv q)))
            (.classEq (.cv p) (.cv q)))))
      p0000 p0036
  have p0038 :=
    @gDff13 p q (synCpw1 (synCncs)) (synCncs) (synCwppcardtfn) dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0039_e01_recanon :
    Nominal.NPrf
      (synWb (synWf1 (synCwppcardtfn) (synCpw1 (synCncs)) (synCncs))
        (synWa (synWf (synCwppcardtfn) (synCpw1 (synCncs)) (synCncs))
          (synWral p (synCpw1 (synCncs)) (synWral q (synCpw1 (synCncs)) (.imp
                (.classEq (synCfv (synCwppcardtfn) (.cv p))
                  (synCfv (synCwppcardtfn) (.cv q))) (.classEq (.cv p) (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWf1 synWa synWf synWfun synWss synCin synCcompl synCnin
          synWnan synCcom synCopab synWex synCcnv synCid synCwppcardtfn synCres
          synCtcfn synCmpt synC1c synCtc synCio synCuni synCsn synCpw1 synCncs
          synCqs synWrex synCec synCima synCvv synCen
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @gMpbir (synWf1 (synCwppcardtfn) (synCpw1 (synCncs)) (synCncs))
      (synWa (synWf (synCwppcardtfn) (synCpw1 (synCncs)) (synCncs))
        (synWral p (synCpw1 (synCncs)) (synWral q (synCpw1 (synCncs)) (.imp
              (.classEq (synCfv (synCwppcardtfn) (.cv p)) (synCfv (synCwppcardtfn) (.cv q)))
              (.classEq (.cv p) (.cv q))))))
      p0037 p0039_e01_recanon
  exact p0039

/-- Checked nominal proof certificate identified upstream as `g_wppcardtfnvalsingndv`. -/
@[expose]
noncomputable def gWppcardtfnvalsingndv (D : Class) :
    Nominal.NPrf
      (.imp (.classMem D (synCncs))
        (.classEq (synCfv (synCwppcardtfn) (synCsn D)) (synCtc D))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwppcardtfn))
  have p0001 :=
    @gFveq1i (synCsn D) (synCwppcardtfn) (synCres (synCtcfn) (synCpw1 (synCncs)))
      p0000
  have p0002 :=
    @gA1i
      (.classEq (synCfv (synCwppcardtfn) (synCsn D))
        (synCfv (synCres (synCtcfn) (synCpw1 (synCncs))) (synCsn D)))
      (.classMem D (synCncs)) p0001
  have p0003 := @gSnelpw1 D (synCncs)
  have p0004 :=
    @gBiimpri (.classMem (synCsn D) (synCpw1 (synCncs))) (.classMem D (synCncs))
      p0003
  have p0005 := @gFvres (synCsn D) (synCpw1 (synCncs)) (synCtcfn)
  have p0006 :=
    @gSyl (.classMem D (synCncs)) (.classMem (synCsn D) (synCpw1 (synCncs)))
      (.classEq (synCfv (synCres (synCtcfn) (synCpw1 (synCncs))) (synCsn D))
        (synCfv (synCtcfn) (synCsn D)))
      p0004 p0005
  have p0007 :=
    @gEqtrd (.classMem D (synCncs)) (synCfv (synCwppcardtfn) (synCsn D))
      (synCfv (synCres (synCtcfn) (synCpw1 (synCncs))) (synCsn D))
      (synCfv (synCtcfn) (synCsn D)) p0002 p0006
  have p0008 := @gId (.classMem D (synCncs))
  have p0009 := @gElex D (synCncs)
  have p0010 :=
    @gSyl (.classMem D (synCncs)) (.classMem D (synCncs)) (.classMem D (synCvv)) p0008
      p0009
  have p0011 := @gTcfnfvcl D
  have p0012 :=
    @gSyl (.classMem D (synCncs)) (.classMem D (synCvv))
      (.classEq (synCfv (synCtcfn) (synCsn D)) (synCtc D)) p0010 p0011
  have p0013 :=
    @gEqtrd (.classMem D (synCncs)) (synCfv (synCwppcardtfn) (synCsn D))
      (synCfv (synCtcfn) (synCsn D)) (synCtc D) p0007 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_wppreachorbitextcbidv`. -/
@[expose]
noncomputable def gWppreachorbitextcbidv (x : Var) (C : Class) (D : Class) (F : Class)
    (G : Class) (r : Var) (p : Var) (a : Var) (dv_C_a : a ∉ C.fv) (dv_C_p : p ∉ C.fv)
    (dv_D_a : a ∉ D.fv) (dv_D_p : p ∉ D.fv) (dv_D_r : r ∉ D.fv) (dv_D_x : x ∉ D.fv)
    (dv_F_a : a ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv)
    (dv_G_a : a ∉ G.fv) (dv_G_p : p ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_a_p : a ≠ p)
    (dv_a_r : a ≠ r)
    (hyp_wppreachorbitextcbidv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppreachorbitextcbidv_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wppreachorbitextcbidv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppreachorbitextcbidv_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppreachorbitextcbidv_5 : Nominal.NPrf (.classMem (synCtc D) (synCdm G)))
    (hyp_wppreachorbitextcbidv_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wppreachorbitextcbidv_7 : Nominal.NPrf (synWral x (synCdm F)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv G (synCtc (.cv x))))))
    (hyp_wppreachorbitextcbidv_8 : Nominal.NPrf (.classMem C (synCncs)))
    (hyp_wppreachorbitextcbidv_9 : Nominal.NPrf (synWral r (synCnnc)
          (.classMem (synCfv (synCfrec F D) (.cv r)) (synCncs)))) :
    Nominal.NPrf
      (synWb (synWrex a (synCnnc) (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a))))
        (synWrex p (synCnnc) (synWbr (synCtc C) (synClec)
            (synCfv (synCfrec G (synCtc D)) (.cv p))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ C.fv ∪ D.fv ∪ F.fv ∪ G.fv ∪ ({ r } : Finset Var) ∪
        ({ p } : Finset Var) ∪
      ({ a } : Finset Var)
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_C : n ∉ C.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))))
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_n_not_F : n ∉ F.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_n_not_G : n ∉ G.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_ne_r : n ≠ r := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_r_ne_n : r ≠ n := Ne.symm fresh_n_ne_r
  have fresh_n_ne_p : n ≠ p := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_n : a ≠ n := Ne.symm fresh_n_ne_a
  have dv_cache_0001 : r ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_a_r), not_false_eq_true])
  have dv_cache_0002 : r ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 :
    r ∉ ((Wff.classMem (synCfv (synCfrec F D) (.cv a)) (synCncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_a_r), dv_F_r, dv_D_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0005 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_x, not_false_eq_true])
  have dv_cache_0006 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((synCtc (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_a_p), not_false_eq_true])
  have dv_cache_0008 : p ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 :
    p ∉
      ((synWbr (synCtc C) (synClec)
          (synCfv (synCfrec G (synCtc D)) (synCtc (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_C_p, (Ne.symm dv_a_p), dv_G_p, dv_D_p,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    a ∉
      ((synWrex p (synCnnc) (synWbr (synCtc C) (synClec)
            (synCfv (synCfrec G (synCtc D)) (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_C_a, dv_a_p, dv_G_a, dv_D_a, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_p, not_false_eq_true])
  have dv_cache_0012 : r ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_n, not_false_eq_true])
  have dv_cache_0013 :
    r ∉ ((Wff.classMem (synCfv (synCfrec F D) (.cv n)) (synCncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_n, dv_F_r, dv_D_r, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_n, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0016 :
    a ∉ ((synWbr C (synClec) (synCfv (synCfrec F D) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_C_a, fresh_a_ne_n, dv_F_a, dv_D_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 :
    n ∉
      ((synWrex a (synCnnc) (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_n_not_C, fresh_n_ne_a, fresh_n_not_F, fresh_n_not_D,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    n ∉
      ((synWa (.classMem (.cv p) (synCnnc)) (synWbr (synCtc C) (synClec)
            (synCfv (synCfrec G (synCtc D)) (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_p, fresh_n_not_C, fresh_n_not_G, fresh_n_not_D,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 :
    p ∉
      ((synWrex a (synCnnc) (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_C_p, (Ne.symm dv_a_p), dv_F_p, dv_D_p,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 :=
    @gSimpl (.classMem (.cv a) (synCnnc))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a)))
  have p0001 := @gNntccl (.cv a)
  have p0002 :=
    @gSyl
      (synWa (.classMem (.cv a) (synCnnc))
        (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a))))
      (.classMem (.cv a) (synCnnc)) (.classMem (synCtc (.cv a)) (synCnnc)) p0000 p0001
  have p0003 :=
    @gA1i (.classMem C (synCncs)) (.classMem (.cv a) (synCnnc))
      hyp_wppreachorbitextcbidv_8
  have p0004 :=
    @gA1i
      (synWral r (synCnnc) (.classMem (synCfv (synCfrec F D) (.cv r)) (synCncs)))
      (.classMem (.cv a) (synCnnc)) hyp_wppreachorbitextcbidv_9
  have p0005 := @gId (.classEq (.cv r) (.cv a))
  have p0006 := @gFveq2d (.classEq (.cv r) (.cv a)) (.cv r) (.cv a) (synCfrec F D) p0005
  have p0007 :=
    @gEleq1d (.classEq (.cv r) (.cv a)) (synCfv (synCfrec F D) (.cv r))
      (synCfv (synCfrec F D) (.cv a)) (synCncs) p0006
  have p0008 :=
    @gRspcv (.classMem (synCfv (synCfrec F D) (.cv r)) (synCncs))
      (.classMem (synCfv (synCfrec F D) (.cv a)) (synCncs)) r (.cv a) (synCnnc)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0007
  have p0009 :=
    @gMpd (.classMem (.cv a) (synCnnc))
      (synWral r (synCnnc) (.classMem (synCfv (synCfrec F D) (.cv r)) (synCncs)))
      (.classMem (synCfv (synCfrec F D) (.cv a)) (synCncs)) p0004 p0008
  have p0010 :=
    @gJca (.classMem (.cv a) (synCnnc)) (.classMem C (synCncs))
      (.classMem (synCfv (synCfrec F D) (.cv a)) (synCncs)) p0003 p0009
  have p0011 := @gTlecg C (synCfv (synCfrec F D) (.cv a))
  have p0012 :=
    @gSyl (.classMem (.cv a) (synCnnc))
      (synWa (.classMem C (synCncs)) (.classMem (synCfv (synCfrec F D) (.cv a)) (synCncs)))
      (synWb (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a)))
        (synWbr (synCtc C) (synClec) (synCtc (synCfv (synCfrec F D) (.cv a)))))
      p0010 p0011
  have p0013 :=
    @gFrectchom0 x F G D (.cv a) dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_wppreachorbitextcbidv_1 hyp_wppreachorbitextcbidv_2 hyp_wppreachorbitextcbidv_3
      hyp_wppreachorbitextcbidv_4 hyp_wppreachorbitextcbidv_5 hyp_wppreachorbitextcbidv_6
      hyp_wppreachorbitextcbidv_7
  have p0014 :=
    @gBreq2d (.classMem (.cv a) (synCnnc)) (synCtc (synCfv (synCfrec F D) (.cv a)))
      (synCfv (synCfrec G (synCtc D)) (synCtc (.cv a))) (synCtc C) (synClec) p0013
  have p0015 :=
    @gBitrd (.classMem (.cv a) (synCnnc))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a)))
      (synWbr (synCtc C) (synClec) (synCtc (synCfv (synCfrec F D) (.cv a))))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (synCtc (.cv a))))
      p0012 p0014
  have p0016 :=
    @gBiimpd (.classMem (.cv a) (synCnnc))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a)))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (synCtc (.cv a))))
      p0015
  have p0017 :=
    @gImp (.classMem (.cv a) (synCnnc))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a)))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (synCtc (.cv a))))
      p0016
  have p0018 :=
    @gJca
      (synWa (.classMem (.cv a) (synCnnc))
        (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a))))
      (.classMem (synCtc (.cv a)) (synCnnc))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (synCtc (.cv a))))
      p0002 p0017
  have p0019 := @gId (.classEq (.cv p) (synCtc (.cv a)))
  have p0020 :=
    @gFveq2d (.classEq (.cv p) (synCtc (.cv a))) (.cv p) (synCtc (.cv a))
      (synCfrec G (synCtc D)) p0019
  have p0021 :=
    @gBreq2d (.classEq (.cv p) (synCtc (.cv a)))
      (synCfv (synCfrec G (synCtc D)) (.cv p))
      (synCfv (synCfrec G (synCtc D)) (synCtc (.cv a))) (synCtc C) (synClec) p0020
  have p0022 :=
    @gRspcev (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p)))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (synCtc (.cv a))))
      p (synCtc (.cv a)) (synCnnc) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0021
  have p0023 :=
    @gSyl
      (synWa (.classMem (.cv a) (synCnnc))
        (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a))))
      (synWa (.classMem (synCtc (.cv a)) (synCnnc)) (synWbr (synCtc C) (synClec)
          (synCfv (synCfrec G (synCtc D)) (synCtc (.cv a)))))
      (synWrex p (synCnnc)
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      p0018 p0022
  have p0024 :=
    @gRexlimiva (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a)))
      (synWrex p (synCnnc)
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      a (synCnnc) dv_cache_0010 p0023
  have p0025 :=
    @gSimpl (.classMem (.cv p) (synCnnc))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p)))
  have p0026 := @gNntcpreim n (.cv p) dv_cache_0011
  have p0027 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCnnc))
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      (.classMem (.cv p) (synCnnc))
      (synWrex n (synCnnc) (.classEq (synCtc (.cv n)) (.cv p))) p0025 p0026
  have p0028 :=
    @gSimp2
      (synWa (.classMem (.cv p) (synCnnc))
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv p))
  have p0029 :=
    @gSimp1
      (synWa (.classMem (.cv p) (synCnnc))
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv p))
  have p0030 :=
    @gSimpr (.classMem (.cv p) (synCnnc))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p)))
  have p0031 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv p) (synCnnc))
          (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv p)))
      (synWa (.classMem (.cv p) (synCnnc))
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))) p0029
      p0030
  have p0032 :=
    @gSimp3
      (synWa (.classMem (.cv p) (synCnnc))
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv p))
  have p0033 := @gId (.classEq (synCtc (.cv n)) (.cv p))
  have p0034 :=
    @gFveq2d (.classEq (synCtc (.cv n)) (.cv p)) (synCtc (.cv n)) (.cv p)
      (synCfrec G (synCtc D)) p0033
  have p0035 :=
    @gBreq2d (.classEq (synCtc (.cv n)) (.cv p))
      (synCfv (synCfrec G (synCtc D)) (synCtc (.cv n)))
      (synCfv (synCfrec G (synCtc D)) (.cv p)) (synCtc C) (synClec) p0034
  have p0036 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv p) (synCnnc))
          (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv p)))
      (.classEq (synCtc (.cv n)) (.cv p))
      (synWb (synWbr (synCtc C) (synClec)
          (synCfv (synCfrec G (synCtc D)) (synCtc (.cv n))))
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      p0032 p0035
  have p0037 :=
    @gMpbird
      (synW3a (synWa (.classMem (.cv p) (synCnnc))
          (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv p)))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (synCtc (.cv n))))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))) p0031
      p0036
  have p0039 :=
    @gA1i (.classMem C (synCncs)) (.classMem (.cv n) (synCnnc))
      hyp_wppreachorbitextcbidv_8
  have p0040 :=
    @gA1i
      (synWral r (synCnnc) (.classMem (synCfv (synCfrec F D) (.cv r)) (synCncs)))
      (.classMem (.cv n) (synCnnc)) hyp_wppreachorbitextcbidv_9
  have p0041 := @gId (.classEq (.cv r) (.cv n))
  have p0042 := @gFveq2d (.classEq (.cv r) (.cv n)) (.cv r) (.cv n) (synCfrec F D) p0041
  have p0043 :=
    @gEleq1d (.classEq (.cv r) (.cv n)) (synCfv (synCfrec F D) (.cv r))
      (synCfv (synCfrec F D) (.cv n)) (synCncs) p0042
  have p0044 :=
    @gRspcv (.classMem (synCfv (synCfrec F D) (.cv r)) (synCncs))
      (.classMem (synCfv (synCfrec F D) (.cv n)) (synCncs)) r (.cv n) (synCnnc)
      dv_cache_0012 dv_cache_0002 dv_cache_0013 p0043
  have p0045 :=
    @gMpd (.classMem (.cv n) (synCnnc))
      (synWral r (synCnnc) (.classMem (synCfv (synCfrec F D) (.cv r)) (synCncs)))
      (.classMem (synCfv (synCfrec F D) (.cv n)) (synCncs)) p0040 p0044
  have p0046 :=
    @gJca (.classMem (.cv n) (synCnnc)) (.classMem C (synCncs))
      (.classMem (synCfv (synCfrec F D) (.cv n)) (synCncs)) p0039 p0045
  have p0047 := @gTlecg C (synCfv (synCfrec F D) (.cv n))
  have p0048 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (synWa (.classMem C (synCncs)) (.classMem (synCfv (synCfrec F D) (.cv n)) (synCncs)))
      (synWb (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n)))
        (synWbr (synCtc C) (synClec) (synCtc (synCfv (synCfrec F D) (.cv n)))))
      p0046 p0047
  have p0049 :=
    @gFrectchom0 x F G D (.cv n) dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_wppreachorbitextcbidv_1 hyp_wppreachorbitextcbidv_2 hyp_wppreachorbitextcbidv_3
      hyp_wppreachorbitextcbidv_4 hyp_wppreachorbitextcbidv_5 hyp_wppreachorbitextcbidv_6
      hyp_wppreachorbitextcbidv_7
  have p0050 :=
    @gBreq2d (.classMem (.cv n) (synCnnc)) (synCtc (synCfv (synCfrec F D) (.cv n)))
      (synCfv (synCfrec G (synCtc D)) (synCtc (.cv n))) (synCtc C) (synClec) p0049
  have p0051 :=
    @gBitrd (.classMem (.cv n) (synCnnc))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n)))
      (synWbr (synCtc C) (synClec) (synCtc (synCfv (synCfrec F D) (.cv n))))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (synCtc (.cv n))))
      p0048 p0050
  have p0052 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv p) (synCnnc))
          (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv p)))
      (.classMem (.cv n) (synCnnc))
      (synWb (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n)))
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (synCtc (.cv n)))))
      p0028 p0051
  have p0053 :=
    @gMpbird
      (synW3a (synWa (.classMem (.cv p) (synCnnc))
          (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv p)))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n)))
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (synCtc (.cv n))))
      p0037 p0052
  have p0054 :=
    @gJca
      (synW3a (synWa (.classMem (.cv p) (synCnnc))
          (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv p)))
      (.classMem (.cv n) (synCnnc))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))) p0028 p0053
  have p0055 := @gId (.classEq (.cv a) (.cv n))
  have p0056 := @gFveq2d (.classEq (.cv a) (.cv n)) (.cv a) (.cv n) (synCfrec F D) p0055
  have p0057 :=
    @gBreq2d (.classEq (.cv a) (.cv n)) (synCfv (synCfrec F D) (.cv a))
      (synCfv (synCfrec F D) (.cv n)) C (synClec) p0056
  have p0058 :=
    @gRspcev (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a)))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))) a (.cv n) (synCnnc)
      dv_cache_0014 dv_cache_0015 dv_cache_0016 p0057
  have p0059 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv p) (synCnnc))
          (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv p)))
      (synWa (.classMem (.cv n) (synCnnc))
        (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))))
      (synWrex a (synCnnc) (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a))))
      p0054 p0058
  have p0060 :=
    @gRexlimdv3a
      (synWa (.classMem (.cv p) (synCnnc))
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      (.classEq (synCtc (.cv n)) (.cv p))
      (synWrex a (synCnnc) (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a)))) n
      (synCnnc) dv_cache_0017 dv_cache_0018 p0059
  have p0061 :=
    @gMpd
      (synWa (.classMem (.cv p) (synCnnc))
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      (synWrex n (synCnnc) (.classEq (synCtc (.cv n)) (.cv p)))
      (synWrex a (synCnnc) (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a))))
      p0027 p0060
  have p0062 :=
    @gRexlimiva
      (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p)))
      (synWrex a (synCnnc) (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a)))) p
      (synCnnc) dv_cache_0019 p0061
  have p0063 :=
    @gImpbii
      (synWrex a (synCnnc) (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a))))
      (synWrex p (synCnnc)
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      p0024 p0062
  exact p0063

/-- Checked nominal proof certificate identified upstream as `g_wppreachorbitfnvndv`. -/
@[expose]
noncomputable def gWppreachorbitfnvndv (C : Class) (F : Class)
    (hyp_wppreachorbitfnvndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (synWfn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCnnc)) :=
  by
  have p0000 := @gWppreachopfn F hyp_wppreachorbitfnvndv_1
  have p0001 := @gFnfun (synCvv) (synCimage (synCcnv F))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gCnvex F hyp_wppreachorbitfnvndv_1
  have p0004 := @gImageex (synCcnv F) p0003
  have p0005 := @gElfuns (synCimage (synCcnv F)) p0004
  have p0006 :=
    @gMpbir (.classMem (synCimage (synCcnv F)) (synCfuns))
      (synWfun (synCimage (synCcnv F))) p0002 p0005
  have p0007 := @gWppreachupperex C
  have p0009 := @gFndm (synCvv) (synCimage (synCcnv F))
  have p0010 := Nominal.mp p0000 p0009
  have p0011 :=
    @gEleqtrri (synCima (synClec) (synCsn C)) (synCvv)
      (synCdm (synCimage (synCcnv F))) p0007 p0010
  have p0012 := @gSsv (synCrn (synCimage (synCcnv F)))
  have p0016 :=
    @gSseqtr4i (synCrn (synCimage (synCcnv F))) (synCvv)
      (synCdm (synCimage (synCcnv F))) p0012 p0010
  have p0017 :=
    @gN3pm32i (.classMem (synCimage (synCcnv F)) (synCfuns))
      (.classMem (synCima (synClec) (synCsn C)) (synCdm (synCimage (synCcnv F))))
      (synWss (synCrn (synCimage (synCcnv F))) (synCdm (synCimage (synCcnv F))))
      p0006 p0011 p0016
  have p0018 :=
    @gWpporbitfnndv (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))
  have p0019 := Nominal.mp p0017 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_elwppreachvndv`. -/
@[expose]
noncomputable def gElwppreachvndv (C : Class) (D : Class) (n : Var) (F : Class)
    (dv_C_n : n ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_F_n : n ∉ F.fv)
    (hyp_elwppreachvndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem D (synCwppreach F C)) (synWrex n (synCnnc) (.classMem D (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (.cv n))))) :=
  by
  have dv_cache_0001 : n ∉ (D).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_n, not_false_eq_true])
  have dv_cache_0002 :
    n ∉ ((synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_F_n,
          dv_C_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    n ∉
      ((synCdm (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_F_n,
          dv_C_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := (Nominal.classEqRefl (synCwppreach F C))
  have p0001 :=
    @gEleq2i (synCwppreach F C)
      (synCuni
        (synCrn (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))))
      D p0000
  have p0002 := @gWppreachorbitfnvndv C F hyp_elwppreachvndv_1
  have p0003 :=
    @gFnfun (synCnnc)
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @gElunirn n D (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
      dv_cache_0001 dv_cache_0002
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @gBitri (.classMem D (synCwppreach F C))
      (.classMem D (synCuni (synCrn
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))))
      (synWrex n
        (synCdm (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))
        (.classMem D
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (.cv n))))
      p0001 p0006
  have p0009 :=
    @gFndm (synCnnc)
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
  have p0010 := Nominal.mp p0002 p0009
  have p0011 :=
    @gRexeqi
      (.classMem D
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (.cv n)))
      n (synCdm (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))
      (synCnnc) dv_cache_0003 dv_cache_0004 p0010
  have p0012 :=
    @gBitri (.classMem D (synCwppreach F C))
      (synWrex n
        (synCdm (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))
        (.classMem D
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (.cv n))))
      (synWrex n (synCnnc) (.classMem D
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (.cv n))))
      p0007 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part045`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppnnstageextcbidv`. -/
@[expose]
noncomputable def gWppnnstageextcbidv (D : Class) (H : Class) (p : Var) (a : Var)
    (dv_D_a : a ∉ D.fv) (dv_D_p : p ∉ D.fv) (dv_H_a : a ∉ H.fv) (dv_H_p : p ∉ H.fv)
    (dv_a_p : a ≠ p) :
    Nominal.NPrf
      (synWb (synWrex a (synCnnc) (.classMem D (synCfv H (.cv a))))
        (synWrex p (synCnnc) (.classMem D (synCfv H (synCtc (.cv p)))))) :=
  by
  let proofSupport : Finset Var :=
    D.fv ∪ H.fv ∪ ({ p } : Finset Var) ∪ ({ a } : Finset Var)
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_D : n ∉ D.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_n_not_H : n ∉ H.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_ne_p : n ≠ p := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_n : p ≠ n := Ne.symm fresh_n_ne_p
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : n ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_a, not_false_eq_true])
  have dv_cache_0002 : p ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_n, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((Wff.classMem D (synCfv H (synCtc (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_p, fresh_p_ne_n, dv_H_p, or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    n ∉ ((synWrex p (synCnnc) (.classMem D (synCfv H (synCtc (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_n_not_D, fresh_n_ne_p, fresh_n_not_H,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0006 :
    n ∉ ((synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_a, fresh_n_not_D, fresh_n_not_H,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 :
    a ∉ ((synWrex p (synCnnc) (.classMem D (synCfv H (synCtc (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_D_a, dv_a_p, dv_H_a, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ ((synCtc (.cv p))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_a_p,
          not_false_eq_true])
  have dv_cache_0009 : a ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((Wff.classMem D (synCfv H (synCtc (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_D_a, dv_a_p, dv_H_a, or_false, not_false_eq_true])
  have dv_cache_0011 :
    p ∉ ((synWrex a (synCnnc) (.classMem D (synCfv H (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_D_p, (Ne.symm dv_a_p), dv_H_p,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @gSimpl (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a)))
  have p0001 := @gNntcpreim n (.cv a) dv_cache_0001
  have p0002 :=
    @gSyl (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
      (.classMem (.cv a) (synCnnc))
      (synWrex n (synCnnc) (.classEq (synCtc (.cv n)) (.cv a))) p0000 p0001
  have p0003 :=
    @gSimp2 (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
      (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv a))
  have p0004 :=
    @gSimp1 (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
      (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv a))
  have p0005 := @gSimpr (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a)))
  have p0006 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv a)))
      (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
      (.classMem D (synCfv H (.cv a))) p0004 p0005
  have p0007 :=
    @gSimp3 (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
      (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv a))
  have p0008 := @gId (.classEq (synCtc (.cv n)) (.cv a))
  have p0009 :=
    @gFveq2d (.classEq (synCtc (.cv n)) (.cv a)) (synCtc (.cv n)) (.cv a) H p0008
  have p0010 :=
    @gEleq2d (.classEq (synCtc (.cv n)) (.cv a)) (synCfv H (synCtc (.cv n)))
      (synCfv H (.cv a)) D p0009
  have p0011 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv a)))
      (.classEq (synCtc (.cv n)) (.cv a))
      (synWb (.classMem D (synCfv H (synCtc (.cv n)))) (.classMem D (synCfv H (.cv a))))
      p0007 p0010
  have p0012 :=
    @gMpbird
      (synW3a (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv a)))
      (.classMem D (synCfv H (synCtc (.cv n)))) (.classMem D (synCfv H (.cv a))) p0006
      p0011
  have p0013 :=
    @gJca
      (synW3a (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv a)))
      (.classMem (.cv n) (synCnnc)) (.classMem D (synCfv H (synCtc (.cv n)))) p0003
      p0012
  have p0014 := @gTceq (.cv p) (.cv n)
  have p0015 :=
    @gFveq2d (.classEq (.cv p) (.cv n)) (synCtc (.cv p)) (synCtc (.cv n)) H p0014
  have p0016 :=
    @gEleq2d (.classEq (.cv p) (.cv n)) (synCfv H (synCtc (.cv p)))
      (synCfv H (synCtc (.cv n))) D p0015
  have p0017 :=
    @gRspcev (.classMem D (synCfv H (synCtc (.cv p))))
      (.classMem D (synCfv H (synCtc (.cv n)))) p (.cv n) (synCnnc) dv_cache_0002
      dv_cache_0003 dv_cache_0004 p0016
  have p0018 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
        (.classMem (.cv n) (synCnnc)) (.classEq (synCtc (.cv n)) (.cv a)))
      (synWa (.classMem (.cv n) (synCnnc)) (.classMem D (synCfv H (synCtc (.cv n)))))
      (synWrex p (synCnnc) (.classMem D (synCfv H (synCtc (.cv p))))) p0013 p0017
  have p0019 :=
    @gRexlimdv3a
      (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
      (.classEq (synCtc (.cv n)) (.cv a))
      (synWrex p (synCnnc) (.classMem D (synCfv H (synCtc (.cv p))))) n (synCnnc)
      dv_cache_0005 dv_cache_0006 p0018
  have p0020 :=
    @gMpd (synWa (.classMem (.cv a) (synCnnc)) (.classMem D (synCfv H (.cv a))))
      (synWrex n (synCnnc) (.classEq (synCtc (.cv n)) (.cv a)))
      (synWrex p (synCnnc) (.classMem D (synCfv H (synCtc (.cv p))))) p0002 p0019
  have p0021 :=
    @gRexlimiva (.classMem D (synCfv H (.cv a)))
      (synWrex p (synCnnc) (.classMem D (synCfv H (synCtc (.cv p))))) a (synCnnc)
      dv_cache_0007 p0020
  have p0022 :=
    @gSimpl (.classMem (.cv p) (synCnnc)) (.classMem D (synCfv H (synCtc (.cv p))))
  have p0023 := @gNntccl (.cv p)
  have p0024 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCnnc)) (.classMem D (synCfv H (synCtc (.cv p)))))
      (.classMem (.cv p) (synCnnc)) (.classMem (synCtc (.cv p)) (synCnnc)) p0022 p0023
  have p0025 :=
    @gSimpr (.classMem (.cv p) (synCnnc)) (.classMem D (synCfv H (synCtc (.cv p))))
  have p0026 :=
    @gJca
      (synWa (.classMem (.cv p) (synCnnc)) (.classMem D (synCfv H (synCtc (.cv p)))))
      (.classMem (synCtc (.cv p)) (synCnnc)) (.classMem D (synCfv H (synCtc (.cv p))))
      p0024 p0025
  have p0027 := @gId (.classEq (.cv a) (synCtc (.cv p)))
  have p0028 :=
    @gFveq2d (.classEq (.cv a) (synCtc (.cv p))) (.cv a) (synCtc (.cv p)) H p0027
  have p0029 :=
    @gEleq2d (.classEq (.cv a) (synCtc (.cv p))) (synCfv H (.cv a))
      (synCfv H (synCtc (.cv p))) D p0028
  have p0030 :=
    @gRspcev (.classMem D (synCfv H (.cv a)))
      (.classMem D (synCfv H (synCtc (.cv p)))) a (synCtc (.cv p)) (synCnnc)
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0029
  have p0031 :=
    @gSyl
      (synWa (.classMem (.cv p) (synCnnc)) (.classMem D (synCfv H (synCtc (.cv p)))))
      (synWa (.classMem (synCtc (.cv p)) (synCnnc))
        (.classMem D (synCfv H (synCtc (.cv p)))))
      (synWrex a (synCnnc) (.classMem D (synCfv H (.cv a)))) p0026 p0030
  have p0032 :=
    @gRexlimiva (.classMem D (synCfv H (synCtc (.cv p))))
      (synWrex a (synCnnc) (.classMem D (synCfv H (.cv a)))) p (synCnnc) dv_cache_0011
      p0031
  have p0033 :=
    @gImpbii (synWrex a (synCnnc) (.classMem D (synCfv H (.cv a))))
      (synWrex p (synCnnc) (.classMem D (synCfv H (synCtc (.cv p))))) p0021 p0032
  exact p0033

/-- Checked nominal proof certificate identified upstream as `g_wppreachtcrexvndv`. -/
@[expose]
noncomputable def gWppreachtcrexvndv (C : Class) (D : Class) (n : Var) (F : Class)
    (dv_C_n : n ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_F_n : n ∉ F.fv)
    (hyp_wppreachtcrexvndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem D (synCwppreach F C)) (synWrex n (synCnnc) (.classMem D (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv n)))))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ ({ n } : Finset Var) ∪ F.fv
  let m : Var := freshVar proofSupport 0
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_m_not_C : m ∉ C.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_m_not_D : m ∉ D.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_m_ne_n : m ≠ n := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_m_not_F : m ∉ F.fv := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (h))
  have dv_cache_0001 : m ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_C, not_false_eq_true])
  have dv_cache_0002 : m ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_D, not_false_eq_true])
  have dv_cache_0003 : m ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_F, not_false_eq_true])
  have dv_cache_0004 : n ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_n, not_false_eq_true])
  have dv_cache_0005 :
    m ∉ ((synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_m_not_F, fresh_m_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    n ∉ ((synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union, dv_F_n,
          dv_C_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show m ≠ n from (by exact fresh_m_ne_n))
  have p0000 :=
    @gElwppreachvndv C D m F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppreachtcrexvndv_1
  have p0001 :=
    @gWppnnstageextcbidv D
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) n m
      dv_cache_0002 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0002 :=
    @gBitri (.classMem D (synCwppreach F C))
      (synWrex m (synCnnc) (.classMem D
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (.cv m))))
      (synWrex n (synCnnc) (.classMem D
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv n)))))
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_wppreachlayerorbvndv`. -/
@[expose]
noncomputable def gWppreachlayerorbvndv (C : Class) (D : Class) (F : Class) (N : Class)
    (hyp_wppreachlayerorbvndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppreachlayerorbvndv_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wppreachlayerorbvndv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppreachlayerorbvndv_4 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (.imp (.classMem N (synCnnc)) (synWb (.classMem D (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc N))) (synWbr C (synClec) (synCfv (synCfrec F D) N)))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ D.fv ∪ F.fv ∪ N.fv
  let c : Var := freshVar proofSupport 0
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_not_C : c ∉ C.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_c_not_D : c ∉ D.fv := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_c_not_F : c ∉ F.fv := by
    intro h
    exact fresh_c (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_c_not_N : c ∉ N.fv := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (h))
  have dv_cache_0001 : Disjoint ((Class.cv c)).fv (F).fv := by
    exact
      (show Disjoint ((Class.cv c)).fv (F).fv from (by
          rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
          exact
            (show Disjoint (({ c } : Finset Var)) ((F).fv) from
              (Finset.disjoint_singleton_left.mpr
                (show c ∉ (F).fv from (by exact fresh_c_not_F))))))
  have dv_cache_0002 : c ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_c_not_C, not_false_eq_true])
  have dv_cache_0003 :
    c ∉
      ((Wff.imp (.classMem N (synCnnc)) (synWb (.classMem D (synCfv
                (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
                (synCtc N))) (synWbr C (synClec) (synCfv (synCfrec F D) N))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
          fresh_c_not_N, fresh_c_not_D, fresh_c_not_F, fresh_c_not_C,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gEqidd (.classEq (.cv c) C) (synCimage (synCcnv F))
  have p0001 := @gId (.classEq (.cv c) C)
  have p0002 := @gSneqd (.classEq (.cv c) C) (.cv c) C p0001
  have p0003 :=
    @gImaeq2d (.classEq (.cv c) C) (synCsn (.cv c)) (synCsn C) (synClec) p0002
  have p0004 :=
    @gJca (.classEq (.cv c) C)
      (.classEq (synCimage (synCcnv F)) (synCimage (synCcnv F)))
      (.classEq (synCima (synClec) (synCsn (.cv c))) (synCima (synClec) (synCsn C)))
      p0000 p0003
  have p0005 :=
    @gFreceq12 (synCimage (synCcnv F)) (synCimage (synCcnv F))
      (synCima (synClec) (synCsn (.cv c))) (synCima (synClec) (synCsn C))
  have p0006 :=
    @gSyl (.classEq (.cv c) C)
      (synWa (.classEq (synCimage (synCcnv F)) (synCimage (synCcnv F)))
        (.classEq (synCima (synClec) (synCsn (.cv c))) (synCima (synClec) (synCsn C))))
      (.classEq (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn (.cv c))))
        (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))))
      p0004 p0005
  have p0007 :=
    @gFveq1d (.classEq (.cv c) C) (synCtc N)
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn (.cv c))))
      (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C))) p0006
  have p0008 :=
    @gEleq2d (.classEq (.cv c) C)
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn (.cv c))))
        (synCtc N))
      (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
        (synCtc N))
      D p0007
  have p0010 :=
    @gBreq1d (.classEq (.cv c) C) (.cv c) C (synCfv (synCfrec F D) N) (synClec) p0001
  have p0011 :=
    @gBibi12d (.classEq (.cv c) C)
      (.classMem D (synCfv
          (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn (.cv c))))
          (synCtc N)))
      (.classMem D
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc N)))
      (synWbr (.cv c) (synClec) (synCfv (synCfrec F D) N))
      (synWbr C (synClec) (synCfv (synCfrec F D) N)) p0008 p0010
  have p0012 :=
    @gImbi2d (.classEq (.cv c) C)
      (synWb (.classMem D (synCfv
            (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn (.cv c))))
            (synCtc N))) (synWbr (.cv c) (synClec) (synCfv (synCfrec F D) N)))
      (synWb (.classMem D
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc N))) (synWbr C (synClec) (synCfv (synCfrec F D) N)))
      (.classMem N (synCnnc)) p0011
  have p0013 :=
    @gWppreachlayerorbfin (.cv c) D F N dv_cache_0001 hyp_wppreachlayerorbvndv_1
      hyp_wppreachlayerorbvndv_2 hyp_wppreachlayerorbvndv_3
  have p0014 :=
    @gVtoclg
      (.imp (.classMem N (synCnnc)) (synWb (.classMem D (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn (.cv c))))
              (synCtc N))) (synWbr (.cv c) (synClec) (synCfv (synCfrec F D) N))))
      (.imp (.classMem N (synCnnc)) (synWb (.classMem D (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc N))) (synWbr C (synClec) (synCfv (synCfrec F D) N))))
      c C (synCvv) dv_cache_0002 dv_cache_0003 p0012 p0013
  have p0015 := Nominal.mp hyp_wppreachlayerorbvndv_4 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_wppreachlayerorbrexvndv`. -/
@[expose]
noncomputable def gWppreachlayerorbrexvndv (C : Class) (D : Class) (n : Var) (F : Class)
    (_dv_C_n : n ∉ C.fv) (_dv_D_n : n ∉ D.fv) (_dv_F_n : n ∉ F.fv)
    (hyp_wppreachlayerorbrexvndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppreachlayerorbrexvndv_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wppreachlayerorbrexvndv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppreachlayerorbrexvndv_4 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (synWrex n (synCnnc) (.classMem D (synCfv
              (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
              (synCtc (.cv n))))) (synWrex n (synCnnc)
          (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))))) :=
  by
  have p0000 :=
    @gWppreachlayerorbvndv C D F (.cv n) hyp_wppreachlayerorbrexvndv_1
      hyp_wppreachlayerorbrexvndv_2 hyp_wppreachlayerorbrexvndv_3
      hyp_wppreachlayerorbrexvndv_4
  have p0001 :=
    @gRexbiia
      (.classMem D
        (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
          (synCtc (.cv n))))
      (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))) n (synCnnc) p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_wppreachfwdrexvndv`. -/
@[expose]
noncomputable def gWppreachfwdrexvndv (C : Class) (D : Class) (n : Var) (F : Class)
    (dv_C_n : n ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_F_n : n ∉ F.fv)
    (hyp_wppreachfwdrexvndv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppreachfwdrexvndv_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wppreachfwdrexvndv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppreachfwdrexvndv_4 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem D (synCwppreach F C)) (synWrex n (synCnnc)
          (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))))) :=
  by
  have dv_cache_0001 : n ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0002 : n ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_n, not_false_eq_true])
  have dv_cache_0003 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_n, not_false_eq_true])
  have p0000 := @gElex F (synCfuns)
  have p0001 := Nominal.mp hyp_wppreachfwdrexvndv_1 p0000
  have p0002 :=
    @gWppreachtcrexvndv C D n F dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @gWppreachlayerorbrexvndv C D n F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppreachfwdrexvndv_1 hyp_wppreachfwdrexvndv_2 hyp_wppreachfwdrexvndv_3
      hyp_wppreachfwdrexvndv_4
  have p0004 :=
    @gBitri (.classMem D (synCwppreach F C))
      (synWrex n (synCnnc) (.classMem D
          (synCfv (synCfrec (synCimage (synCcnv F)) (synCima (synClec) (synCsn C)))
            (synCtc (.cv n)))))
      (synWrex n (synCnnc) (synWbr C (synClec) (synCfv (synCfrec F D) (.cv n))))
      p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_wppreachtcbidv`. -/
@[expose]
noncomputable def gWppreachtcbidv (x : Var) (C : Class) (D : Class) (F : Class)
    (G : Class) (r : Var) (dv_D_r : r ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_F_r : r ∉ F.fv)
    (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv)
    (hyp_wppreachtcbidv_1 : Nominal.NPrf (.classMem F (synCfuns)))
    (hyp_wppreachtcbidv_2 : Nominal.NPrf (.classMem D (synCdm F)))
    (hyp_wppreachtcbidv_3 : Nominal.NPrf (synWss (synCrn F) (synCdm F)))
    (hyp_wppreachtcbidv_4 : Nominal.NPrf (.classMem G (synCfuns)))
    (hyp_wppreachtcbidv_5 : Nominal.NPrf (.classMem (synCtc D) (synCdm G)))
    (hyp_wppreachtcbidv_6 : Nominal.NPrf (synWss (synCrn G) (synCdm G)))
    (hyp_wppreachtcbidv_7 : Nominal.NPrf (synWral x (synCdm F)
          (.classEq (synCtc (synCfv F (.cv x))) (synCfv G (synCtc (.cv x))))))
    (hyp_wppreachtcbidv_8 : Nominal.NPrf (.classMem C (synCncs)))
    (hyp_wppreachtcbidv_9 : Nominal.NPrf (synWral r (synCnnc)
          (.classMem (synCfv (synCfrec F D) (.cv r)) (synCncs)))) :
    Nominal.NPrf
      (synWb (.classMem D (synCwppreach F C))
        (.classMem (synCtc D) (synCwppreach G (synCtc C)))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ C.fv ∪ D.fv ∪ F.fv ∪ G.fv ∪ ({ r } : Finset Var)
  let p : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_p_not_D : p ∉ D.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_p_not_F : p ∉ F.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_p_not_G : p ∉ G.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_a_not_D : a ∉ D.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_a_not_F : a ∉ F.fv := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_a_not_G : a ∉ G.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_a_ne_r : a ≠ r := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_a : p ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_p : a ≠ p := Ne.symm fresh_p_ne_a
  have dv_cache_0001 : a ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_C, not_false_eq_true])
  have dv_cache_0002 : a ∉ (D).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_D, not_false_eq_true])
  have dv_cache_0003 : a ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_F, not_false_eq_true])
  have dv_cache_0004 : p ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_C, not_false_eq_true])
  have dv_cache_0005 : p ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_D, not_false_eq_true])
  have dv_cache_0006 : r ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_r, not_false_eq_true])
  have dv_cache_0007 : x ∉ (D).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_D_x, not_false_eq_true])
  have dv_cache_0008 : p ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_F, not_false_eq_true])
  have dv_cache_0009 : r ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_r, not_false_eq_true])
  have dv_cache_0010 : x ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_x, not_false_eq_true])
  have dv_cache_0011 : a ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_G, not_false_eq_true])
  have dv_cache_0012 : p ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_G, not_false_eq_true])
  have dv_cache_0013 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_x, not_false_eq_true])
  have dv_cache_0014 : a ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show a ≠ p from (by exact fresh_a_ne_p))
  have dv_cache_0015 : a ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show a ≠ r from (by exact fresh_a_ne_r))
  have dv_cache_0016 : p ∉ ((synCtc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_p_not_C,
          not_false_eq_true])
  have dv_cache_0017 : p ∉ ((synCtc D)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_p_not_D,
          not_false_eq_true])
  have p0000 := @gElex C (synCncs)
  have p0001 := Nominal.mp hyp_wppreachtcbidv_8 p0000
  have p0002 :=
    @gWppreachfwdrexvndv C D a F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppreachtcbidv_1 hyp_wppreachtcbidv_2 hyp_wppreachtcbidv_3 p0001
  have p0003 :=
    @gWppreachorbitextcbidv x C D F G r p a dv_cache_0001 dv_cache_0004 dv_cache_0002
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      hyp_wppreachtcbidv_1 hyp_wppreachtcbidv_2 hyp_wppreachtcbidv_3 hyp_wppreachtcbidv_4
      hyp_wppreachtcbidv_5 hyp_wppreachtcbidv_6 hyp_wppreachtcbidv_7 hyp_wppreachtcbidv_8
      hyp_wppreachtcbidv_9
  have p0004 :=
    @gBitri (.classMem D (synCwppreach F C))
      (synWrex a (synCnnc) (synWbr C (synClec) (synCfv (synCfrec F D) (.cv a))))
      (synWrex p (synCnnc)
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      p0002 p0003
  have p0005 := @gTccl C
  have p0006 := Nominal.mp hyp_wppreachtcbidv_8 p0005
  have p0007 := @gElex (synCtc C) (synCncs)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gWppreachfwdrexvndv (synCtc C) (synCtc D) p G dv_cache_0016 dv_cache_0017
      dv_cache_0012 hyp_wppreachtcbidv_4 hyp_wppreachtcbidv_5 hyp_wppreachtcbidv_6 p0008
  have p0010 :=
    @gBitr4i (.classMem D (synCwppreach F C))
      (synWrex p (synCnnc)
        (synWbr (synCtc C) (synClec) (synCfv (synCfrec G (synCtc D)) (.cv p))))
      (.classMem (synCtc D) (synCwppreach G (synCtc C))) p0004 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_elhwcardsweclndv`. -/
@[expose]
noncomputable def gElhwcardsweclndv (K : Class) (s : Var) (d : Var) (dv_K_d : d ∉ K.fv)
    (dv_K_s : s ∉ K.fv) (dv_d_s : d ≠ s) :
    Nominal.NPrf
      (.imp (.classMem K (synCvv)) (synWb (.classMem K (synChwcards (synCvv))) (synWex d
            (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
                (.classEq K (synCnc (.cv d)))))))) :=
  by
  let proofSupport : Finset Var := K.fv ∪ ({ s } : Finset Var) ∪ ({ d } : Finset Var)
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_K : k ∉ K.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_k_ne_s : k ≠ s := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_s_ne_k : s ≠ k := Ne.symm fresh_k_ne_s
  have fresh_k_ne_d : k ≠ d := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_k : d ≠ k := Ne.symm fresh_k_ne_d
  have dv_cache_0001 : s ∉ ((Wff.classEq (.cv k) K)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_k, dv_K_s, or_false, not_false_eq_true])
  have dv_cache_0002 : d ∉ ((Wff.classEq (.cv k) K)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_k, dv_K_d, or_false, not_false_eq_true])
  have dv_cache_0003 : d ≠ k :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ k from (by exact fresh_d_ne_k))
  have dv_cache_0004 : d ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show d ≠ s from (by exact dv_d_s))
  have dv_cache_0005 : k ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show k ≠ s from (by exact fresh_k_ne_s))
  have dv_cache_0006 : k ∉ (K).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_K, not_false_eq_true])
  have dv_cache_0007 :
    k ∉
      ((synWb (.classMem K (synChwcards (synCvv))) (synWex d (synWex s
              (synWa (synWbr (.cv s) (synCwe) (.cv d))
                (.classEq K (synCnc (.cv d)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_not_K, fresh_k_ne_s,
          fresh_k_ne_d, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @gId (.classEq (.cv k) K)
  have p0001 := @gEleq1d (.classEq (.cv k) K) (.cv k) K (synChwcards (synCvv)) p0000
  have p0003 := @gEqeq1d (.classEq (.cv k) K) (.cv k) K (synCnc (.cv d)) p0000
  have p0004 :=
    @gAnbi2d (.classEq (.cv k) K) (.classEq (.cv k) (synCnc (.cv d)))
      (.classEq K (synCnc (.cv d))) (synWbr (.cv s) (synCwe) (.cv d)) p0003
  have p0005 :=
    @gExbidv (.classEq (.cv k) K)
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d))))
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))) s
      dv_cache_0001 p0004
  have p0006 :=
    @gExbidv (.classEq (.cv k) K)
      (synWex s
        (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d)))))
      (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))
      d dv_cache_0002 p0005
  have p0007 :=
    @gBibi12d (.classEq (.cv k) K) (.classMem (.cv k) (synChwcards (synCvv)))
      (.classMem K (synChwcards (synCvv)))
      (synWex d (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv d))
            (.classEq (.cv k) (synCnc (.cv d))))))
      (synWex d (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))))
      p0001 p0006
  have p0008 := @gElhwcardswev k s d dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 :=
    @gVtoclg
      (synWb (.classMem (.cv k) (synChwcards (synCvv))) (synWex d (synWex s
            (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq (.cv k) (synCnc (.cv d)))))))
      (synWb (.classMem K (synChwcards (synCvv))) (synWex d (synWex s
            (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))))
      k K (synCvv) dv_cache_0006 dv_cache_0007 p0007 p0008
  exact p0009


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part046`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_hwcardstcclndv`. -/
@[expose]
noncomputable def gHwcardstcclndv (K : Class) :
    Nominal.NPrf
      (.imp (.classMem K (synChwcards (synCvv)))
        (.classMem (synCtc K) (synChwcards (synCvv)))) :=
  by
  let proofSupport : Finset Var := K.fv
  let s : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  let x : Var := freshVar proofSupport 3
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_s_not_K : s ∉ K.fv := by
    intro h
    exact fresh_s (h)
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_K : d ∉ K.fv := by
    intro h
    exact fresh_d (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_y_not_K : y ∉ K.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_x_not_K : x ∉ K.fv := by
    intro h
    exact fresh_x (h)
  have fresh_s_ne_d : s ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_s : d ≠ s := Ne.symm fresh_s_ne_d
  have fresh_s_ne_y : s ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_s : y ≠ s := Ne.symm fresh_s_ne_y
  have fresh_d_ne_y : d ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_d : y ≠ d := Ne.symm fresh_d_ne_y
  have fresh_d_ne_x : d ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_x_ne_d : x ≠ d := Ne.symm fresh_d_ne_x
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : d ∉ (K).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_K, not_false_eq_true])
  have dv_cache_0002 : s ∉ (K).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_K, not_false_eq_true])
  have dv_cache_0003 : d ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0004 : y ∉ ((synCsi (.cv s))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_s,
          not_false_eq_true])
  have dv_cache_0005 :
    y ∉
      ((synWa (synWbr (synCsi (.cv s)) (synCwe) (synCpw1 (.cv d)))
          (.classEq (synCtc K) (synCnc (synCpw1 (.cv d)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_s, fresh_y_ne_d, fresh_y_not_K,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv x) (synCpw1 (.cv d)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_d, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synCpw1 (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_d,
          not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((synWex y (synWa (synWbr (.cv y) (synCwe) (synCpw1 (.cv d)))
            (.classEq (synCtc K) (synCnc (synCpw1 (.cv d))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_d,
          fresh_x_not_K, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCtc K)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_x_not_K,
          not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synCtc K)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_y_not_K,
          not_false_eq_true])
  have dv_cache_0011 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0012 : d ∉ ((Wff.classMem (synCtc K) (synChwcards (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_d_not_K, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : s ∉ ((Wff.classMem (synCtc K) (synChwcards (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_s_not_K, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gId (.classMem K (synChwcards (synCvv)))
  have p0002 := @gElex K (synChwcards (synCvv))
  have p0003 :=
    @gSyl (.classMem K (synChwcards (synCvv))) (.classMem K (synChwcards (synCvv)))
      (.classMem K (synCvv)) p0000 p0002
  have p0004 := @gElhwcardsweclndv K s d dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    @gSyl (.classMem K (synChwcards (synCvv))) (.classMem K (synCvv))
      (synWb (.classMem K (synChwcards (synCvv))) (synWex d (synWex s
            (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))))))
      p0003 p0004
  have p0006 :=
    @gMpbid (.classMem K (synChwcards (synCvv))) (.classMem K (synChwcards (synCvv)))
      (synWex d (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))))
      p0000 p0005
  have p0007 :=
    @gSimpl (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))
  have p0008 := @gSiwendv (.cv d) (.cv s)
  have p0009 :=
    @gSyl (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synWbr (.cv s) (synCwe) (.cv d))
      (synWbr (synCsi (.cv s)) (synCwe) (synCpw1 (.cv d))) p0007 p0008
  have p0010 :=
    @gSimpr (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d)))
  have p0011 := @gTceq K (synCnc (.cv d))
  have p0012 :=
    @gSyl (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (.classEq K (synCnc (.cv d))) (.classEq (synCtc K) (synCtc (synCnc (.cv d))))
      p0010 p0011
  have p0014 := @gBrex (.cv s) (.cv d) (synCwe)
  have p0015 := @gSimpr (.classMem (.cv s) (synCvv)) (.classMem (.cv d) (synCvv))
  have p0016 :=
    @gSyl (synWbr (.cv s) (synCwe) (.cv d))
      (synWa (.classMem (.cv s) (synCvv)) (.classMem (.cv d) (synCvv)))
      (.classMem (.cv d) (synCvv)) p0014 p0015
  have p0017 :=
    @gSyl (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synWbr (.cv s) (synCwe) (.cv d)) (.classMem (.cv d) (synCvv)) p0007 p0016
  have p0018 := @gTcncg (.cv d) (synCvv)
  have p0019 :=
    @gSyl (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (.classMem (.cv d) (synCvv))
      (.classEq (synCtc (synCnc (.cv d))) (synCnc (synCpw1 (.cv d)))) p0017 p0018
  have p0020 :=
    @gEqtrd (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synCtc K) (synCtc (synCnc (.cv d))) (synCnc (synCpw1 (.cv d))) p0012 p0019
  have p0021 :=
    @gJca (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synWbr (synCsi (.cv s)) (synCwe) (synCpw1 (.cv d)))
      (.classEq (synCtc K) (synCnc (synCpw1 (.cv d)))) p0009 p0020
  have p0024 := @gSimpl (.classMem (.cv s) (synCvv)) (.classMem (.cv d) (synCvv))
  have p0025 :=
    @gSyl (synWbr (.cv s) (synCwe) (.cv d))
      (synWa (.classMem (.cv s) (synCvv)) (.classMem (.cv d) (synCvv)))
      (.classMem (.cv s) (synCvv)) p0014 p0024
  have p0026 :=
    @gSyl (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synWbr (.cv s) (synCwe) (.cv d)) (.classMem (.cv s) (synCvv)) p0007 p0025
  have p0027 := @gSiexg (.cv s) (synCvv)
  have p0028 :=
    @gSyl (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (.classMem (.cv s) (synCvv)) (.classMem (synCsi (.cv s)) (synCvv)) p0026 p0027
  have p0029 := @gId (.classEq (.cv y) (synCsi (.cv s)))
  have p0030 :=
    @gBreq1d (.classEq (.cv y) (synCsi (.cv s))) (.cv y) (synCsi (.cv s))
      (synCpw1 (.cv d)) (synCwe) p0029
  have p0031 :=
    @gAnbi1d (.classEq (.cv y) (synCsi (.cv s)))
      (synWbr (.cv y) (synCwe) (synCpw1 (.cv d)))
      (synWbr (synCsi (.cv s)) (synCwe) (synCpw1 (.cv d)))
      (.classEq (synCtc K) (synCnc (synCpw1 (.cv d)))) p0030
  have p0032 :=
    @gSpcegv
      (synWa (synWbr (.cv y) (synCwe) (synCpw1 (.cv d)))
        (.classEq (synCtc K) (synCnc (synCpw1 (.cv d)))))
      (synWa (synWbr (synCsi (.cv s)) (synCwe) (synCpw1 (.cv d)))
        (.classEq (synCtc K) (synCnc (synCpw1 (.cv d)))))
      y (synCsi (.cv s)) (synCvv) dv_cache_0004 dv_cache_0005 p0031
  have p0033 :=
    @gSyl (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (.classMem (synCsi (.cv s)) (synCvv))
      (.imp (synWa (synWbr (synCsi (.cv s)) (synCwe) (synCpw1 (.cv d)))
          (.classEq (synCtc K) (synCnc (synCpw1 (.cv d))))) (synWex y
          (synWa (synWbr (.cv y) (synCwe) (synCpw1 (.cv d)))
            (.classEq (synCtc K) (synCnc (synCpw1 (.cv d)))))))
      p0028 p0032
  have p0034 :=
    @gMpd (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synWa (synWbr (synCsi (.cv s)) (synCwe) (synCpw1 (.cv d)))
        (.classEq (synCtc K) (synCnc (synCpw1 (.cv d)))))
      (synWex y (synWa (synWbr (.cv y) (synCwe) (synCpw1 (.cv d)))
          (.classEq (synCtc K) (synCnc (synCpw1 (.cv d))))))
      p0021 p0033
  have p0040 := @gPw1exg (.cv d) (synCvv)
  have p0041 :=
    @gSyl (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (.classMem (.cv d) (synCvv)) (.classMem (synCpw1 (.cv d)) (synCvv)) p0017 p0040
  have p0042 := @gId (.classEq (.cv x) (synCpw1 (.cv d)))
  have p0043 :=
    @gBreq2d (.classEq (.cv x) (synCpw1 (.cv d))) (.cv x) (synCpw1 (.cv d)) (.cv y)
      (synCwe) p0042
  have p0045 :=
    @gNceqd (.classEq (.cv x) (synCpw1 (.cv d))) (.cv x) (synCpw1 (.cv d)) p0042
  have p0046 :=
    @gEqeq2d (.classEq (.cv x) (synCpw1 (.cv d))) (synCnc (.cv x))
      (synCnc (synCpw1 (.cv d))) (synCtc K) p0045
  have p0047 :=
    @gAnbi12d (.classEq (.cv x) (synCpw1 (.cv d))) (synWbr (.cv y) (synCwe) (.cv x))
      (synWbr (.cv y) (synCwe) (synCpw1 (.cv d)))
      (.classEq (synCtc K) (synCnc (.cv x)))
      (.classEq (synCtc K) (synCnc (synCpw1 (.cv d)))) p0043 p0046
  have p0048 :=
    @gExbidv (.classEq (.cv x) (synCpw1 (.cv d)))
      (synWa (synWbr (.cv y) (synCwe) (.cv x)) (.classEq (synCtc K) (synCnc (.cv x))))
      (synWa (synWbr (.cv y) (synCwe) (synCpw1 (.cv d)))
        (.classEq (synCtc K) (synCnc (synCpw1 (.cv d)))))
      y dv_cache_0006 p0047
  have p0049 :=
    @gSpcegv
      (synWex y (synWa (synWbr (.cv y) (synCwe) (.cv x))
          (.classEq (synCtc K) (synCnc (.cv x)))))
      (synWex y (synWa (synWbr (.cv y) (synCwe) (synCpw1 (.cv d)))
          (.classEq (synCtc K) (synCnc (synCpw1 (.cv d))))))
      x (synCpw1 (.cv d)) (synCvv) dv_cache_0007 dv_cache_0008 p0048
  have p0050 :=
    @gSyl (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (.classMem (synCpw1 (.cv d)) (synCvv))
      (.imp (synWex y (synWa (synWbr (.cv y) (synCwe) (synCpw1 (.cv d)))
            (.classEq (synCtc K) (synCnc (synCpw1 (.cv d)))))) (synWex x (synWex y
            (synWa (synWbr (.cv y) (synCwe) (.cv x))
              (.classEq (synCtc K) (synCnc (.cv x)))))))
      p0041 p0049
  have p0051 :=
    @gMpd (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synWex y (synWa (synWbr (.cv y) (synCwe) (synCpw1 (.cv d)))
          (.classEq (synCtc K) (synCnc (synCpw1 (.cv d))))))
      (synWex x (synWex y (synWa (synWbr (.cv y) (synCwe) (.cv x))
            (.classEq (synCtc K) (synCnc (.cv x))))))
      p0034 p0050
  have p0052 := @gTcex K
  have p0053 :=
    @gElhwcardsweclndv (synCtc K) y x dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0054 := Nominal.mp p0052 p0053
  have p0055 :=
    @gBiimpri (.classMem (synCtc K) (synChwcards (synCvv)))
      (synWex x (synWex y (synWa (synWbr (.cv y) (synCwe) (.cv x))
            (.classEq (synCtc K) (synCnc (.cv x))))))
      p0054
  have p0056 :=
    @gSyl (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (synWex x (synWex y (synWa (synWbr (.cv y) (synCwe) (.cv x))
            (.classEq (synCtc K) (synCnc (.cv x))))))
      (.classMem (synCtc K) (synChwcards (synCvv))) p0051 p0055
  have p0057 :=
    @gExlimivv
      (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))
      (.classMem (synCtc K) (synChwcards (synCvv))) d s dv_cache_0012 dv_cache_0013
      p0056
  have p0058 :=
    @gSyl (.classMem K (synChwcards (synCvv)))
      (synWex d (synWex s
          (synWa (synWbr (.cv s) (synCwe) (.cv d)) (.classEq K (synCnc (.cv d))))))
      (.classMem (synCtc K) (synChwcards (synCvv))) p0006 p0057
  exact p0058

/-- Checked nominal proof certificate identified upstream as `g_hwcardsdownltcndv`. -/
@[expose]
noncomputable def gHwcardsdownltcndv (C : Class) (d : Var) :
    Nominal.NPrf
      (.imp (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C)) (.classMem (.cv d) (synChwcards (synCvv)))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ ({ d } : Finset Var)
  let r : Var := freshVar proofSupport 0
  let e : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let s : Var := freshVar proofSupport 3
  let a : Var := freshVar proofSupport 4
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_ne_d : r ≠ d := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_e_not_C : e ∉ C.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (h))
  have fresh_e_ne_d : e ≠ d := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_ne_d : x ≠ d := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_s_ne_d : s ≠ d := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d_ne_s : d ≠ s := Ne.symm fresh_s_ne_d
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_a_ne_d : a ≠ d := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_e : r ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_e_ne_r : e ≠ r := Ne.symm fresh_r_ne_e
  have fresh_r_ne_x : r ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
  have fresh_r_ne_s : r ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_s_ne_r : s ≠ r := Ne.symm fresh_r_ne_s
  have fresh_r_ne_a : r ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_r : a ≠ r := Ne.symm fresh_r_ne_a
  have fresh_e_ne_x : e ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_e : x ≠ e := Ne.symm fresh_e_ne_x
  have fresh_x_ne_s : x ≠ s :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_s_ne_x : s ≠ x := Ne.symm fresh_x_ne_s
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_s_ne_a : s ≠ a :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_a_ne_s : a ≠ s := Ne.symm fresh_s_ne_a
  have dv_cache_0001 : e ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_C, not_false_eq_true])
  have dv_cache_0002 : r ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_C, not_false_eq_true])
  have dv_cache_0003 : e ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show e ≠ r from (by exact fresh_e_ne_r))
  have dv_cache_0004 : x ∉ ((Class.cv e)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_e, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_d, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0007 : s ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_s_ne_x, not_false_eq_true])
  have dv_cache_0008 : a ∉ ((synCin (.cv r) (synCxp (.cv x) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_r, fresh_a_ne_x, or_false, not_false_eq_true])
  have dv_cache_0009 : s ∉ ((synCin (.cv r) (synCxp (.cv x) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_r, fresh_s_ne_x, or_false, not_false_eq_true])
  have dv_cache_0010 :
    a ∉
      ((synWa (synWbr (synCin (.cv r) (synCxp (.cv x) (.cv x))) (synCwe) (.cv x))
          (.classEq (.cv d) (synCnc (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_r, fresh_a_ne_x, fresh_a_ne_d,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    s ∉
      ((synWa (synWbr (synCin (.cv r) (synCxp (.cv x) (.cv x))) (synCwe) (.cv x))
          (.classEq (.cv d) (synCnc (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_r, fresh_s_ne_x, fresh_s_ne_d,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : a ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show a ≠ s from (by exact fresh_a_ne_s))
  have dv_cache_0013 : a ≠ d :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show a ≠ d from (by exact fresh_a_ne_d))
  have dv_cache_0014 : d ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show d ≠ s from (by exact fresh_d_ne_s))
  have dv_cache_0015 : x ∉ ((Wff.classMem (.cv d) (synChwcards (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_d, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 :
    x ∉
      ((synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C)) (synWa (synWbr (.cv r) (synCwe) (.cv e))
            (.classEq C (synCnc (.cv e)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_d, fresh_x_not_C, fresh_x_ne_r, fresh_x_ne_e,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : e ∉ ((Wff.classMem (.cv d) (synChwcards (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_e_ne_d, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0018 : r ∉ ((Wff.classMem (.cv d) (synChwcards (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_d, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0019 :
    e ∉
      ((synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_e_ne_d, fresh_e_not_C, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0020 :
    r ∉
      ((synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_d, fresh_r_not_C, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    @gSimpl
      (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
      (synWbr (.cv d) (synClec) C)
  have p0001 :=
    @gSimpr (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv)))
  have p0002 :=
    @gSyl
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
      (.classMem C (synChwcards (synCvv))) p0000 p0001
  have p0006 := @gElex C (synChwcards (synCvv))
  have p0007 :=
    @gSyl
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (.classMem C (synChwcards (synCvv))) (.classMem C (synCvv)) p0002 p0006
  have p0008 := @gElhwcardsweclndv C r e dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @gSyl
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (.classMem C (synCvv))
      (synWb (.classMem C (synChwcards (synCvv))) (synWex e (synWex r
            (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))))
      p0007 p0008
  have p0010 :=
    @gMpbid
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (.classMem C (synChwcards (synCvv)))
      (synWex e (synWex r
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e))))))
      p0002 p0009
  have p0011 :=
    @gSimpl
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e))))
  have p0012 :=
    @gSimpr
      (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
      (synWbr (.cv d) (synClec) C)
  have p0013 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (synWbr (.cv d) (synClec) C) p0011 p0012
  have p0014 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e))))
  have p0015 :=
    @gSimpr (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))
  have p0016 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e))))
      (.classEq C (synCnc (.cv e))) p0014 p0015
  have p0017 :=
    @gBreq2d
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      C (synCnc (.cv e)) (.cv d) (synClec) p0016
  have p0018 :=
    @gMpbid
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWbr (.cv d) (synClec) C) (synWbr (.cv d) (synClec) (synCnc (.cv e))) p0013
      p0017
  have p0021 :=
    @gSimpl (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv)))
  have p0022 :=
    @gSyl
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
      (.classMem (.cv d) (synCncs)) p0000 p0021
  have p0023 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (.classMem (.cv d) (synCncs)) p0011 p0022
  have p0024 := @gVex e
  have p0025 := @gLenc x (.cv e) (.cv d) dv_cache_0004 dv_cache_0005 p0024
  have p0026 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (.classMem (.cv d) (synCncs))
      (synWb (synWbr (.cv d) (synClec) (synCnc (.cv e)))
        (synWrex x (.cv d) (synWss (.cv x) (.cv e))))
      p0023 p0025
  have p0027 :=
    @gMpbid
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWbr (.cv d) (synClec) (synCnc (.cv e)))
      (synWrex x (.cv d) (synWss (.cv x) (.cv e))) p0018 p0026
  have p0028 :=
    @gSimpl
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e)))
  have p0030 :=
    @gSimpl (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))
  have p0031 :=
    @gSyl
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e))))
      (synWbr (.cv r) (synCwe) (.cv e)) p0014 p0030
  have p0032 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWbr (.cv r) (synCwe) (.cv e)) p0028 p0031
  have p0033 :=
    @gSimpr
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e)))
  have p0034 := @gSimpr (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))
  have p0035 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e)))
      (synWss (.cv x) (.cv e)) p0033 p0034
  have p0036 := @gVex x
  have p0037 :=
    @gA1i (.classMem (.cv x) (synCvv))
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      p0036
  have p0038 :=
    @gWerestrndv
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      (.cv x) (.cv e) (.cv r) p0032 p0035 p0037
  have p0040 := @gSimpl (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))
  have p0041 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e)))
      (.classMem (.cv x) (.cv d)) p0033 p0040
  have p0048 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (.classMem (.cv d) (synCncs)) p0028 p0023
  have p0049 := @gNcseqnc (.cv d) (.cv x)
  have p0050 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      (.classMem (.cv d) (synCncs))
      (synWb (.classEq (.cv d) (synCnc (.cv x))) (.classMem (.cv x) (.cv d))) p0048
      p0049
  have p0051 :=
    @gMpbird
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      (.classEq (.cv d) (synCnc (.cv x))) (.classMem (.cv x) (.cv d)) p0041 p0050
  have p0052 :=
    @gJca
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      (synWbr (synCin (.cv r) (synCxp (.cv x) (.cv x))) (synCwe) (.cv x))
      (.classEq (.cv d) (synCnc (.cv x))) p0038 p0051
  have p0054 := @gVex r
  have p0057 := @gXpex (.cv x) (.cv x) p0036 p0036
  have p0058 := @gInex (.cv r) (synCxp (.cv x) (.cv x)) p0054 p0057
  have p0059 :=
    @gPm32i (.classMem (.cv x) (synCvv))
      (.classMem (synCin (.cv r) (synCxp (.cv x) (.cv x))) (synCvv)) p0036 p0058
  have p0060 :=
    @gSimpr (.classEq (.cv a) (.cv x))
      (.classEq (.cv s) (synCin (.cv r) (synCxp (.cv x) (.cv x))))
  have p0061 :=
    @gSimpl (.classEq (.cv a) (.cv x))
      (.classEq (.cv s) (synCin (.cv r) (synCxp (.cv x) (.cv x))))
  have p0062 :=
    @gBreq12d
      (synWa (.classEq (.cv a) (.cv x))
        (.classEq (.cv s) (synCin (.cv r) (synCxp (.cv x) (.cv x)))))
      (.cv s) (synCin (.cv r) (synCxp (.cv x) (.cv x))) (.cv a) (.cv x) (synCwe) p0060
      p0061
  have p0064 :=
    @gNceqd
      (synWa (.classEq (.cv a) (.cv x))
        (.classEq (.cv s) (synCin (.cv r) (synCxp (.cv x) (.cv x)))))
      (.cv a) (.cv x) p0061
  have p0065 :=
    @gEqeq2d
      (synWa (.classEq (.cv a) (.cv x))
        (.classEq (.cv s) (synCin (.cv r) (synCxp (.cv x) (.cv x)))))
      (synCnc (.cv a)) (synCnc (.cv x)) (.cv d) p0064
  have p0066 :=
    @gAnbi12d
      (synWa (.classEq (.cv a) (.cv x))
        (.classEq (.cv s) (synCin (.cv r) (synCxp (.cv x) (.cv x)))))
      (synWbr (.cv s) (synCwe) (.cv a))
      (synWbr (synCin (.cv r) (synCxp (.cv x) (.cv x))) (synCwe) (.cv x))
      (.classEq (.cv d) (synCnc (.cv a))) (.classEq (.cv d) (synCnc (.cv x))) p0062
      p0065
  have p0067 :=
    @gSpc2egv
      (synWa (synWbr (.cv s) (synCwe) (.cv a)) (.classEq (.cv d) (synCnc (.cv a))))
      (synWa (synWbr (synCin (.cv r) (synCxp (.cv x) (.cv x))) (synCwe) (.cv x))
        (.classEq (.cv d) (synCnc (.cv x))))
      a s (.cv x) (synCin (.cv r) (synCxp (.cv x) (.cv x))) (synCvv) (synCvv)
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0066
  have p0068 := Nominal.mp p0059 p0067
  have p0069 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      (synWa (synWbr (synCin (.cv r) (synCxp (.cv x) (.cv x))) (synCwe) (.cv x))
        (.classEq (.cv d) (synCnc (.cv x))))
      (synWex a (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv a))
            (.classEq (.cv d) (synCnc (.cv a))))))
      p0052 p0068
  have p0070 := @gElhwcardswev d s a dv_cache_0013 dv_cache_0012 dv_cache_0014
  have p0071 :=
    @gBiimpri (.classMem (.cv d) (synChwcards (synCvv)))
      (synWex a (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv a))
            (.classEq (.cv d) (synCnc (.cv a))))))
      p0070
  have p0072 :=
    @gSyl
      (synWa (synWa (synWa
            (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
            (synWbr (.cv d) (synClec) C))
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
        (synWa (.classMem (.cv x) (.cv d)) (synWss (.cv x) (.cv e))))
      (synWex a (synWex s (synWa (synWbr (.cv s) (synCwe) (.cv a))
            (.classEq (.cv d) (synCnc (.cv a))))))
      (.classMem (.cv d) (synChwcards (synCvv))) p0069 p0071
  have p0073 :=
    @gRexlimdvaa
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWss (.cv x) (.cv e)) (.classMem (.cv d) (synChwcards (synCvv))) x (.cv d)
      dv_cache_0015 dv_cache_0016 p0072
  have p0074 :=
    @gMpd
      (synWa (synWa
          (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
          (synWbr (.cv d) (synClec) C))
        (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e)))))
      (synWrex x (.cv d) (synWss (.cv x) (.cv e)))
      (.classMem (.cv d) (synChwcards (synCvv))) p0027 p0073
  have p0075 :=
    @gEx
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e))))
      (.classMem (.cv d) (synChwcards (synCvv))) p0074
  have p0076 :=
    @gExlimdvv
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e))))
      (.classMem (.cv d) (synChwcards (synCvv))) e r dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 p0075
  have p0077 :=
    @gMpd
      (synWa (synWa (.classMem (.cv d) (synCncs)) (.classMem C (synChwcards (synCvv))))
        (synWbr (.cv d) (synClec) C))
      (synWex e (synWex r
          (synWa (synWbr (.cv r) (synCwe) (.cv e)) (.classEq C (synCnc (.cv e))))))
      (.classMem (.cv d) (synChwcards (synCvv))) p0010 p0076
  exact p0077


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk016Compact001Part047`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_wppgammaimagetceqndv`. -/
@[expose]
noncomputable def gWppgammaimagetceqndv (C : Class) (k : Var) (F : Class) (G : Class)
    (d : Var) (dv_C_d : d ∉ C.fv) (dv_C_k : k ∉ C.fv) (dv_F_d : d ∉ F.fv)
    (dv_F_k : k ∉ F.fv) (_dv_G_d : d ∉ G.fv) (dv_G_k : k ∉ G.fv) (dv_d_k : d ≠ k)
    (hyp_wppgammaimagetceqndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_wppgammaimagetceqndv_2 : Nominal.NPrf (.classMem C (synChwcards (synCvv))))
    (hyp_wppgammaimagetceqndv_3 : Nominal.NPrf (.classMem G (synCvv)))
    (hyp_wppgammaimagetceqndv_4 : Nominal.NPrf (.classMem (synCtc C) (synChwcards (synCvv))))
    (hyp_wppgammaimagetceqndv_5 : Nominal.NPrf (.all k
          (synWb (.classMem (.cv k) (synCwppcand G (synCtc C)))
            (synWrex d (synCwppcand F C) (.classEq (.cv k) (synCtc (.cv d))))))) :
    Nominal.NPrf (.classEq (synCtc (synCwppgamma F C)) (synCwppgamma G (synCtc C))) :=
  by
  have dv_cache_0001 : k ∉ ((synCtc C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, dv_C_k,
          not_false_eq_true])
  have dv_cache_0002 : k ∉ (G).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_k, not_false_eq_true])
  have dv_cache_0003 : d ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_d, not_false_eq_true])
  have dv_cache_0004 : d ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_d, not_false_eq_true])
  have dv_cache_0005 : d ∉ ((synCwppgamma F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, dv_C_d, dv_F_d, or_false, not_false_eq_true])
  have dv_cache_0006 : d ∉ ((synCwppcand F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          Finset.mem_union, dv_C_d, dv_F_d, or_false, not_false_eq_true])
  have dv_cache_0007 :
    d ∉ ((Wff.classEq (synCtc (synCwppgamma F C)) (synCtc (synCwppgamma F C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union,
          dv_C_d, dv_F_d, or_false, not_false_eq_true])
  have dv_cache_0008 : d ∉ ((Wff.classEq (.cv k) (synCtc (synCwppgamma F C)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union,
          Finset.mem_singleton, dv_d_k, dv_C_d, dv_F_d, or_false, not_false_eq_true])
  have dv_cache_0009 : k ∉ ((synCtc (synCwppgamma F C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma, Finset.mem_union,
          dv_C_k, dv_F_k, or_false, not_false_eq_true])
  have dv_cache_0010 :
    k ∉
      ((synWb (.classMem (synCtc (synCwppgamma F C)) (synCwppcand G (synCtc C)))
          (synWrex d (synCwppcand F C)
            (.classEq (synCtc (synCwppgamma F C)) (synCtc (.cv d)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppcand,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_C_k, dv_F_k, dv_G_k, (Ne.symm dv_d_k), or_false,
          and_false, not_false_eq_true])
  have dv_cache_0011 :
    d ∉ ((synWbr (synCtc (synCwppgamma F C)) (synClec) (.cv k))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_C_d, dv_F_d, dv_d_k, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0012 : k ∉ ((synCwppgamma G (synCtc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_k,
          dv_G_k, or_false, not_false_eq_true])
  have p0000 :=
    @gPm32i (.classMem G (synCvv)) (.classMem (synCtc C) (synChwcards (synCvv)))
      hyp_wppgammaimagetceqndv_3 hyp_wppgammaimagetceqndv_4
  have p0001 := @gWppgammaminhwndv (synCtc C) k G dv_cache_0001 dv_cache_0002
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gSimpl (.classMem (synCwppgamma G (synCtc C)) (synCwppcand G (synCtc C)))
      (synWral k (synCwppcand G (synCtc C))
        (synWbr (synCwppgamma G (synCtc C)) (synClec) (.cv k)))
  have p0004 := Nominal.mp p0002 p0003
  have p0008 :=
    @gSimpr (.classMem (synCwppgamma G (synCtc C)) (synCwppcand G (synCtc C)))
      (synWral k (synCwppcand G (synCtc C))
        (synWbr (synCwppgamma G (synCtc C)) (synClec) (.cv k)))
  have p0009 := Nominal.mp p0002 p0008
  have p0010 :=
    @gPm32i (.classMem F (synCvv)) (.classMem C (synChwcards (synCvv)))
      hyp_wppgammaimagetceqndv_1 hyp_wppgammaimagetceqndv_2
  have p0011 := @gWppgammaminhwndv C d F dv_cache_0003 dv_cache_0004
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @gSimpl (.classMem (synCwppgamma F C) (synCwppcand F C))
      (synWral d (synCwppcand F C) (synWbr (synCwppgamma F C) (synClec) (.cv d)))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 := @gEqid (synCtc (synCwppgamma F C))
  have p0016 :=
    @gPm32i (.classMem (synCwppgamma F C) (synCwppcand F C))
      (.classEq (synCtc (synCwppgamma F C)) (synCtc (synCwppgamma F C))) p0014 p0015
  have p0017 := @gTceq (.cv d) (synCwppgamma F C)
  have p0018 :=
    @gEqeq2d (.classEq (.cv d) (synCwppgamma F C)) (synCtc (.cv d))
      (synCtc (synCwppgamma F C)) (synCtc (synCwppgamma F C)) p0017
  have p0019 :=
    @gRspcev (.classEq (synCtc (synCwppgamma F C)) (synCtc (.cv d)))
      (.classEq (synCtc (synCwppgamma F C)) (synCtc (synCwppgamma F C))) d
      (synCwppgamma F C) (synCwppcand F C) dv_cache_0005 dv_cache_0006 dv_cache_0007
      p0018
  have p0020 := Nominal.mp p0016 p0019
  have p0026 := @gElwppcand C (synCwppgamma F C) F
  have p0027 :=
    @gBiimpi (.classMem (synCwppgamma F C) (synCwppcand F C))
      (synWa (synWa (.classMem (synCwppgamma F C) (synChwcards (synCvv)))
          (synWbr (synCwppgamma F C) (synClec) C))
        (.classMem (synCwppgamma F C) (synCwppreach F C)))
      p0026
  have p0028 := Nominal.mp p0014 p0027
  have p0029 :=
    @gSimpl
      (synWa (.classMem (synCwppgamma F C) (synChwcards (synCvv)))
        (synWbr (synCwppgamma F C) (synClec) C))
      (.classMem (synCwppgamma F C) (synCwppreach F C))
  have p0030 := Nominal.mp p0028 p0029
  have p0031 :=
    @gSimpl (.classMem (synCwppgamma F C) (synChwcards (synCvv)))
      (synWbr (synCwppgamma F C) (synClec) C)
  have p0032 := Nominal.mp p0030 p0031
  have p0033 := @gHwcardssnc (synCvv)
  have p0034 := @gSseli (synChwcards (synCvv)) (synCncs) (synCwppgamma F C) p0033
  have p0035 := Nominal.mp p0032 p0034
  have p0036 := @gTccl (synCwppgamma F C)
  have p0037 := Nominal.mp p0035 p0036
  have p0038 := @gElex (synCtc (synCwppgamma F C)) (synCncs)
  have p0039 := Nominal.mp p0037 p0038
  have p0040 := @gId (.classEq (.cv k) (synCtc (synCwppgamma F C)))
  have p0041 :=
    @gEleq1d (.classEq (.cv k) (synCtc (synCwppgamma F C))) (.cv k)
      (synCtc (synCwppgamma F C)) (synCwppcand G (synCtc C)) p0040
  have p0043 :=
    @gEqeq1d (.classEq (.cv k) (synCtc (synCwppgamma F C))) (.cv k)
      (synCtc (synCwppgamma F C)) (synCtc (.cv d)) p0040
  have p0044 :=
    @gRexbidv (.classEq (.cv k) (synCtc (synCwppgamma F C)))
      (.classEq (.cv k) (synCtc (.cv d)))
      (.classEq (synCtc (synCwppgamma F C)) (synCtc (.cv d))) d (synCwppcand F C)
      dv_cache_0008 p0043
  have p0045 :=
    @gBibi12d (.classEq (.cv k) (synCtc (synCwppgamma F C)))
      (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (.classMem (synCtc (synCwppgamma F C)) (synCwppcand G (synCtc C)))
      (synWrex d (synCwppcand F C) (.classEq (.cv k) (synCtc (.cv d))))
      (synWrex d (synCwppcand F C) (.classEq (synCtc (synCwppgamma F C)) (synCtc (.cv d))))
      p0041 p0044
  have p0046 :=
    @gSpcv
      (synWb (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWrex d (synCwppcand F C) (.classEq (.cv k) (synCtc (.cv d)))))
      (synWb (.classMem (synCtc (synCwppgamma F C)) (synCwppcand G (synCtc C)))
        (synWrex d (synCwppcand F C)
          (.classEq (synCtc (synCwppgamma F C)) (synCtc (.cv d)))))
      k (synCtc (synCwppgamma F C)) dv_cache_0009 dv_cache_0010 p0039 p0045
  have p0047 := Nominal.mp hyp_wppgammaimagetceqndv_5 p0046
  have p0048 :=
    @gMpbir (.classMem (synCtc (synCwppgamma F C)) (synCwppcand G (synCtc C)))
      (synWrex d (synCwppcand F C) (.classEq (synCtc (synCwppgamma F C)) (synCtc (.cv d))))
      p0020 p0047
  have p0049 :=
    @gSp
      (synWb (.classMem (.cv k) (synCwppcand G (synCtc C)))
        (synWrex d (synCwppcand F C) (.classEq (.cv k) (synCtc (.cv d)))))
      k
  have p0050 := Nominal.mp hyp_wppgammaimagetceqndv_5 p0049
  have p0051 :=
    @gBiimpi (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWrex d (synCwppcand F C) (.classEq (.cv k) (synCtc (.cv d)))) p0050
  have p0052 :=
    @gSimpl (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d)))
  have p0056 :=
    @gSimpr (.classMem (synCwppgamma F C) (synCwppcand F C))
      (synWral d (synCwppcand F C) (synWbr (synCwppgamma F C) (synClec) (.cv d)))
  have p0057 := Nominal.mp p0012 p0056
  have p0058 :=
    @gRsp (synWbr (synCwppgamma F C) (synClec) (.cv d)) d (synCwppcand F C)
  have p0059 := Nominal.mp p0057 p0058
  have p0060 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv d) (synCwppcand F C))
      (synWbr (synCwppgamma F C) (synClec) (.cv d)) p0052 p0059
  have p0076 :=
    @gA1i (.classMem (synCwppgamma F C) (synCncs))
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      p0035
  have p0078 := @gElwppcand C (.cv d) F
  have p0079 :=
    @gBiimpi (.classMem (.cv d) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.classMem (.cv d) (synCwppreach F C)))
      p0078
  have p0080 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv d) (synCwppcand F C))
      (synWa (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.classMem (.cv d) (synCwppreach F C)))
      p0052 p0079
  have p0081 :=
    @gSimpl
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (.classMem (.cv d) (synCwppreach F C))
  have p0082 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (synWa (.classMem (.cv d) (synChwcards (synCvv)))
          (synWbr (.cv d) (synClec) C)) (.classMem (.cv d) (synCwppreach F C)))
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      p0080 p0081
  have p0083 :=
    @gSimpl (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C)
  have p0084 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (.classMem (.cv d) (synChwcards (synCvv))) (synWbr (.cv d) (synClec) C))
      (.classMem (.cv d) (synChwcards (synCvv))) p0082 p0083
  have p0086 := @gSseli (synChwcards (synCvv)) (synCncs) (.cv d) p0033
  have p0087 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (.cv d) (synChwcards (synCvv))) (.classMem (.cv d) (synCncs)) p0084
      p0086
  have p0088 :=
    @gJca
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.classMem (synCwppgamma F C) (synCncs)) (.classMem (.cv d) (synCncs)) p0076
      p0087
  have p0089 := @gTlecg (synCwppgamma F C) (.cv d)
  have p0090 :=
    @gSyl
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWa (.classMem (synCwppgamma F C) (synCncs)) (.classMem (.cv d) (synCncs)))
      (synWb (synWbr (synCwppgamma F C) (synClec) (.cv d))
        (synWbr (synCtc (synCwppgamma F C)) (synClec) (synCtc (.cv d))))
      p0088 p0089
  have p0091 :=
    @gMpbid
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWbr (synCwppgamma F C) (synClec) (.cv d))
      (synWbr (synCtc (synCwppgamma F C)) (synClec) (synCtc (.cv d))) p0060 p0090
  have p0092 :=
    @gSimpr (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d)))
  have p0093 :=
    @gBreq2d
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (.cv k) (synCtc (.cv d)) (synCtc (synCwppgamma F C)) (synClec) p0092
  have p0094 :=
    @gMpbird
      (synWa (.classMem (.cv d) (synCwppcand F C)) (.classEq (.cv k) (synCtc (.cv d))))
      (synWbr (synCtc (synCwppgamma F C)) (synClec) (.cv k))
      (synWbr (synCtc (synCwppgamma F C)) (synClec) (synCtc (.cv d))) p0091 p0093
  have p0095 :=
    @gRexlimiva (.classEq (.cv k) (synCtc (.cv d)))
      (synWbr (synCtc (synCwppgamma F C)) (synClec) (.cv k)) d (synCwppcand F C)
      dv_cache_0011 p0094
  have p0096 :=
    @gSyl (.classMem (.cv k) (synCwppcand G (synCtc C)))
      (synWrex d (synCwppcand F C) (.classEq (.cv k) (synCtc (.cv d))))
      (synWbr (synCtc (synCwppgamma F C)) (synClec) (.cv k)) p0051 p0095
  have p0097 :=
    @gRgen (synWbr (synCtc (synCwppgamma F C)) (synClec) (.cv k)) k
      (synCwppcand G (synCtc C)) p0096
  have p0098 :=
    @gWppcandleastuniqclndv (synCwppgamma G (synCtc C)) (synCtc (synCwppgamma F C))
      (synCtc C) k G dv_cache_0012 dv_cache_0009 dv_cache_0001 dv_cache_0002 p0004 p0009
      p0048 p0097
  have p0099 :=
    @gEqcomi (synCwppgamma G (synCtc C)) (synCtc (synCwppgamma F C)) p0098
  exact p0099

/-- Checked nominal proof certificate identified upstream as `g_wppgammareachndv`. -/
@[expose]
noncomputable def gWppgammareachndv (C : Class) (F : Class)
    (hyp_wppgammareachndv_1 : Nominal.NPrf (.classMem F (synCvv)))
    (hyp_wppgammareachndv_2 : Nominal.NPrf (.classMem C (synChwcards (synCvv)))) :
    Nominal.NPrf (.classMem (synCwppgamma F C) (synCwppreach F C)) :=
  by
  let proofSupport : Finset Var := C.fv ∪ F.fv
  let k : Var := freshVar proofSupport 0
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_k_not_C : k ∉ C.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (h))
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_C, not_false_eq_true])
  have dv_cache_0002 : k ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_F, not_false_eq_true])
  have p0000 :=
    @gPm32i (.classMem F (synCvv)) (.classMem C (synChwcards (synCvv)))
      hyp_wppgammareachndv_1 hyp_wppgammareachndv_2
  have p0001 := @gWppgammaminhwndv C k F dv_cache_0001 dv_cache_0002
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @gSimpl (.classMem (synCwppgamma F C) (synCwppcand F C))
      (synWral k (synCwppcand F C) (synWbr (synCwppgamma F C) (synClec) (.cv k)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @gElwppcand C (synCwppgamma F C) F
  have p0006 :=
    @gBiimpi (.classMem (synCwppgamma F C) (synCwppcand F C))
      (synWa (synWa (.classMem (synCwppgamma F C) (synChwcards (synCvv)))
          (synWbr (synCwppgamma F C) (synClec) C))
        (.classMem (synCwppgamma F C) (synCwppreach F C)))
      p0005
  have p0007 := Nominal.mp p0004 p0006
  have p0008 :=
    @gSimpr
      (synWa (.classMem (synCwppgamma F C) (synChwcards (synCvv)))
        (synWbr (synCwppgamma F C) (synClec) C))
      (.classMem (synCwppgamma F C) (synCwppreach F C))
  have p0009 := Nominal.mp p0007 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_wpphitexvndv`. -/
@[expose]
noncomputable def gWpphitexvndv (C : Class) (F : Class) (I : Class)
    (hyp_wpphitexvndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf (.classMem (synCwpphit F I C) (synCvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphit F I C))
  have p0001 :=
    @gA1i
      (.classEq (synCwpphit F I C)
        (synCima (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C))))
      (.classMem F (synCvv)) p0000
  have p0002 := @gEqid (synCfrec F I)
  have p0003 := @gFrecexg (synCfrec F I) F I (synCvv) p0002
  have p0004 := @gCnvexg (synCfrec F I) (synCvv)
  have p0005 :=
    @gSyl (.classMem F (synCvv)) (.classMem (synCfrec F I) (synCvv))
      (.classMem (synCcnv (synCfrec F I)) (synCvv)) p0003 p0004
  have p0006 := @gLecex
  have p0007 := @gSnex C
  have p0008 :=
    @gPm32i (.classMem (synClec) (synCvv)) (.classMem (synCsn C) (synCvv)) p0006
      p0007
  have p0009 := @gImaexg (synClec) (synCsn C) (synCvv) (synCvv)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @gA1i (.classMem (synCima (synClec) (synCsn C)) (synCvv)) (.classMem F (synCvv))
      p0010
  have p0012 :=
    @gJca (.classMem F (synCvv)) (.classMem (synCcnv (synCfrec F I)) (synCvv))
      (.classMem (synCima (synClec) (synCsn C)) (synCvv)) p0005 p0011
  have p0013 :=
    @gImaexg (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C)) (synCvv)
      (synCvv)
  have p0014 :=
    @gSyl (.classMem F (synCvv))
      (synWa (.classMem (synCcnv (synCfrec F I)) (synCvv))
        (.classMem (synCima (synClec) (synCsn C)) (synCvv)))
      (.classMem (synCima (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C)))
        (synCvv))
      p0012 p0013
  have p0015 :=
    @gEqeltrd (.classMem F (synCvv)) (synCwpphit F I C)
      (synCima (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C))) (synCvv)
      p0001 p0014
  have p0016 := Nominal.mp hyp_wpphitexvndv_1 p0015
  exact p0016

/-- Checked nominal proof certificate identified upstream as `g_elwpphitvndv`. -/
@[expose]
noncomputable def gElwpphitvndv (C : Class) (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (synWb (.classMem N (synCwpphit F I C))
          (synWa (.classMem N (synCnnc))
            (synWbr C (synClec) (synCfv (synCfrec F I) N))))) :=
  by
  have p0000 := (Nominal.classEqRefl (synCwpphit F I C))
  have p0001 :=
    @gEleq2i (synCwpphit F I C)
      (synCima (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C))) N p0000
  have p0002 :=
    @gA1i
      (synWb (.classMem N (synCwpphit F I C)) (.classMem N
          (synCima (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C)))))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      p0001
  have p0003 := @gWpporbitfnndv F I
  have p0004 := @gElpreima (synCnnc) N (synCima (synClec) (synCsn C)) (synCfrec F I)
  have p0005 :=
    @gSyl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWfn (synCfrec F I) (synCnnc))
      (synWb (.classMem N
          (synCima (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C))))
        (synWa (.classMem N (synCnnc))
          (.classMem (synCfv (synCfrec F I) N) (synCima (synClec) (synCsn C)))))
      p0003 p0004
  have p0006 := @gElimasn (synClec) C (synCfv (synCfrec F I) N)
  have p0007 := (Nominal.biimpRefl (synWbr C (synClec) (synCfv (synCfrec F I) N)))
  have p0008 :=
    @gBicomi (synWbr C (synClec) (synCfv (synCfrec F I) N))
      (.classMem (synCop C (synCfv (synCfrec F I) N)) (synClec)) p0007
  have p0009 :=
    @gBitri (.classMem (synCfv (synCfrec F I) N) (synCima (synClec) (synCsn C)))
      (.classMem (synCop C (synCfv (synCfrec F I) N)) (synClec))
      (synWbr C (synClec) (synCfv (synCfrec F I) N)) p0006 p0008
  have p0010 :=
    @gAnbi2i (.classMem (synCfv (synCfrec F I) N) (synCima (synClec) (synCsn C)))
      (synWbr C (synClec) (synCfv (synCfrec F I) N)) (.classMem N (synCnnc)) p0009
  have p0011 :=
    @gA1i
      (synWb (synWa (.classMem N (synCnnc))
          (.classMem (synCfv (synCfrec F I) N) (synCima (synClec) (synCsn C))))
        (synWa (.classMem N (synCnnc)) (synWbr C (synClec) (synCfv (synCfrec F I) N))))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      p0010
  have p0012 :=
    @gBitrd
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCima (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C))))
      (synWa (.classMem N (synCnnc))
        (.classMem (synCfv (synCfrec F I) N) (synCima (synClec) (synCsn C))))
      (synWa (.classMem N (synCnnc)) (synWbr C (synClec) (synCfv (synCfrec F I) N)))
      p0005 p0011
  have p0013 :=
    @gBitrd
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCwpphit F I C))
      (.classMem N (synCima (synCcnv (synCfrec F I)) (synCima (synClec) (synCsn C))))
      (synWa (.classMem N (synCnnc)) (synWbr C (synClec) (synCfv (synCfrec F I) N)))
      p0002 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_wpphitminexvndv`. -/
@[expose]
noncomputable def gWpphitminexvndv (x : Var) (C : Class) (S : Class) (m : Var) (n : Var)
    (F : Class) (I : Class) (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_x : x ∉ C.fv)
    (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_I_m : m ∉ I.fv)
    (dv_I_n : n ∉ I.fv) (dv_I_x : x ∉ I.fv) (dv_S_m : m ∉ S.fv) (dv_S_n : n ∉ S.fv)
    (_dv_S_x : x ∉ S.fv) (dv_m_n : m ≠ n) (dv_m_x : m ≠ x) (dv_n_x : n ≠ x)
    (hyp_wpphitminexvndv_1 : Nominal.NPrf (.classMem F (synCvv))) :
    Nominal.NPrf
      (.imp (synWa (synWbr S (synCwe) (synCnnc))
          (synWrex x (synCnnc) (.classMem (.cv x) (synCwpphit F I C))))
        (synWrex m (synCnnc) (synWa (.classMem (.cv m) (synCwpphit F I C))
            (synWral n (synCnnc) (.imp (.classMem (.cv n) (synCwpphit F I C))
                (synWbr (.cv m) S (.cv n))))))) :=
  by
  have dv_cache_0001 : x ∉ ((synCwpphit F I C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          Finset.mem_union, dv_C_x, dv_F_x, dv_I_x, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : m ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : n ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : m ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_m, not_false_eq_true])
  have dv_cache_0006 : n ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_n, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (.cv m) (synCwpphit F I C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_m_x), dv_C_x, dv_F_x, dv_I_x, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    m ∉
      ((synWa (synWbr S (synCwe) (synCnnc))
          (synWrex x (synCnnc) (.classMem (.cv x) (synCwpphit F I C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_S_m, dv_m_x, dv_C_m, dv_F_m, dv_I_m,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 :
    n ∉
      ((synWa (synWbr S (synCwe) (synCnnc))
          (synWrex x (synCnnc) (.classMem (.cv x) (synCwpphit F I C))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_S_n, dv_n_x, dv_C_n, dv_F_n, dv_I_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0010 : m ∉ ((Wff.classMem (.cv x) (synCwpphit F I C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_singleton, dv_m_x, dv_C_m, dv_F_m, dv_I_m, or_false,
          not_false_eq_true])
  have dv_cache_0011 : n ∉ ((Wff.classMem (.cv x) (synCwpphit F I C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_singleton, dv_n_x, dv_C_n, dv_F_n, dv_I_n, or_false,
          not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.classMem (.cv n) (synCwpphit F I C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_n_x), dv_C_x, dv_F_x, dv_I_x, or_false,
          not_false_eq_true])
  have dv_cache_0013 : x ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ m from (by exact Ne.symm dv_m_x))
  have dv_cache_0014 : x ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show x ≠ n from (by exact Ne.symm dv_n_x))
  have dv_cache_0015 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show m ≠ n from (by exact dv_m_n))
  have p0000 := @gAbid2 x (synCwpphit F I C) dv_cache_0001
  have p0001 := @gWpphitexvndv C F I hyp_wpphitminexvndv_1
  have p0002 :=
    @gEqeltri (.cab x (.classMem (.cv x) (synCwpphit F I C))) (synCwpphit F I C)
      (synCvv) p0000 p0001
  have p0003 := @gEleq1 (.cv x) (.cv m) (synCwpphit F I C)
  have p0004 := @gEleq1 (.cv x) (.cv n) (synCwpphit F I C)
  have p0005 :=
    @gSimpl (synWbr S (synCwe) (synCnnc))
      (synWrex x (synCnnc) (.classMem (.cv x) (synCwpphit F I C)))
  have p0006 :=
    @gSimpr (synWbr S (synCwe) (synCnnc))
      (synWrex x (synCnnc) (.classMem (.cv x) (synCwpphit F I C)))
  have p0007_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq x m) (synWb (.classMem (.cv x) (synCwpphit F I C))
          (.classMem (.cv m) (synCwpphit F I C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwpphit synCima synWrex synWex synWa synWbr synCop synCun
          synCnin synWnan synCcompl synCcnv synCopab synCfrec synCclos1 synCint
          synCsn synCpprod synCtxp synCin synCcom synCmpt synCvv synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0007_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x n) (synWb (.classMem (.cv x) (synCwpphit F I C))
          (.classMem (.cv n) (synCwpphit F I C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCwpphit synCima synWrex synWex synWa synWbr synCop synCun
          synCnin synWnan synCcompl synCcnv synCopab synCfrec synCclos1 synCint
          synCsn synCpprod synCtxp synCin synCcom synCmpt synCvv synCplc synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0007 :=
    @gWeds
      (synWa (synWbr S (synCwe) (synCnnc))
        (synWrex x (synCnnc) (.classMem (.cv x) (synCwpphit F I C))))
      (.classMem (.cv x) (synCwpphit F I C)) (.classMem (.cv m) (synCwpphit F I C))
      (.classMem (.cv n) (synCwpphit F I C)) x m n (synCnnc) S dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 p0002 p0007_e01_recanon p0007_e02_recanon p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_elwpphitsucvndv`. -/
@[expose]
noncomputable def gElwpphitsucvndv (C : Class) (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
        (synWb (.classMem (synCplc N (synC1c)) (synCwpphit F I C))
          (synWbr C (synClec) (synCfv F (synCfv (synCfrec F I) N))))) :=
  by
  have p0000 :=
    @gSimpl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0001 := @gElwpphitvndv C F I (synCplc N (synC1c))
  have p0002 :=
    @gSyl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWb (.classMem (synCplc N (synC1c)) (synCwpphit F I C))
        (synWa (.classMem (synCplc N (synC1c)) (synCnnc))
          (synWbr C (synClec) (synCfv (synCfrec F I) (synCplc N (synC1c))))))
      p0000 p0001
  have p0003 := @gWpporbitsucndv F I N
  have p0004 :=
    @gBreq2d
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synCfv (synCfrec F I) (synCplc N (synC1c)))
      (synCfv F (synCfv (synCfrec F I) N)) C (synClec) p0003
  have p0005 :=
    @gAnbi2d
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synWbr C (synClec) (synCfv (synCfrec F I) (synCplc N (synC1c))))
      (synWbr C (synClec) (synCfv F (synCfv (synCfrec F I) N)))
      (.classMem (synCplc N (synC1c)) (synCnnc)) p0004
  have p0006 :=
    @gBitrd
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (.classMem (synCplc N (synC1c)) (synCwpphit F I C))
      (synWa (.classMem (synCplc N (synC1c)) (synCnnc))
        (synWbr C (synClec) (synCfv (synCfrec F I) (synCplc N (synC1c)))))
      (synWa (.classMem (synCplc N (synC1c)) (synCnnc))
        (synWbr C (synClec) (synCfv F (synCfv (synCfrec F I) N))))
      p0002 p0005
  have p0007 :=
    @gSimpr
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0008 := @gPeano2 N
  have p0009 :=
    @gSyl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (.classMem N (synCnnc)) (.classMem (synCplc N (synC1c)) (synCnnc)) p0007 p0008
  have p0010 :=
    @gBiantrurd
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (.classMem (synCplc N (synC1c)) (synCnnc))
      (synWbr C (synClec) (synCfv F (synCfv (synCfrec F I) N))) p0009
  have p0011 :=
    @gBicomd
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synWbr C (synClec) (synCfv F (synCfv (synCfrec F I) N)))
      (synWa (.classMem (synCplc N (synC1c)) (synCnnc))
        (synWbr C (synClec) (synCfv F (synCfv (synCfrec F I) N))))
      p0010
  have p0012 :=
    @gBitrd
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (.classMem (synCplc N (synC1c)) (synCwpphit F I C))
      (synWa (.classMem (synCplc N (synC1c)) (synCnnc))
        (synWbr C (synClec) (synCfv F (synCfv (synCfrec F I) N))))
      (synWbr C (synClec) (synCfv F (synCfv (synCfrec F I) N))) p0006 p0011
  exact p0012

/-- Checked nominal proof certificate identified upstream as `g_wpphitnestptndv`. -/
@[expose]
noncomputable def gWpphitnestptndv (F : Class) (H : Class) (I : Class) (L : Class)
    (N : Class) (_dv_F_N : Disjoint F.fv N.fv) (_dv_I_N : Disjoint I.fv N.fv) :
    Nominal.NPrf
      (.imp (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
              (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
            (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
              (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
        (.imp (.classMem N (synCwpphit F I H)) (.classMem N (synCwpphit F I L)))) :=
  by
  have p0000 :=
    @gSimpl
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synWa (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
          (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H))
  have p0001 :=
    @gSimpr
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0002 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (.classMem N (synCnnc)) p0000 p0001
  have p0003 :=
    @gA1d
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (.classMem N (synCnnc)) (.classMem N (synCwpphit F I H)) p0002
  have p0004 :=
    @gSimpr
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synWa (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
          (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H))
  have p0005 :=
    @gSimpr
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
        (.classMem (synCfv (synCfrec F I) N) (synCncs)))
      (synWbr L (synClec) H)
  have p0006 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (synWa (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
          (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H))
      (synWbr L (synClec) H) p0004 p0005
  have p0007 :=
    @gA1d
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (synWbr L (synClec) H) (.classMem N (synCwpphit F I H)) p0006
  have p0009 :=
    @gSimpl
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (.classMem N (synCnnc))
  have p0010 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
          (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      p0000 p0009
  have p0011 := @gElwpphitvndv H F I N
  have p0012 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWb (.classMem N (synCwpphit F I H)) (synWa (.classMem N (synCnnc))
          (synWbr H (synClec) (synCfv (synCfrec F I) N))))
      p0010 p0011
  have p0013 :=
    @gBiimpd
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (.classMem N (synCwpphit F I H))
      (synWa (.classMem N (synCnnc)) (synWbr H (synClec) (synCfv (synCfrec F I) N)))
      p0012
  have p0014 :=
    @gSimpr (.classMem N (synCnnc)) (synWbr H (synClec) (synCfv (synCfrec F I) N))
  have p0015 :=
    @gSyl6
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (.classMem N (synCwpphit F I H))
      (synWa (.classMem N (synCnnc)) (synWbr H (synClec) (synCfv (synCfrec F I) N)))
      (synWbr H (synClec) (synCfv (synCfrec F I) N)) p0013 p0014
  have p0016 :=
    @gJcad
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (.classMem N (synCwpphit F I H)) (synWbr L (synClec) H)
      (synWbr H (synClec) (synCfv (synCfrec F I) N)) p0007 p0015
  have p0018 :=
    @gSimpl
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
        (.classMem (synCfv (synCfrec F I) N) (synCncs)))
      (synWbr L (synClec) H)
  have p0019 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (synWa (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
          (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H))
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
        (.classMem (synCfv (synCfrec F I) N) (synCncs)))
      p0004 p0018
  have p0020 := @gLectr L H (synCfv (synCfrec F I) N)
  have p0021 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
        (.classMem (synCfv (synCfrec F I) N) (synCncs)))
      (.imp (synWa (synWbr L (synClec) H) (synWbr H (synClec) (synCfv (synCfrec F I) N)))
        (synWbr L (synClec) (synCfv (synCfrec F I) N)))
      p0019 p0020
  have p0022 :=
    @gSyld
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (.classMem N (synCwpphit F I H))
      (synWa (synWbr L (synClec) H) (synWbr H (synClec) (synCfv (synCfrec F I) N)))
      (synWbr L (synClec) (synCfv (synCfrec F I) N)) p0016 p0021
  have p0023 :=
    @gJcad
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (.classMem N (synCwpphit F I H)) (.classMem N (synCnnc))
      (synWbr L (synClec) (synCfv (synCfrec F I) N)) p0003 p0022
  have p0027 := @gElwpphitvndv L F I N
  have p0028 :=
    @gSyl
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
        (synWss (synCrn F) (synCdm F)))
      (synWb (.classMem N (synCwpphit F I L)) (synWa (.classMem N (synCnnc))
          (synWbr L (synClec) (synCfv (synCfrec F I) N))))
      p0010 p0027
  have p0029 :=
    @gBiimprd
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (.classMem N (synCwpphit F I L))
      (synWa (.classMem N (synCnnc)) (synWbr L (synClec) (synCfv (synCfrec F I) N)))
      p0028
  have p0030 :=
    @gSyld
      (synWa (synWa (synW3a (.classMem F (synCfuns)) (.classMem I (synCdm F))
            (synWss (synCrn F) (synCdm F))) (.classMem N (synCnnc))) (synWa
          (synW3a (.classMem L (synCncs)) (.classMem H (synCncs))
            (.classMem (synCfv (synCfrec F I) N) (synCncs))) (synWbr L (synClec) H)))
      (.classMem N (synCwpphit F I H))
      (synWa (.classMem N (synCnnc)) (synWbr L (synClec) (synCfv (synCfrec F I) N)))
      (.classMem N (synCwpphit F I L)) p0023 p0029
  exact p0030


end NFChoice.DirectNominalPrf.WPPReplay

end
