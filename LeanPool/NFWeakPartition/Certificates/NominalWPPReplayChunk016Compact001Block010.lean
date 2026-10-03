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

@[expose]
noncomputable def g_wppcandleastreundv (ph : Wff) (C : Class) (k : Var) (m : Var)
    (F : Class) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv)
    (dv_F_m : m ∉ F.fv) (dv_k_m : k ≠ m) (_dv_k_ph : k ∉ ph.fv) (_dv_m_ph : m ∉ ph.fv)
    (hyp_wppcandleastreundv_1 : Nominal.NPrf (.imp ph (syn_wrex m (syn_cwppcand F C)
            (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))) :
    Nominal.NPrf
      (.imp ph (syn_wreu m (syn_cwppcand F C)
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))) :=
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
  have dv_cache_0002 : k ∉ ((syn_cwppcand F C)).fv :=
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
  have dv_cache_0003 : k ∉ ((syn_wbr (.cv m) (syn_clec) (.cv n))).fv :=
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
  have dv_cache_0005 : k ∉ ((syn_wbr (.cv n) (syn_clec) (.cv m))).fv :=
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
  have dv_cache_0006 : n ∉ ((syn_cwppcand F C)).fv :=
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
  have dv_cache_0007 : m ∉ (syn_wtru).fv :=
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
  have dv_cache_0008 : n ∉ (syn_wtru).fv :=
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
  have dv_cache_0011 : m ∉ ((syn_cwppcand F C)).fv :=
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
    n ∉ ((syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))).fv :=
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
    m ∉ ((syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))).fv :=
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
  have p0000 := @g_tru
  have p0001 :=
    @g_simpr
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C)))
      (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
        (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
  have p0002 :=
    @g_simpl (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))
  have p0003 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
        (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) p0001 p0002
  have p0004 :=
    @g_simpl
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C)))
      (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
        (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
  have p0005 :=
    @g_simpr (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C)))
      (.classMem (.cv n) (syn_cwppcand F C)) p0004 p0005
  have p0007 := @g_id (.classEq (.cv k) (.cv n))
  have p0008 :=
    @g_breq2d (.classEq (.cv k) (.cv n)) (.cv k) (.cv n) (.cv m) (syn_clec) p0007
  have p0009 :=
    @g_rspcv (syn_wbr (.cv m) (syn_clec) (.cv k)) (syn_wbr (.cv m) (syn_clec) (.cv n)) k
      (.cv n) (syn_cwppcand F C) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0008
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (.classMem (.cv n) (syn_cwppcand F C))
      (.imp (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
        (syn_wbr (.cv m) (syn_clec) (.cv n)))
      p0006 p0009
  have p0011 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
      (syn_wbr (.cv m) (syn_clec) (.cv n)) p0003 p0010
  have p0013 :=
    @g_simpr (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))
  have p0014 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
        (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))) p0001 p0013
  have p0016 :=
    @g_simpl (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C))
  have p0017 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C)))
      (.classMem (.cv m) (syn_cwppcand F C)) p0004 p0016
  have p0018 := @g_id (.classEq (.cv k) (.cv m))
  have p0019 :=
    @g_breq2d (.classEq (.cv k) (.cv m)) (.cv k) (.cv m) (.cv n) (syn_clec) p0018
  have p0020 :=
    @g_rspcv (syn_wbr (.cv n) (syn_clec) (.cv k)) (syn_wbr (.cv n) (syn_clec) (.cv m)) k
      (.cv m) (syn_cwppcand F C) dv_cache_0004 dv_cache_0002 dv_cache_0005 p0019
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (.classMem (.cv m) (syn_cwppcand F C))
      (.imp (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))
        (syn_wbr (.cv n) (syn_clec) (.cv m)))
      p0017 p0020
  have p0022 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))
      (syn_wbr (.cv n) (syn_clec) (.cv m)) p0014 p0021
  have p0023 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wbr (.cv m) (syn_clec) (.cv n)) (syn_wbr (.cv n) (syn_clec) (.cv m)) p0011
      p0022
  have p0027 := @g_elwppcand C (.cv m) F
  have p0028 :=
    @g_biimpi (.classMem (.cv m) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv m) (syn_clec) C)) (.classMem (.cv m) (syn_cwppreach F C)))
      p0027
  have p0029 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (.classMem (.cv m) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv m) (syn_clec) C)) (.classMem (.cv m) (syn_cwppreach F C)))
      p0017 p0028
  have p0030 :=
    @g_simpl
      (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C))
      (.classMem (.cv m) (syn_cwppreach F C))
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wa (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv m) (syn_clec) C)) (.classMem (.cv m) (syn_cwppreach F C)))
      (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C))
      p0029 p0030
  have p0032 :=
    @g_simpl (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C)
  have p0033 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv))) (syn_wbr (.cv m) (syn_clec) C))
      (.classMem (.cv m) (syn_chwcards (syn_cvv))) p0031 p0032
  have p0037 := @g_elwppcand C (.cv n) F
  have p0038 :=
    @g_biimpi (.classMem (.cv n) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv n) (syn_clec) C)) (.classMem (.cv n) (syn_cwppreach F C)))
      p0037
  have p0039 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (.classMem (.cv n) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv n) (syn_clec) C)) (.classMem (.cv n) (syn_cwppreach F C)))
      p0006 p0038
  have p0040 :=
    @g_simpl
      (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C))
      (.classMem (.cv n) (syn_cwppreach F C))
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wa (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv n) (syn_clec) C)) (.classMem (.cv n) (syn_cwppreach F C)))
      (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C))
      p0039 p0040
  have p0042 :=
    @g_simpl (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C)
  have p0043 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wa (.classMem (.cv n) (syn_chwcards (syn_cvv))) (syn_wbr (.cv n) (syn_clec) C))
      (.classMem (.cv n) (syn_chwcards (syn_cvv))) p0041 p0042
  have p0044 :=
    @g_jca
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (.classMem (.cv m) (syn_chwcards (syn_cvv)))
      (.classMem (.cv n) (syn_chwcards (syn_cvv))) p0033 p0043
  have p0045 := @g_hwcardslecanti m n
  have p0046 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wa (.classMem (.cv m) (syn_chwcards (syn_cvv)))
        (.classMem (.cv n) (syn_chwcards (syn_cvv))))
      (.imp (syn_wa (syn_wbr (.cv m) (syn_clec) (.cv n)) (syn_wbr (.cv n) (syn_clec) (.cv m)))
        (.classEq (.cv m) (.cv n)))
      p0044 p0045
  have p0047 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C)))
        (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k)))))
      (syn_wa (syn_wbr (.cv m) (syn_clec) (.cv n)) (syn_wbr (.cv n) (syn_clec) (.cv m)))
      (.classEq (.cv m) (.cv n)) p0023 p0046
  have p0048 :=
    @g_ex
      (syn_wa (.classMem (.cv m) (syn_cwppcand F C)) (.classMem (.cv n) (syn_cwppcand F C)))
      (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
        (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
      (.classEq (.cv m) (.cv n)) p0047
  have p0049 :=
    @g_a1i
      (.imp (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (.classMem (.cv n) (syn_cwppcand F C))) (.imp
          (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
          (.classEq (.cv m) (.cv n))))
      syn_wtru p0048
  have p0050 :=
    @g_ralrimivv syn_wtru
      (.imp (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
        (.classEq (.cv m) (.cv n)))
      m n (syn_cwppcand F C) (syn_cwppcand F C) dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 p0049
  have p0051 := Nominal.mp p0000 p0050
  have p0052 :=
    @g_a1i
      (syn_wral m (syn_cwppcand F C) (syn_wral n (syn_cwppcand F C) (.imp
            (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
              (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
            (.classEq (.cv m) (.cv n)))))
      ph p0051
  have p0053 :=
    @g_jca ph
      (syn_wrex m (syn_cwppcand F C)
        (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (syn_wral m (syn_cwppcand F C) (syn_wral n (syn_cwppcand F C) (.imp
            (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
              (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
            (.classEq (.cv m) (.cv n)))))
      hyp_wppcandleastreundv_1 p0052
  have p0054 := @g_id (.classEq (.cv m) (.cv n))
  have p0055 :=
    @g_breq1d (.classEq (.cv m) (.cv n)) (.cv m) (.cv n) (.cv k) (syn_clec) p0054
  have p0056 :=
    @g_ralbidv (.classEq (.cv m) (.cv n)) (syn_wbr (.cv m) (syn_clec) (.cv k))
      (syn_wbr (.cv n) (syn_clec) (.cv k)) k (syn_cwppcand F C) dv_cache_0010 p0055
  have p0057_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq m n)
        (syn_wb (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wral syn_cwppcand syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cwppreach syn_cuni syn_wex syn_crn syn_cima syn_wrex syn_wbr syn_cop syn_cun
          syn_cvv syn_cfrec syn_cclos1 syn_cint syn_csn syn_cpprod syn_ctxp syn_ccom
          syn_copab syn_c1st syn_cmpt syn_cplc syn_c1c syn_cimage syn_ccnv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0056
  have p0057 :=
    @g_reu4 (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))) m n
      (syn_cwppcand F C) dv_cache_0011 dv_cache_0006 dv_cache_0012 dv_cache_0013
      dv_cache_0009 p0057_e00_recanon
  have p0058_e00_recanon :
    Nominal.NPrf
      (syn_wb (syn_wreu m (syn_cwppcand F C)
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))) (syn_wa
          (syn_wrex m (syn_cwppcand F C)
            (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))
          (syn_wral m (syn_cwppcand F C) (syn_wral n (syn_cwppcand F C) (.imp (syn_wa
                  (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
                  (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
                (.classEq (.cv m) (.cv n))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wreu syn_weu syn_wex syn_wa syn_cwppcand syn_cin syn_ccompl
          syn_cnin syn_wnan syn_cwppreach syn_cuni syn_crn syn_cima syn_wrex syn_wbr
          syn_cop syn_cun syn_cvv syn_cfrec syn_cclos1 syn_cint syn_csn syn_cpprod
          syn_ctxp syn_ccom syn_copab syn_c1st syn_cmpt syn_cplc syn_c1c syn_cimage
          syn_ccnv syn_wral
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
    @g_biimpri
      (syn_wreu m (syn_cwppcand F C)
        (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (syn_wa (syn_wrex m (syn_cwppcand F C)
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))
        (syn_wral m (syn_cwppcand F C) (syn_wral n (syn_cwppcand F C) (.imp
              (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
                (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
              (.classEq (.cv m) (.cv n))))))
      p0058_e00_recanon
  have p0059 :=
    @g_syl ph
      (syn_wa (syn_wrex m (syn_cwppcand F C)
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))
        (syn_wral m (syn_cwppcand F C) (syn_wral n (syn_cwppcand F C) (.imp
              (syn_wa (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
                (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv n) (syn_clec) (.cv k))))
              (.classEq (.cv m) (.cv n))))))
      (syn_wreu m (syn_cwppcand F C)
        (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))
      p0053 p0058
  exact p0059

@[expose]
noncomputable def g_wppgammaminpackndv (ph : Wff) (C : Class) (k : Var) (m : Var)
    (F : Class) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv) (dv_F_k : k ∉ F.fv)
    (dv_F_m : m ∉ F.fv) (dv_k_m : k ≠ m) (dv_k_ph : k ∉ ph.fv) (dv_m_ph : m ∉ ph.fv)
    (hyp_wppgammaminpackndv_1 : Nominal.NPrf (.imp ph (syn_wrex m (syn_cwppcand F C)
            (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))) :
    Nominal.NPrf
      (.imp ph (syn_wa (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k))))) :=
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
  have dv_cache_0008 : k ∉ ((Wff.classEq (.cv m) (syn_cwppgamma F C))).fv :=
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
  have dv_cache_0009 : m ∉ ((syn_cwppgamma F C)).fv :=
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
  have dv_cache_0010 : m ∉ ((syn_cwppcand F C)).fv :=
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
      ((syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_wppgamma C k m F
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 :=
    @g_a1i
      (.classEq (syn_cwppgamma F C) (syn_cio m (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))))
      ph p0000
  have p0002 :=
    @g_wppcandleastreundv ph C k m F dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 hyp_wppgammaminpackndv_1
  have p0003 :=
    @g_reiotacl2 (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))) m
      (syn_cwppcand F C)
  have p0004 :=
    @g_syl ph
      (syn_wreu m (syn_cwppcand F C)
        (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))
      (.classMem (syn_cio m (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
            (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))
        (syn_crab m (syn_cwppcand F C)
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))
      p0002 p0003
  have p0005 :=
    @g_eqeltrd ph (syn_cwppgamma F C)
      (syn_cio m (syn_wa (.classMem (.cv m) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))
      (syn_crab m (syn_cwppcand F C)
        (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k))))
      p0001 p0004
  have p0006 := @g_id (.classEq (.cv m) (syn_cwppgamma F C))
  have p0007 :=
    @g_breq1d (.classEq (.cv m) (syn_cwppgamma F C)) (.cv m) (syn_cwppgamma F C) (.cv k)
      (syn_clec) p0006
  have p0008 :=
    @g_ralbidv (.classEq (.cv m) (syn_cwppgamma F C)) (syn_wbr (.cv m) (syn_clec) (.cv k))
      (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k)) k (syn_cwppcand F C) dv_cache_0008
      p0007
  have p0009 :=
    @g_elrab (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k))) m
      (syn_cwppgamma F C) (syn_cwppcand F C) dv_cache_0009 dv_cache_0010 dv_cache_0011
      p0008
  have p0010 :=
    @g_biimpi
      (.classMem (syn_cwppgamma F C) (syn_crab m (syn_cwppcand F C)
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))
      (syn_wa (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
        (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k))))
      p0009
  have p0011 :=
    @g_syl ph
      (.classMem (syn_cwppgamma F C) (syn_crab m (syn_cwppcand F C)
          (syn_wral k (syn_cwppcand F C) (syn_wbr (.cv m) (syn_clec) (.cv k)))))
      (syn_wa (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
        (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k))))
      p0005 p0010
  exact p0011

@[expose]
noncomputable def g_wppgammaminhwndv (C : Class) (k : Var) (F : Class) (dv_C_k : k ∉ C.fv)
    (dv_F_k : k ∉ F.fv) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wa (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
          (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k))))) :=
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
    k ∉ ((syn_wa (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))))).fv :=
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
    m ∉ ((syn_wa (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv))))).fv :=
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
    @g_wppcandminhwndv k C m F dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0001 :=
    @g_wppgammaminpackndv
      (syn_wa (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv)))) C k m F
      dv_cache_0002 dv_cache_0001 dv_cache_0004 dv_cache_0003 dv_cache_0006 dv_cache_0007
      dv_cache_0008 p0000
  exact p0001

@[expose]
noncomputable def g_wppcardtfnexndv :
    Nominal.NPrf (.classMem (syn_cwppcardtfn) (syn_cvv)) :=
  by
  have p0000 := @g_tcfnex
  have p0001 := @g_ncsex
  have p0002 := @g_pw1ex (syn_cncs) p0001
  have p0003 := @g_resex (syn_ctcfn) (syn_cpw1 (syn_cncs)) p0000 p0002
  have p0004 := (Nominal.classEqRefl (syn_cwppcardtfn))
  have p0005 :=
    @g_eleq1i (syn_cwppcardtfn) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_cvv)
      p0004
  have p0006 :=
    @g_mpbir (.classMem (syn_cwppcardtfn) (syn_cvv))
      (.classMem (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_cvv)) p0003 p0005
  exact p0006

@[expose]
noncomputable def g_wppcardtfnvalndv (q : Var) :
    Nominal.NPrf
      (.imp (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
        (.classEq (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_ctc (syn_cuni (.cv q))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppcardtfn))
  have p0001 :=
    @g_fveq1i (.cv q) (syn_cwppcardtfn) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) p0000
  have p0002 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppcardtfn) (.cv q))
        (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (.cv q)))
      (.classMem (.cv q) (syn_cpw1 (syn_cncs))) p0001
  have p0003 := @g_fvres (.cv q) (syn_cpw1 (syn_cncs)) (syn_ctcfn)
  have p0004 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (.cv q))
      (syn_cfv (syn_ctcfn) (.cv q)) p0002 p0003
  have p0005 := @g_hnwpw1argcl (syn_cncs) q
  have p0006 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_cuni (.cv q)) (syn_cncs))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0005
  have p0007 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.cv q)
      (syn_csn (syn_cuni (.cv q))) (syn_ctcfn) p0006
  have p0008 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q))
      (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q))))
      p0004 p0007
  have p0010 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_cuni (.cv q)) (syn_cncs))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0005
  have p0011 := @g_elex (syn_cuni (.cv q)) (syn_cncs)
  have p0012 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classMem (syn_cuni (.cv q)) (syn_cvv))
      p0010 p0011
  have p0013 := @g_tcfnfvcl (syn_cuni (.cv q))
  have p0014 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))))
      p0012 p0013
  have p0015 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q))
      (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))
      p0008 p0014
  exact p0015

@[expose]
noncomputable def g_wppcardtfnmapndv :
    Nominal.NPrf (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let q : Var := freshVar proofSupport 0
  have dv_cache_0001 : q ∉ ((syn_cpw1 (syn_cncs))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : q ∉ ((syn_cncs)).fv :=
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
  have dv_cache_0003 : q ∉ ((syn_cwppcardtfn)).fv :=
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
  have p0000 := @g_fntcfn
  have p0001 := @g_pw1ss1c (syn_cncs)
  have p0002 :=
    @g_pm3_2i (syn_wfn (syn_ctcfn) (syn_c1c)) (syn_wss (syn_cpw1 (syn_cncs)) (syn_c1c))
      p0000 p0001
  have p0003 := @g_fnssres (syn_c1c) (syn_cpw1 (syn_cncs)) (syn_ctcfn)
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := (Nominal.classEqRefl (syn_cwppcardtfn))
  have p0006 :=
    @g_fneq1i (syn_cpw1 (syn_cncs)) (syn_cwppcardtfn)
      (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) p0005
  have p0007 :=
    @g_mpbir (syn_wfn (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)))
      (syn_wfn (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_cpw1 (syn_cncs))) p0004
      p0006
  have p0009 :=
    @g_fveq1i (.cv q) (syn_cwppcardtfn) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) p0005
  have p0010 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppcardtfn) (.cv q))
        (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (.cv q)))
      (.classMem (.cv q) (syn_cpw1 (syn_cncs))) p0009
  have p0011 := @g_fvres (.cv q) (syn_cpw1 (syn_cncs)) (syn_ctcfn)
  have p0012 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (.cv q))
      (syn_cfv (syn_ctcfn) (.cv q)) p0010 p0011
  have p0013 := @g_hnwpw1argcl (syn_cncs) q
  have p0014 :=
    @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_cuni (.cv q)) (syn_cncs))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0013
  have p0015 :=
    @g_fveq2d (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.cv q)
      (syn_csn (syn_cuni (.cv q))) (syn_ctcfn) p0014
  have p0016 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q))
      (syn_cfv (syn_ctcfn) (.cv q)) (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q))))
      p0012 p0015
  have p0018 :=
    @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_cuni (.cv q)) (syn_cncs))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0013
  have p0019 := @g_elex (syn_cuni (.cv q)) (syn_cncs)
  have p0020 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_cuni (.cv q)) (syn_cncs)) (.classMem (syn_cuni (.cv q)) (syn_cvv))
      p0018 p0019
  have p0021 := @g_tcfnfvcl (syn_cuni (.cv q))
  have p0022 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_cuni (.cv q)) (syn_cvv))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q))))
      p0020 p0021
  have p0023 :=
    @g_eqtrd (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (syn_cfv (syn_cwppcardtfn) (.cv q))
      (syn_cfv (syn_ctcfn) (syn_csn (syn_cuni (.cv q)))) (syn_ctc (syn_cuni (.cv q)))
      p0016 p0022
  have p0026 := @g_tccl (syn_cuni (.cv q))
  have p0027 :=
    @g_syl (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classMem (syn_cuni (.cv q)) (syn_cncs))
      (.classMem (syn_ctc (syn_cuni (.cv q))) (syn_cncs)) p0018 p0026
  have p0028 :=
    @g_eqeltrd (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_ctc (syn_cuni (.cv q))) (syn_cncs) p0023
      p0027
  have p0029 :=
    @g_rgen (.classMem (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cncs)) q
      (syn_cpw1 (syn_cncs)) p0028
  have p0030 :=
    @g_pm3_2i (syn_wfn (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)))
      (syn_wral q (syn_cpw1 (syn_cncs))
        (.classMem (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cncs)))
      p0007 p0029
  have p0031 :=
    @g_ffnfv q (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn) dv_cache_0001
      dv_cache_0002 dv_cache_0003
  have p0032 :=
    @g_mpbir (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs))
      (syn_wa (syn_wfn (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)))
        (syn_wral q (syn_cpw1 (syn_cncs))
          (.classMem (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_cncs))))
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

@[expose]
noncomputable def g_wppcardtfnf1ndv :
    Nominal.NPrf (syn_wf1 (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let p : Var := freshVar proofSupport 0
  let q : Var := freshVar proofSupport 1
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : q ∉ ((Wff.classMem (.cv p) (syn_cpw1 (syn_cncs)))).fv := by
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
  have dv_cache_0002 : p ∉ ((syn_cpw1 (syn_cncs))).fv :=
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
  have dv_cache_0003 : q ∉ ((syn_cpw1 (syn_cncs))).fv :=
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
  have dv_cache_0004 : p ∉ ((syn_cwppcardtfn)).fv :=
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
  have dv_cache_0005 : q ∉ ((syn_cwppcardtfn)).fv :=
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
  have p0000 := @g_wppcardtfnmapndv
  have p0001 :=
    @g_simp1 (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
      (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
  have p0002 := @g_hnwpw1argcl (syn_cncs) p
  have p0003 :=
    @g_syl
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cncs))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))))
      p0001 p0002
  have p0004 :=
    @g_simprd
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classMem (syn_cuni (.cv p)) (syn_cncs))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0003
  have p0005 :=
    @g_simp3 (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
      (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
  have p0007 := @g_wppcardtfnvalndv p
  have p0008 :=
    @g_syl
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
      (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_ctc (syn_cuni (.cv p)))) p0001
      p0007
  have p0009 :=
    @g_simp2 (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
      (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
  have p0010 := @g_wppcardtfnvalndv q
  have p0011 :=
    @g_syl
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classEq (syn_cfv (syn_cwppcardtfn) (.cv q)) (syn_ctc (syn_cuni (.cv q)))) p0009
      p0010
  have p0012 :=
    @g_n_3eqtr3d
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q))
      (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q))) p0005 p0008 p0011
  have p0016 :=
    @g_simpld
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classMem (syn_cuni (.cv p)) (syn_cncs))
      (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0003
  have p0018 := @g_hnwpw1argcl (syn_cncs) q
  have p0019 :=
    @g_syl
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (syn_wa (.classMem (syn_cuni (.cv q)) (syn_cncs))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))))
      p0009 p0018
  have p0020 :=
    @g_simpld
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classMem (syn_cuni (.cv q)) (syn_cncs))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0019
  have p0021 :=
    @g_jca
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classMem (syn_cuni (.cv p)) (syn_cncs)) (.classMem (syn_cuni (.cv q)) (syn_cncs))
      p0016 p0020
  have p0022 := @g_tc11 (syn_cuni (.cv p)) (syn_cuni (.cv q))
  have p0023 :=
    @g_syl
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cncs))
        (.classMem (syn_cuni (.cv q)) (syn_cncs)))
      (syn_wb (.classEq (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q))))
        (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q))))
      p0021 p0022
  have p0024 :=
    @g_biimpd
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classEq (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q))))
      (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q))) p0023
  have p0025 :=
    @g_mpd
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classEq (syn_ctc (syn_cuni (.cv p))) (syn_ctc (syn_cuni (.cv q))))
      (.classEq (syn_cuni (.cv p)) (syn_cuni (.cv q))) p0012 p0024
  have p0026 :=
    @g_sneqd
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (syn_cuni (.cv p)) (syn_cuni (.cv q)) p0025
  have p0027 :=
    @g_eqtrd
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.cv p) (syn_csn (syn_cuni (.cv p))) (syn_csn (syn_cuni (.cv q))) p0004 p0026
  have p0031 :=
    @g_simprd
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.classMem (syn_cuni (.cv q)) (syn_cncs))
      (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0019
  have p0032 :=
    @g_eqcomd
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.cv q) (syn_csn (syn_cuni (.cv q))) p0031
  have p0033 :=
    @g_eqtrd
      (syn_w3a (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
        (.classMem (.cv q) (syn_cpw1 (syn_cncs))) (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
          (syn_cfv (syn_cwppcardtfn) (.cv q))))
      (.cv p) (syn_csn (syn_cuni (.cv q))) (.cv q) p0027 p0032
  have p0034 :=
    @g_n_3exp (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
      (.classMem (.cv q) (syn_cpw1 (syn_cncs)))
      (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
      (.classEq (.cv p) (.cv q)) p0033
  have p0035 :=
    @g_ralrimiv (.classMem (.cv p) (syn_cpw1 (syn_cncs)))
      (.imp (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
        (.classEq (.cv p) (.cv q)))
      q (syn_cpw1 (syn_cncs)) dv_cache_0001 p0034
  have p0036 :=
    @g_rgen
      (syn_wral q (syn_cpw1 (syn_cncs)) (.imp (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
            (syn_cfv (syn_cwppcardtfn) (.cv q))) (.classEq (.cv p) (.cv q))))
      p (syn_cpw1 (syn_cncs)) p0035
  have p0037 :=
    @g_pm3_2i (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs))
      (syn_wral p (syn_cpw1 (syn_cncs)) (syn_wral q (syn_cpw1 (syn_cncs)) (.imp
            (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
            (.classEq (.cv p) (.cv q)))))
      p0000 p0036
  have p0038 :=
    @g_dff13 p q (syn_cpw1 (syn_cncs)) (syn_cncs) (syn_cwppcardtfn) dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0039_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wf1 (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs))
        (syn_wa (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs))
          (syn_wral p (syn_cpw1 (syn_cncs)) (syn_wral q (syn_cpw1 (syn_cncs)) (.imp
                (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p))
                  (syn_cfv (syn_cwppcardtfn) (.cv q))) (.classEq (.cv p) (.cv q))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wf1 syn_wa syn_wf syn_wfun syn_wss syn_cin syn_ccompl syn_cnin
          syn_wnan syn_ccom syn_copab syn_wex syn_ccnv syn_cid syn_cwppcardtfn syn_cres
          syn_ctcfn syn_cmpt syn_c1c syn_ctc syn_cio syn_cuni syn_csn syn_cpw1 syn_cncs
          syn_cqs syn_wrex syn_cec syn_cima syn_cvv syn_cen
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
    @g_mpbir (syn_wf1 (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs))
      (syn_wa (syn_wf (syn_cwppcardtfn) (syn_cpw1 (syn_cncs)) (syn_cncs))
        (syn_wral p (syn_cpw1 (syn_cncs)) (syn_wral q (syn_cpw1 (syn_cncs)) (.imp
              (.classEq (syn_cfv (syn_cwppcardtfn) (.cv p)) (syn_cfv (syn_cwppcardtfn) (.cv q)))
              (.classEq (.cv p) (.cv q))))))
      p0037 p0039_e01_recanon
  exact p0039

@[expose]
noncomputable def g_wppcardtfnvalsingndv (D : Class) :
    Nominal.NPrf
      (.imp (.classMem D (syn_cncs))
        (.classEq (syn_cfv (syn_cwppcardtfn) (syn_csn D)) (syn_ctc D))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwppcardtfn))
  have p0001 :=
    @g_fveq1i (syn_csn D) (syn_cwppcardtfn) (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs)))
      p0000
  have p0002 :=
    @g_a1i
      (.classEq (syn_cfv (syn_cwppcardtfn) (syn_csn D))
        (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_csn D)))
      (.classMem D (syn_cncs)) p0001
  have p0003 := @g_snelpw1 D (syn_cncs)
  have p0004 :=
    @g_biimpri (.classMem (syn_csn D) (syn_cpw1 (syn_cncs))) (.classMem D (syn_cncs))
      p0003
  have p0005 := @g_fvres (syn_csn D) (syn_cpw1 (syn_cncs)) (syn_ctcfn)
  have p0006 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem (syn_csn D) (syn_cpw1 (syn_cncs)))
      (.classEq (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_csn D))
        (syn_cfv (syn_ctcfn) (syn_csn D)))
      p0004 p0005
  have p0007 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardtfn) (syn_csn D))
      (syn_cfv (syn_cres (syn_ctcfn) (syn_cpw1 (syn_cncs))) (syn_csn D))
      (syn_cfv (syn_ctcfn) (syn_csn D)) p0002 p0006
  have p0008 := @g_id (.classMem D (syn_cncs))
  have p0009 := @g_elex D (syn_cncs)
  have p0010 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem D (syn_cncs)) (.classMem D (syn_cvv)) p0008
      p0009
  have p0011 := @g_tcfnfvcl D
  have p0012 :=
    @g_syl (.classMem D (syn_cncs)) (.classMem D (syn_cvv))
      (.classEq (syn_cfv (syn_ctcfn) (syn_csn D)) (syn_ctc D)) p0010 p0011
  have p0013 :=
    @g_eqtrd (.classMem D (syn_cncs)) (syn_cfv (syn_cwppcardtfn) (syn_csn D))
      (syn_cfv (syn_ctcfn) (syn_csn D)) (syn_ctc D) p0007 p0012
  exact p0013

@[expose]
noncomputable def g_wppreachorbitextcbidv (x : Var) (C : Class) (D : Class) (F : Class)
    (G : Class) (r : Var) (p : Var) (a : Var) (dv_C_a : a ∉ C.fv) (dv_C_p : p ∉ C.fv)
    (dv_D_a : a ∉ D.fv) (dv_D_p : p ∉ D.fv) (dv_D_r : r ∉ D.fv) (dv_D_x : x ∉ D.fv)
    (dv_F_a : a ∉ F.fv) (dv_F_p : p ∉ F.fv) (dv_F_r : r ∉ F.fv) (dv_F_x : x ∉ F.fv)
    (dv_G_a : a ∉ G.fv) (dv_G_p : p ∉ G.fv) (dv_G_x : x ∉ G.fv) (dv_a_p : a ≠ p)
    (dv_a_r : a ≠ r)
    (hyp_wppreachorbitextcbidv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppreachorbitextcbidv_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wppreachorbitextcbidv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppreachorbitextcbidv_4 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_wppreachorbitextcbidv_5 : Nominal.NPrf (.classMem (syn_ctc D) (syn_cdm G)))
    (hyp_wppreachorbitextcbidv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G)))
    (hyp_wppreachorbitextcbidv_7 : Nominal.NPrf (syn_wral x (syn_cdm F)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x))))))
    (hyp_wppreachorbitextcbidv_8 : Nominal.NPrf (.classMem C (syn_cncs)))
    (hyp_wppreachorbitextcbidv_9 : Nominal.NPrf (syn_wral r (syn_cnnc)
          (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs)))) :
    Nominal.NPrf
      (syn_wb (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))
        (syn_wrex p (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec)
            (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))) :=
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
  have dv_cache_0002 : r ∉ ((syn_cnnc)).fv :=
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
    r ∉ ((Wff.classMem (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs))).fv :=
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
  have dv_cache_0007 : p ∉ ((syn_ctc (.cv a))).fv :=
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
  have dv_cache_0008 : p ∉ ((syn_cnnc)).fv :=
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
      ((syn_wbr (syn_ctc C) (syn_clec)
          (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))))).fv :=
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
      ((syn_wrex p (syn_cnnc) (syn_wbr (syn_ctc C) (syn_clec)
            (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))).fv :=
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
    r ∉ ((Wff.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs))).fv :=
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
  have dv_cache_0015 : a ∉ ((syn_cnnc)).fv :=
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
    a ∉ ((syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))).fv :=
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
      ((syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))).fv :=
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
      ((syn_wa (.classMem (.cv p) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec)
            (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))).fv :=
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
      ((syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))).fv :=
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
    @g_simpl (.classMem (.cv a) (syn_cnnc))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))
  have p0001 := @g_nntccl (.cv a)
  have p0002 :=
    @g_syl
      (syn_wa (.classMem (.cv a) (syn_cnnc))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))
      (.classMem (.cv a) (syn_cnnc)) (.classMem (syn_ctc (.cv a)) (syn_cnnc)) p0000 p0001
  have p0003 :=
    @g_a1i (.classMem C (syn_cncs)) (.classMem (.cv a) (syn_cnnc))
      hyp_wppreachorbitextcbidv_8
  have p0004 :=
    @g_a1i
      (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs)))
      (.classMem (.cv a) (syn_cnnc)) hyp_wppreachorbitextcbidv_9
  have p0005 := @g_id (.classEq (.cv r) (.cv a))
  have p0006 := @g_fveq2d (.classEq (.cv r) (.cv a)) (.cv r) (.cv a) (syn_cfrec F D) p0005
  have p0007 :=
    @g_eleq1d (.classEq (.cv r) (.cv a)) (syn_cfv (syn_cfrec F D) (.cv r))
      (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs) p0006
  have p0008 :=
    @g_rspcv (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs))
      (.classMem (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs)) r (.cv a) (syn_cnnc)
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0007
  have p0009 :=
    @g_mpd (.classMem (.cv a) (syn_cnnc))
      (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs)))
      (.classMem (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs)) p0004 p0008
  have p0010 :=
    @g_jca (.classMem (.cv a) (syn_cnnc)) (.classMem C (syn_cncs))
      (.classMem (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs)) p0003 p0009
  have p0011 := @g_tlecg C (syn_cfv (syn_cfrec F D) (.cv a))
  have p0012 :=
    @g_syl (.classMem (.cv a) (syn_cnnc))
      (syn_wa (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F D) (.cv a)) (syn_cncs)))
      (syn_wb (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv a)))))
      p0010 p0011
  have p0013 :=
    @g_frectchom0 x F G D (.cv a) dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_wppreachorbitextcbidv_1 hyp_wppreachorbitextcbidv_2 hyp_wppreachorbitextcbidv_3
      hyp_wppreachorbitextcbidv_4 hyp_wppreachorbitextcbidv_5 hyp_wppreachorbitextcbidv_6
      hyp_wppreachorbitextcbidv_7
  have p0014 :=
    @g_breq2d (.classMem (.cv a) (syn_cnnc)) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv a)))
      (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))) (syn_ctc C) (syn_clec) p0013
  have p0015 :=
    @g_bitrd (.classMem (.cv a) (syn_cnnc))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv a))))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))))
      p0012 p0014
  have p0016 :=
    @g_biimpd (.classMem (.cv a) (syn_cnnc))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))))
      p0015
  have p0017 :=
    @g_imp (.classMem (.cv a) (syn_cnnc))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))))
      p0016
  have p0018 :=
    @g_jca
      (syn_wa (.classMem (.cv a) (syn_cnnc))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))
      (.classMem (syn_ctc (.cv a)) (syn_cnnc))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))))
      p0002 p0017
  have p0019 := @g_id (.classEq (.cv p) (syn_ctc (.cv a)))
  have p0020 :=
    @g_fveq2d (.classEq (.cv p) (syn_ctc (.cv a))) (.cv p) (syn_ctc (.cv a))
      (syn_cfrec G (syn_ctc D)) p0019
  have p0021 :=
    @g_breq2d (.classEq (.cv p) (syn_ctc (.cv a)))
      (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))
      (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))) (syn_ctc C) (syn_clec) p0020
  have p0022 :=
    @g_rspcev (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a))))
      p (syn_ctc (.cv a)) (syn_cnnc) dv_cache_0007 dv_cache_0008 dv_cache_0009 p0021
  have p0023 :=
    @g_syl
      (syn_wa (.classMem (.cv a) (syn_cnnc))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))
      (syn_wa (.classMem (syn_ctc (.cv a)) (syn_cnnc)) (syn_wbr (syn_ctc C) (syn_clec)
          (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv a)))))
      (syn_wrex p (syn_cnnc)
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      p0018 p0022
  have p0024 :=
    @g_rexlimiva (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))
      (syn_wrex p (syn_cnnc)
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      a (syn_cnnc) dv_cache_0010 p0023
  have p0025 :=
    @g_simpl (.classMem (.cv p) (syn_cnnc))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))
  have p0026 := @g_nntcpreim n (.cv p) dv_cache_0011
  have p0027 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      (.classMem (.cv p) (syn_cnnc))
      (syn_wrex n (syn_cnnc) (.classEq (syn_ctc (.cv n)) (.cv p))) p0025 p0026
  have p0028 :=
    @g_simp2
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))
  have p0029 :=
    @g_simp1
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))
  have p0030 :=
    @g_simpr (.classMem (.cv p) (syn_cnnc))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))
  have p0031 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc))
          (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p)))
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))) p0029
      p0030
  have p0032 :=
    @g_simp3
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p))
  have p0033 := @g_id (.classEq (syn_ctc (.cv n)) (.cv p))
  have p0034 :=
    @g_fveq2d (.classEq (syn_ctc (.cv n)) (.cv p)) (syn_ctc (.cv n)) (.cv p)
      (syn_cfrec G (syn_ctc D)) p0033
  have p0035 :=
    @g_breq2d (.classEq (syn_ctc (.cv n)) (.cv p))
      (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n)))
      (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)) (syn_ctc C) (syn_clec) p0034
  have p0036 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc))
          (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p)))
      (.classEq (syn_ctc (.cv n)) (.cv p))
      (syn_wb (syn_wbr (syn_ctc C) (syn_clec)
          (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n))))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      p0032 p0035
  have p0037 :=
    @g_mpbird
      (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc))
          (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p)))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n))))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))) p0031
      p0036
  have p0039 :=
    @g_a1i (.classMem C (syn_cncs)) (.classMem (.cv n) (syn_cnnc))
      hyp_wppreachorbitextcbidv_8
  have p0040 :=
    @g_a1i
      (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs)))
      (.classMem (.cv n) (syn_cnnc)) hyp_wppreachorbitextcbidv_9
  have p0041 := @g_id (.classEq (.cv r) (.cv n))
  have p0042 := @g_fveq2d (.classEq (.cv r) (.cv n)) (.cv r) (.cv n) (syn_cfrec F D) p0041
  have p0043 :=
    @g_eleq1d (.classEq (.cv r) (.cv n)) (syn_cfv (syn_cfrec F D) (.cv r))
      (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs) p0042
  have p0044 :=
    @g_rspcv (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs))
      (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs)) r (.cv n) (syn_cnnc)
      dv_cache_0012 dv_cache_0002 dv_cache_0013 p0043
  have p0045 :=
    @g_mpd (.classMem (.cv n) (syn_cnnc))
      (syn_wral r (syn_cnnc) (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs)))
      (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs)) p0040 p0044
  have p0046 :=
    @g_jca (.classMem (.cv n) (syn_cnnc)) (.classMem C (syn_cncs))
      (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs)) p0039 p0045
  have p0047 := @g_tlecg C (syn_cfv (syn_cfrec F D) (.cv n))
  have p0048 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (syn_wa (.classMem C (syn_cncs)) (.classMem (syn_cfv (syn_cfrec F D) (.cv n)) (syn_cncs)))
      (syn_wb (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv n)))))
      p0046 p0047
  have p0049 :=
    @g_frectchom0 x F G D (.cv n) dv_cache_0004 dv_cache_0005 dv_cache_0006
      hyp_wppreachorbitextcbidv_1 hyp_wppreachorbitextcbidv_2 hyp_wppreachorbitextcbidv_3
      hyp_wppreachorbitextcbidv_4 hyp_wppreachorbitextcbidv_5 hyp_wppreachorbitextcbidv_6
      hyp_wppreachorbitextcbidv_7
  have p0050 :=
    @g_breq2d (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv n)))
      (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n))) (syn_ctc C) (syn_clec) p0049
  have p0051 :=
    @g_bitrd (.classMem (.cv n) (syn_cnnc))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_ctc (syn_cfv (syn_cfrec F D) (.cv n))))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n))))
      p0048 p0050
  have p0052 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc))
          (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p)))
      (.classMem (.cv n) (syn_cnnc))
      (syn_wb (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n)))))
      p0028 p0051
  have p0053 :=
    @g_mpbird
      (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc))
          (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p)))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n)))
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (syn_ctc (.cv n))))
      p0037 p0052
  have p0054 :=
    @g_jca
      (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc))
          (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p)))
      (.classMem (.cv n) (syn_cnnc))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) p0028 p0053
  have p0055 := @g_id (.classEq (.cv a) (.cv n))
  have p0056 := @g_fveq2d (.classEq (.cv a) (.cv n)) (.cv a) (.cv n) (syn_cfrec F D) p0055
  have p0057 :=
    @g_breq2d (.classEq (.cv a) (.cv n)) (syn_cfv (syn_cfrec F D) (.cv a))
      (syn_cfv (syn_cfrec F D) (.cv n)) C (syn_clec) p0056
  have p0058 :=
    @g_rspcev (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) a (.cv n) (syn_cnnc)
      dv_cache_0014 dv_cache_0015 dv_cache_0016 p0057
  have p0059 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv p) (syn_cnnc))
          (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv p)))
      (syn_wa (.classMem (.cv n) (syn_cnnc))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))
      (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))
      p0054 p0058
  have p0060 :=
    @g_rexlimdv3a
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      (.classEq (syn_ctc (.cv n)) (.cv p))
      (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) n
      (syn_cnnc) dv_cache_0017 dv_cache_0018 p0059
  have p0061 :=
    @g_mpd
      (syn_wa (.classMem (.cv p) (syn_cnnc))
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      (syn_wrex n (syn_cnnc) (.classEq (syn_ctc (.cv n)) (.cv p)))
      (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))
      p0027 p0060
  have p0062 :=
    @g_rexlimiva
      (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p)))
      (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a)))) p
      (syn_cnnc) dv_cache_0019 p0061
  have p0063 :=
    @g_impbii
      (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))
      (syn_wrex p (syn_cnnc)
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      p0024 p0062
  exact p0063

@[expose]
noncomputable def g_wppreachorbitfnvndv (C : Class) (F : Class)
    (hyp_wppreachorbitfnvndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (syn_wfn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_cnnc)) :=
  by
  have p0000 := @g_wppreachopfn F hyp_wppreachorbitfnvndv_1
  have p0001 := @g_fnfun (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_cnvex F hyp_wppreachorbitfnvndv_1
  have p0004 := @g_imageex (syn_ccnv F) p0003
  have p0005 := @g_elfuns (syn_cimage (syn_ccnv F)) p0004
  have p0006 :=
    @g_mpbir (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
      (syn_wfun (syn_cimage (syn_ccnv F))) p0002 p0005
  have p0007 := @g_wppreachupperex C
  have p0009 := @g_fndm (syn_cvv) (syn_cimage (syn_ccnv F))
  have p0010 := Nominal.mp p0000 p0009
  have p0011 :=
    @g_eleqtrri (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
      (syn_cdm (syn_cimage (syn_ccnv F))) p0007 p0010
  have p0012 := @g_ssv (syn_crn (syn_cimage (syn_ccnv F)))
  have p0016 :=
    @g_sseqtr4i (syn_crn (syn_cimage (syn_ccnv F))) (syn_cvv)
      (syn_cdm (syn_cimage (syn_ccnv F))) p0012 p0010
  have p0017 :=
    @g_n_3pm3_2i (.classMem (syn_cimage (syn_ccnv F)) (syn_cfuns))
      (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cdm (syn_cimage (syn_ccnv F))))
      (syn_wss (syn_crn (syn_cimage (syn_ccnv F))) (syn_cdm (syn_cimage (syn_ccnv F))))
      p0006 p0011 p0016
  have p0018 :=
    @g_wpporbitfnndv (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))
  have p0019 := Nominal.mp p0017 p0018
  exact p0019

@[expose]
noncomputable def g_elwppreachvndv (C : Class) (D : Class) (n : Var) (F : Class)
    (dv_C_n : n ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_F_n : n ∉ F.fv)
    (hyp_elwppreachvndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem D (syn_cwppreach F C)) (syn_wrex n (syn_cnnc) (.classMem D (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
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
    n ∉ ((syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))).fv :=
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
      ((syn_cdm (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))).fv :=
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
  have dv_cache_0004 : n ∉ ((syn_cnnc)).fv :=
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
  have p0000 := (Nominal.classEqRefl (syn_cwppreach F C))
  have p0001 :=
    @g_eleq2i (syn_cwppreach F C)
      (syn_cuni
        (syn_crn (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))))
      D p0000
  have p0002 := @g_wppreachorbitfnvndv C F hyp_elwppreachvndv_1
  have p0003 :=
    @g_fnfun (syn_cnnc)
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_elunirn n D (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
      dv_cache_0001 dv_cache_0002
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_bitri (.classMem D (syn_cwppreach F C))
      (.classMem D (syn_cuni (syn_crn
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))))
      (syn_wrex n
        (syn_cdm (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
        (.classMem D
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (.cv n))))
      p0001 p0006
  have p0009 :=
    @g_fndm (syn_cnnc)
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
  have p0010 := Nominal.mp p0002 p0009
  have p0011 :=
    @g_rexeqi
      (.classMem D
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (.cv n)))
      n (syn_cdm (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
      (syn_cnnc) dv_cache_0003 dv_cache_0004 p0010
  have p0012 :=
    @g_bitri (.classMem D (syn_cwppreach F C))
      (syn_wrex n
        (syn_cdm (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
        (.classMem D
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (.cv n))))
      (syn_wrex n (syn_cnnc) (.classMem D
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
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

@[expose]
noncomputable def g_wppnnstageextcbidv (D : Class) (H : Class) (p : Var) (a : Var)
    (dv_D_a : a ∉ D.fv) (dv_D_p : p ∉ D.fv) (dv_H_a : a ∉ H.fv) (dv_H_p : p ∉ H.fv)
    (dv_a_p : a ≠ p) :
    Nominal.NPrf
      (syn_wb (syn_wrex a (syn_cnnc) (.classMem D (syn_cfv H (.cv a))))
        (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p)))))) :=
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
  have dv_cache_0003 : p ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0004 : p ∉ ((Wff.classMem D (syn_cfv H (syn_ctc (.cv n))))).fv :=
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
    n ∉ ((syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p)))))).fv :=
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
    n ∉ ((syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))).fv :=
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
    a ∉ ((syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p)))))).fv :=
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
  have dv_cache_0008 : a ∉ ((syn_ctc (.cv p))).fv :=
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
  have dv_cache_0009 : a ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0010 : a ∉ ((Wff.classMem D (syn_cfv H (syn_ctc (.cv p))))).fv :=
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
    p ∉ ((syn_wrex a (syn_cnnc) (.classMem D (syn_cfv H (.cv a))))).fv :=
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
  have p0000 := @g_simpl (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))
  have p0001 := @g_nntcpreim n (.cv a) dv_cache_0001
  have p0002 :=
    @g_syl (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
      (.classMem (.cv a) (syn_cnnc))
      (syn_wrex n (syn_cnnc) (.classEq (syn_ctc (.cv n)) (.cv a))) p0000 p0001
  have p0003 :=
    @g_simp2 (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
      (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))
  have p0004 :=
    @g_simp1 (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
      (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))
  have p0005 := @g_simpr (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a)))
  have p0006 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a)))
      (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
      (.classMem D (syn_cfv H (.cv a))) p0004 p0005
  have p0007 :=
    @g_simp3 (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
      (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a))
  have p0008 := @g_id (.classEq (syn_ctc (.cv n)) (.cv a))
  have p0009 :=
    @g_fveq2d (.classEq (syn_ctc (.cv n)) (.cv a)) (syn_ctc (.cv n)) (.cv a) H p0008
  have p0010 :=
    @g_eleq2d (.classEq (syn_ctc (.cv n)) (.cv a)) (syn_cfv H (syn_ctc (.cv n)))
      (syn_cfv H (.cv a)) D p0009
  have p0011 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a)))
      (.classEq (syn_ctc (.cv n)) (.cv a))
      (syn_wb (.classMem D (syn_cfv H (syn_ctc (.cv n)))) (.classMem D (syn_cfv H (.cv a))))
      p0007 p0010
  have p0012 :=
    @g_mpbird
      (syn_w3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a)))
      (.classMem D (syn_cfv H (syn_ctc (.cv n)))) (.classMem D (syn_cfv H (.cv a))) p0006
      p0011
  have p0013 :=
    @g_jca
      (syn_w3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a)))
      (.classMem (.cv n) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv n)))) p0003
      p0012
  have p0014 := @g_tceq (.cv p) (.cv n)
  have p0015 :=
    @g_fveq2d (.classEq (.cv p) (.cv n)) (syn_ctc (.cv p)) (syn_ctc (.cv n)) H p0014
  have p0016 :=
    @g_eleq2d (.classEq (.cv p) (.cv n)) (syn_cfv H (syn_ctc (.cv p)))
      (syn_cfv H (syn_ctc (.cv n))) D p0015
  have p0017 :=
    @g_rspcev (.classMem D (syn_cfv H (syn_ctc (.cv p))))
      (.classMem D (syn_cfv H (syn_ctc (.cv n)))) p (.cv n) (syn_cnnc) dv_cache_0002
      dv_cache_0003 dv_cache_0004 p0016
  have p0018 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
        (.classMem (.cv n) (syn_cnnc)) (.classEq (syn_ctc (.cv n)) (.cv a)))
      (syn_wa (.classMem (.cv n) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv n)))))
      (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) p0013 p0017
  have p0019 :=
    @g_rexlimdv3a
      (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
      (.classEq (syn_ctc (.cv n)) (.cv a))
      (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) n (syn_cnnc)
      dv_cache_0005 dv_cache_0006 p0018
  have p0020 :=
    @g_mpd (syn_wa (.classMem (.cv a) (syn_cnnc)) (.classMem D (syn_cfv H (.cv a))))
      (syn_wrex n (syn_cnnc) (.classEq (syn_ctc (.cv n)) (.cv a)))
      (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) p0002 p0019
  have p0021 :=
    @g_rexlimiva (.classMem D (syn_cfv H (.cv a)))
      (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) a (syn_cnnc)
      dv_cache_0007 p0020
  have p0022 :=
    @g_simpl (.classMem (.cv p) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p))))
  have p0023 := @g_nntccl (.cv p)
  have p0024 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p)))))
      (.classMem (.cv p) (syn_cnnc)) (.classMem (syn_ctc (.cv p)) (syn_cnnc)) p0022 p0023
  have p0025 :=
    @g_simpr (.classMem (.cv p) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p))))
  have p0026 :=
    @g_jca
      (syn_wa (.classMem (.cv p) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p)))))
      (.classMem (syn_ctc (.cv p)) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p))))
      p0024 p0025
  have p0027 := @g_id (.classEq (.cv a) (syn_ctc (.cv p)))
  have p0028 :=
    @g_fveq2d (.classEq (.cv a) (syn_ctc (.cv p))) (.cv a) (syn_ctc (.cv p)) H p0027
  have p0029 :=
    @g_eleq2d (.classEq (.cv a) (syn_ctc (.cv p))) (syn_cfv H (.cv a))
      (syn_cfv H (syn_ctc (.cv p))) D p0028
  have p0030 :=
    @g_rspcev (.classMem D (syn_cfv H (.cv a)))
      (.classMem D (syn_cfv H (syn_ctc (.cv p)))) a (syn_ctc (.cv p)) (syn_cnnc)
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0029
  have p0031 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_cnnc)) (.classMem D (syn_cfv H (syn_ctc (.cv p)))))
      (syn_wa (.classMem (syn_ctc (.cv p)) (syn_cnnc))
        (.classMem D (syn_cfv H (syn_ctc (.cv p)))))
      (syn_wrex a (syn_cnnc) (.classMem D (syn_cfv H (.cv a)))) p0026 p0030
  have p0032 :=
    @g_rexlimiva (.classMem D (syn_cfv H (syn_ctc (.cv p))))
      (syn_wrex a (syn_cnnc) (.classMem D (syn_cfv H (.cv a)))) p (syn_cnnc) dv_cache_0011
      p0031
  have p0033 :=
    @g_impbii (syn_wrex a (syn_cnnc) (.classMem D (syn_cfv H (.cv a))))
      (syn_wrex p (syn_cnnc) (.classMem D (syn_cfv H (syn_ctc (.cv p))))) p0021 p0032
  exact p0033

@[expose]
noncomputable def g_wppreachtcrexvndv (C : Class) (D : Class) (n : Var) (F : Class)
    (dv_C_n : n ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_F_n : n ∉ F.fv)
    (hyp_wppreachtcrexvndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem D (syn_cwppreach F C)) (syn_wrex n (syn_cnnc) (.classMem D (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv n)))))) :=
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
    m ∉ ((syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))).fv :=
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
    n ∉ ((syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))).fv :=
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
    @g_elwppreachvndv C D m F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppreachtcrexvndv_1
  have p0001 :=
    @g_wppnnstageextcbidv D
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) n m
      dv_cache_0002 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0002 :=
    @g_bitri (.classMem D (syn_cwppreach F C))
      (syn_wrex m (syn_cnnc) (.classMem D
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (.cv m))))
      (syn_wrex n (syn_cnnc) (.classMem D
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv n)))))
      p0000 p0001
  exact p0002

@[expose]
noncomputable def g_wppreachlayerorbvndv (C : Class) (D : Class) (F : Class) (N : Class)
    (hyp_wppreachlayerorbvndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppreachlayerorbvndv_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wppreachlayerorbvndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppreachlayerorbvndv_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem D (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N)))) :=
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
      ((Wff.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem D (syn_cfv
                (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
                (syn_ctc N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N))))).fv :=
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
  have p0000 := @g_eqidd (.classEq (.cv c) C) (syn_cimage (syn_ccnv F))
  have p0001 := @g_id (.classEq (.cv c) C)
  have p0002 := @g_sneqd (.classEq (.cv c) C) (.cv c) C p0001
  have p0003 :=
    @g_imaeq2d (.classEq (.cv c) C) (syn_csn (.cv c)) (syn_csn C) (syn_clec) p0002
  have p0004 :=
    @g_jca (.classEq (.cv c) C)
      (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F)))
      (.classEq (syn_cima (syn_clec) (syn_csn (.cv c))) (syn_cima (syn_clec) (syn_csn C)))
      p0000 p0003
  have p0005 :=
    @g_freceq12 (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F))
      (syn_cima (syn_clec) (syn_csn (.cv c))) (syn_cima (syn_clec) (syn_csn C))
  have p0006 :=
    @g_syl (.classEq (.cv c) C)
      (syn_wa (.classEq (syn_cimage (syn_ccnv F)) (syn_cimage (syn_ccnv F)))
        (.classEq (syn_cima (syn_clec) (syn_csn (.cv c))) (syn_cima (syn_clec) (syn_csn C))))
      (.classEq (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c))))
        (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))))
      p0004 p0005
  have p0007 :=
    @g_fveq1d (.classEq (.cv c) C) (syn_ctc N)
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c))))
      (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C))) p0006
  have p0008 :=
    @g_eleq2d (.classEq (.cv c) C)
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c))))
        (syn_ctc N))
      (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_ctc N))
      D p0007
  have p0010 :=
    @g_breq1d (.classEq (.cv c) C) (.cv c) C (syn_cfv (syn_cfrec F D) N) (syn_clec) p0001
  have p0011 :=
    @g_bibi12d (.classEq (.cv c) C)
      (.classMem D (syn_cfv
          (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c))))
          (syn_ctc N)))
      (.classMem D
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc N)))
      (syn_wbr (.cv c) (syn_clec) (syn_cfv (syn_cfrec F D) N))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N)) p0008 p0010
  have p0012 :=
    @g_imbi2d (.classEq (.cv c) C)
      (syn_wb (.classMem D (syn_cfv
            (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c))))
            (syn_ctc N))) (syn_wbr (.cv c) (syn_clec) (syn_cfv (syn_cfrec F D) N)))
      (syn_wb (.classMem D
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N)))
      (.classMem N (syn_cnnc)) p0011
  have p0013 :=
    @g_wppreachlayerorbfin (.cv c) D F N dv_cache_0001 hyp_wppreachlayerorbvndv_1
      hyp_wppreachlayerorbvndv_2 hyp_wppreachlayerorbvndv_3
  have p0014 :=
    @g_vtoclg
      (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem D (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn (.cv c))))
              (syn_ctc N))) (syn_wbr (.cv c) (syn_clec) (syn_cfv (syn_cfrec F D) N))))
      (.imp (.classMem N (syn_cnnc)) (syn_wb (.classMem D (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc N))) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) N))))
      c C (syn_cvv) dv_cache_0002 dv_cache_0003 p0012 p0013
  have p0015 := Nominal.mp hyp_wppreachlayerorbvndv_4 p0014
  exact p0015

@[expose]
noncomputable def g_wppreachlayerorbrexvndv (C : Class) (D : Class) (n : Var) (F : Class)
    (_dv_C_n : n ∉ C.fv) (_dv_D_n : n ∉ D.fv) (_dv_F_n : n ∉ F.fv)
    (hyp_wppreachlayerorbrexvndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppreachlayerorbrexvndv_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wppreachlayerorbrexvndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppreachlayerorbrexvndv_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (syn_wrex n (syn_cnnc) (.classMem D (syn_cfv
              (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
              (syn_ctc (.cv n))))) (syn_wrex n (syn_cnnc)
          (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))) :=
  by
  have p0000 :=
    @g_wppreachlayerorbvndv C D F (.cv n) hyp_wppreachlayerorbrexvndv_1
      hyp_wppreachlayerorbrexvndv_2 hyp_wppreachlayerorbrexvndv_3
      hyp_wppreachlayerorbrexvndv_4
  have p0001 :=
    @g_rexbiia
      (.classMem D
        (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
          (syn_ctc (.cv n))))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))) n (syn_cnnc) p0000
  exact p0001

@[expose]
noncomputable def g_wppreachfwdrexvndv (C : Class) (D : Class) (n : Var) (F : Class)
    (dv_C_n : n ∉ C.fv) (dv_D_n : n ∉ D.fv) (dv_F_n : n ∉ F.fv)
    (hyp_wppreachfwdrexvndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppreachfwdrexvndv_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wppreachfwdrexvndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppreachfwdrexvndv_4 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem D (syn_cwppreach F C)) (syn_wrex n (syn_cnnc)
          (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))) :=
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
  have p0000 := @g_elex F (syn_cfuns)
  have p0001 := Nominal.mp hyp_wppreachfwdrexvndv_1 p0000
  have p0002 :=
    @g_wppreachtcrexvndv C D n F dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @g_wppreachlayerorbrexvndv C D n F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppreachfwdrexvndv_1 hyp_wppreachfwdrexvndv_2 hyp_wppreachfwdrexvndv_3
      hyp_wppreachfwdrexvndv_4
  have p0004 :=
    @g_bitri (.classMem D (syn_cwppreach F C))
      (syn_wrex n (syn_cnnc) (.classMem D
          (syn_cfv (syn_cfrec (syn_cimage (syn_ccnv F)) (syn_cima (syn_clec) (syn_csn C)))
            (syn_ctc (.cv n)))))
      (syn_wrex n (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv n))))
      p0002 p0003
  exact p0004

@[expose]
noncomputable def g_wppreachtcbidv (x : Var) (C : Class) (D : Class) (F : Class)
    (G : Class) (r : Var) (dv_D_r : r ∉ D.fv) (dv_D_x : x ∉ D.fv) (dv_F_r : r ∉ F.fv)
    (dv_F_x : x ∉ F.fv) (dv_G_x : x ∉ G.fv)
    (hyp_wppreachtcbidv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppreachtcbidv_2 : Nominal.NPrf (.classMem D (syn_cdm F)))
    (hyp_wppreachtcbidv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppreachtcbidv_4 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_wppreachtcbidv_5 : Nominal.NPrf (.classMem (syn_ctc D) (syn_cdm G)))
    (hyp_wppreachtcbidv_6 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G)))
    (hyp_wppreachtcbidv_7 : Nominal.NPrf (syn_wral x (syn_cdm F)
          (.classEq (syn_ctc (syn_cfv F (.cv x))) (syn_cfv G (syn_ctc (.cv x))))))
    (hyp_wppreachtcbidv_8 : Nominal.NPrf (.classMem C (syn_cncs)))
    (hyp_wppreachtcbidv_9 : Nominal.NPrf (syn_wral r (syn_cnnc)
          (.classMem (syn_cfv (syn_cfrec F D) (.cv r)) (syn_cncs)))) :
    Nominal.NPrf
      (syn_wb (.classMem D (syn_cwppreach F C))
        (.classMem (syn_ctc D) (syn_cwppreach G (syn_ctc C)))) :=
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
  have dv_cache_0016 : p ∉ ((syn_ctc C)).fv :=
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
  have dv_cache_0017 : p ∉ ((syn_ctc D)).fv :=
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
  have p0000 := @g_elex C (syn_cncs)
  have p0001 := Nominal.mp hyp_wppreachtcbidv_8 p0000
  have p0002 :=
    @g_wppreachfwdrexvndv C D a F dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppreachtcbidv_1 hyp_wppreachtcbidv_2 hyp_wppreachtcbidv_3 p0001
  have p0003 :=
    @g_wppreachorbitextcbidv x C D F G r p a dv_cache_0001 dv_cache_0004 dv_cache_0002
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0003 dv_cache_0008 dv_cache_0009
      dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
      hyp_wppreachtcbidv_1 hyp_wppreachtcbidv_2 hyp_wppreachtcbidv_3 hyp_wppreachtcbidv_4
      hyp_wppreachtcbidv_5 hyp_wppreachtcbidv_6 hyp_wppreachtcbidv_7 hyp_wppreachtcbidv_8
      hyp_wppreachtcbidv_9
  have p0004 :=
    @g_bitri (.classMem D (syn_cwppreach F C))
      (syn_wrex a (syn_cnnc) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F D) (.cv a))))
      (syn_wrex p (syn_cnnc)
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      p0002 p0003
  have p0005 := @g_tccl C
  have p0006 := Nominal.mp hyp_wppreachtcbidv_8 p0005
  have p0007 := @g_elex (syn_ctc C) (syn_cncs)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_wppreachfwdrexvndv (syn_ctc C) (syn_ctc D) p G dv_cache_0016 dv_cache_0017
      dv_cache_0012 hyp_wppreachtcbidv_4 hyp_wppreachtcbidv_5 hyp_wppreachtcbidv_6 p0008
  have p0010 :=
    @g_bitr4i (.classMem D (syn_cwppreach F C))
      (syn_wrex p (syn_cnnc)
        (syn_wbr (syn_ctc C) (syn_clec) (syn_cfv (syn_cfrec G (syn_ctc D)) (.cv p))))
      (.classMem (syn_ctc D) (syn_cwppreach G (syn_ctc C))) p0004 p0009
  exact p0010

@[expose]
noncomputable def g_elhwcardsweclndv (K : Class) (s : Var) (d : Var) (dv_K_d : d ∉ K.fv)
    (dv_K_s : s ∉ K.fv) (dv_d_s : d ≠ s) :
    Nominal.NPrf
      (.imp (.classMem K (syn_cvv)) (syn_wb (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d
            (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
                (.classEq K (syn_cnc (.cv d)))))))) :=
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
      ((syn_wb (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s
              (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
                (.classEq K (syn_cnc (.cv d)))))))).fv :=
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
  have p0000 := @g_id (.classEq (.cv k) K)
  have p0001 := @g_eleq1d (.classEq (.cv k) K) (.cv k) K (syn_chwcards (syn_cvv)) p0000
  have p0003 := @g_eqeq1d (.classEq (.cv k) K) (.cv k) K (syn_cnc (.cv d)) p0000
  have p0004 :=
    @g_anbi2d (.classEq (.cv k) K) (.classEq (.cv k) (syn_cnc (.cv d)))
      (.classEq K (syn_cnc (.cv d))) (syn_wbr (.cv s) (syn_cwe) (.cv d)) p0003
  have p0005 :=
    @g_exbidv (.classEq (.cv k) K)
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) s
      dv_cache_0001 p0004
  have p0006 :=
    @g_exbidv (.classEq (.cv k) K)
      (syn_wex s
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))
      (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
      d dv_cache_0002 p0005
  have p0007 :=
    @g_bibi12d (.classEq (.cv k) K) (.classMem (.cv k) (syn_chwcards (syn_cvv)))
      (.classMem K (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d))
            (.classEq (.cv k) (syn_cnc (.cv d))))))
      (syn_wex d (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))))
      p0001 p0006
  have p0008 := @g_elhwcardswev k s d dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0009 :=
    @g_vtoclg
      (syn_wb (.classMem (.cv k) (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s
            (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq (.cv k) (syn_cnc (.cv d)))))))
      (syn_wb (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s
            (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))))
      k K (syn_cvv) dv_cache_0006 dv_cache_0007 p0007 p0008
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

@[expose]
noncomputable def g_hwcardstcclndv (K : Class) :
    Nominal.NPrf
      (.imp (.classMem K (syn_chwcards (syn_cvv)))
        (.classMem (syn_ctc K) (syn_chwcards (syn_cvv)))) :=
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
  have dv_cache_0004 : y ∉ ((syn_csi (.cv s))).fv :=
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
      ((syn_wa (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d)))
          (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))).fv :=
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
  have dv_cache_0006 : y ∉ ((Wff.classEq (.cv x) (syn_cpw1 (.cv d)))).fv :=
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
  have dv_cache_0007 : x ∉ ((syn_cpw1 (.cv d))).fv :=
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
      ((syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d)))
            (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))))).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_ctc K)).fv :=
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
  have dv_cache_0010 : y ∉ ((syn_ctc K)).fv :=
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
  have dv_cache_0012 : d ∉ ((Wff.classMem (syn_ctc K) (syn_chwcards (syn_cvv)))).fv :=
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
  have dv_cache_0013 : s ∉ ((Wff.classMem (syn_ctc K) (syn_chwcards (syn_cvv)))).fv :=
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
  have p0000 := @g_id (.classMem K (syn_chwcards (syn_cvv)))
  have p0002 := @g_elex K (syn_chwcards (syn_cvv))
  have p0003 :=
    @g_syl (.classMem K (syn_chwcards (syn_cvv))) (.classMem K (syn_chwcards (syn_cvv)))
      (.classMem K (syn_cvv)) p0000 p0002
  have p0004 := @g_elhwcardsweclndv K s d dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    @g_syl (.classMem K (syn_chwcards (syn_cvv))) (.classMem K (syn_cvv))
      (syn_wb (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex s
            (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))))
      p0003 p0004
  have p0006 :=
    @g_mpbid (.classMem K (syn_chwcards (syn_cvv))) (.classMem K (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))))
      p0000 p0005
  have p0007 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0008 := @g_siwendv (.cv d) (.cv s)
  have p0009 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_wbr (.cv s) (syn_cwe) (.cv d))
      (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d))) p0007 p0008
  have p0010 :=
    @g_simpr (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0011 := @g_tceq K (syn_cnc (.cv d))
  have p0012 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (.classEq K (syn_cnc (.cv d))) (.classEq (syn_ctc K) (syn_ctc (syn_cnc (.cv d))))
      p0010 p0011
  have p0014 := @g_brex (.cv s) (.cv d) (syn_cwe)
  have p0015 := @g_simpr (.classMem (.cv s) (syn_cvv)) (.classMem (.cv d) (syn_cvv))
  have p0016 :=
    @g_syl (syn_wbr (.cv s) (syn_cwe) (.cv d))
      (syn_wa (.classMem (.cv s) (syn_cvv)) (.classMem (.cv d) (syn_cvv)))
      (.classMem (.cv d) (syn_cvv)) p0014 p0015
  have p0017 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classMem (.cv d) (syn_cvv)) p0007 p0016
  have p0018 := @g_tcncg (.cv d) (syn_cvv)
  have p0019 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (.classMem (.cv d) (syn_cvv))
      (.classEq (syn_ctc (syn_cnc (.cv d))) (syn_cnc (syn_cpw1 (.cv d)))) p0017 p0018
  have p0020 :=
    @g_eqtrd (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_ctc K) (syn_ctc (syn_cnc (.cv d))) (syn_cnc (syn_cpw1 (.cv d))) p0012 p0019
  have p0021 :=
    @g_jca (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d)))
      (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))) p0009 p0020
  have p0024 := @g_simpl (.classMem (.cv s) (syn_cvv)) (.classMem (.cv d) (syn_cvv))
  have p0025 :=
    @g_syl (syn_wbr (.cv s) (syn_cwe) (.cv d))
      (syn_wa (.classMem (.cv s) (syn_cvv)) (.classMem (.cv d) (syn_cvv)))
      (.classMem (.cv s) (syn_cvv)) p0014 p0024
  have p0026 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classMem (.cv s) (syn_cvv)) p0007 p0025
  have p0027 := @g_siexg (.cv s) (syn_cvv)
  have p0028 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (.classMem (.cv s) (syn_cvv)) (.classMem (syn_csi (.cv s)) (syn_cvv)) p0026 p0027
  have p0029 := @g_id (.classEq (.cv y) (syn_csi (.cv s)))
  have p0030 :=
    @g_breq1d (.classEq (.cv y) (syn_csi (.cv s))) (.cv y) (syn_csi (.cv s))
      (syn_cpw1 (.cv d)) (syn_cwe) p0029
  have p0031 :=
    @g_anbi1d (.classEq (.cv y) (syn_csi (.cv s)))
      (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d)))
      (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d)))
      (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))) p0030
  have p0032 :=
    @g_spcegv
      (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d)))
        (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))
      (syn_wa (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d)))
        (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))
      y (syn_csi (.cv s)) (syn_cvv) dv_cache_0004 dv_cache_0005 p0031
  have p0033 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (.classMem (syn_csi (.cv s)) (syn_cvv))
      (.imp (syn_wa (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d)))
          (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))) (syn_wex y
          (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d)))
            (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))))
      p0028 p0032
  have p0034 :=
    @g_mpd (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_wa (syn_wbr (syn_csi (.cv s)) (syn_cwe) (syn_cpw1 (.cv d)))
        (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))
      (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d)))
          (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))))
      p0021 p0033
  have p0040 := @g_pw1exg (.cv d) (syn_cvv)
  have p0041 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (.classMem (.cv d) (syn_cvv)) (.classMem (syn_cpw1 (.cv d)) (syn_cvv)) p0017 p0040
  have p0042 := @g_id (.classEq (.cv x) (syn_cpw1 (.cv d)))
  have p0043 :=
    @g_breq2d (.classEq (.cv x) (syn_cpw1 (.cv d))) (.cv x) (syn_cpw1 (.cv d)) (.cv y)
      (syn_cwe) p0042
  have p0045 :=
    @g_nceqd (.classEq (.cv x) (syn_cpw1 (.cv d))) (.cv x) (syn_cpw1 (.cv d)) p0042
  have p0046 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cpw1 (.cv d))) (syn_cnc (.cv x))
      (syn_cnc (syn_cpw1 (.cv d))) (syn_ctc K) p0045
  have p0047 :=
    @g_anbi12d (.classEq (.cv x) (syn_cpw1 (.cv d))) (syn_wbr (.cv y) (syn_cwe) (.cv x))
      (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d)))
      (.classEq (syn_ctc K) (syn_cnc (.cv x)))
      (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))) p0043 p0046
  have p0048 :=
    @g_exbidv (.classEq (.cv x) (syn_cpw1 (.cv d)))
      (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x)) (.classEq (syn_ctc K) (syn_cnc (.cv x))))
      (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d)))
        (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))
      y dv_cache_0006 p0047
  have p0049 :=
    @g_spcegv
      (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x))
          (.classEq (syn_ctc K) (syn_cnc (.cv x)))))
      (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d)))
          (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))))
      x (syn_cpw1 (.cv d)) (syn_cvv) dv_cache_0007 dv_cache_0008 p0048
  have p0050 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (.classMem (syn_cpw1 (.cv d)) (syn_cvv))
      (.imp (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d)))
            (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d)))))) (syn_wex x (syn_wex y
            (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x))
              (.classEq (syn_ctc K) (syn_cnc (.cv x)))))))
      p0041 p0049
  have p0051 :=
    @g_mpd (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (syn_cpw1 (.cv d)))
          (.classEq (syn_ctc K) (syn_cnc (syn_cpw1 (.cv d))))))
      (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x))
            (.classEq (syn_ctc K) (syn_cnc (.cv x))))))
      p0034 p0050
  have p0052 := @g_tcex K
  have p0053 :=
    @g_elhwcardsweclndv (syn_ctc K) y x dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0054 := Nominal.mp p0052 p0053
  have p0055 :=
    @g_biimpri (.classMem (syn_ctc K) (syn_chwcards (syn_cvv)))
      (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x))
            (.classEq (syn_ctc K) (syn_cnc (.cv x))))))
      p0054
  have p0056 :=
    @g_syl (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_wex x (syn_wex y (syn_wa (syn_wbr (.cv y) (syn_cwe) (.cv x))
            (.classEq (syn_ctc K) (syn_cnc (.cv x))))))
      (.classMem (syn_ctc K) (syn_chwcards (syn_cvv))) p0051 p0055
  have p0057 :=
    @g_exlimivv
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (.classMem (syn_ctc K) (syn_chwcards (syn_cvv))) d s dv_cache_0012 dv_cache_0013
      p0056
  have p0058 :=
    @g_syl (.classMem K (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))))
      (.classMem (syn_ctc K) (syn_chwcards (syn_cvv))) p0006 p0057
  exact p0058

@[expose]
noncomputable def g_hwcardsdownltcndv (C : Class) (d : Var) :
    Nominal.NPrf
      (.imp (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_chwcards (syn_cvv)))) :=
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
  have dv_cache_0008 : a ∉ ((syn_cin (.cv r) (syn_cxp (.cv x) (.cv x)))).fv :=
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
  have dv_cache_0009 : s ∉ ((syn_cin (.cv r) (syn_cxp (.cv x) (.cv x)))).fv :=
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
      ((syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x))
          (.classEq (.cv d) (syn_cnc (.cv x))))).fv :=
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
      ((syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x))
          (.classEq (.cv d) (syn_cnc (.cv x))))).fv :=
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
  have dv_cache_0015 : x ∉ ((Wff.classMem (.cv d) (syn_chwcards (syn_cvv)))).fv :=
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
      ((syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C)) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e))
            (.classEq C (syn_cnc (.cv e)))))).fv :=
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
  have dv_cache_0017 : e ∉ ((Wff.classMem (.cv d) (syn_chwcards (syn_cvv)))).fv :=
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
  have dv_cache_0018 : r ∉ ((Wff.classMem (.cv d) (syn_chwcards (syn_cvv)))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))).fv :=
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
    @g_simpl
      (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
      (syn_wbr (.cv d) (syn_clec) C)
  have p0001 :=
    @g_simpr (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
      (.classMem C (syn_chwcards (syn_cvv))) p0000 p0001
  have p0006 := @g_elex C (syn_chwcards (syn_cvv))
  have p0007 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (.classMem C (syn_chwcards (syn_cvv))) (.classMem C (syn_cvv)) p0002 p0006
  have p0008 := @g_elhwcardsweclndv C r e dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0009 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (.classMem C (syn_cvv))
      (syn_wb (.classMem C (syn_chwcards (syn_cvv))) (syn_wex e (syn_wex r
            (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))))
      p0007 p0008
  have p0010 :=
    @g_mpbid
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (.classMem C (syn_chwcards (syn_cvv)))
      (syn_wex e (syn_wex r
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))))
      p0002 p0009
  have p0011 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
  have p0012 :=
    @g_simpr
      (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
      (syn_wbr (.cv d) (syn_clec) C)
  have p0013 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (syn_wbr (.cv d) (syn_clec) C) p0011 p0012
  have p0014 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
  have p0015 :=
    @g_simpr (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))
  have p0016 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
      (.classEq C (syn_cnc (.cv e))) p0014 p0015
  have p0017 :=
    @g_breq2d
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      C (syn_cnc (.cv e)) (.cv d) (syn_clec) p0016
  have p0018 :=
    @g_mpbid
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wbr (.cv d) (syn_clec) C) (syn_wbr (.cv d) (syn_clec) (syn_cnc (.cv e))) p0013
      p0017
  have p0021 :=
    @g_simpl (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv)))
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
      (.classMem (.cv d) (syn_cncs)) p0000 p0021
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (.classMem (.cv d) (syn_cncs)) p0011 p0022
  have p0024 := @g_vex e
  have p0025 := @g_lenc x (.cv e) (.cv d) dv_cache_0004 dv_cache_0005 p0024
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (.classMem (.cv d) (syn_cncs))
      (syn_wb (syn_wbr (.cv d) (syn_clec) (syn_cnc (.cv e)))
        (syn_wrex x (.cv d) (syn_wss (.cv x) (.cv e))))
      p0023 p0025
  have p0027 :=
    @g_mpbid
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wbr (.cv d) (syn_clec) (syn_cnc (.cv e)))
      (syn_wrex x (.cv d) (syn_wss (.cv x) (.cv e))) p0018 p0026
  have p0028 :=
    @g_simpl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))
  have p0030 :=
    @g_simpl (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
      (syn_wbr (.cv r) (syn_cwe) (.cv e)) p0014 p0030
  have p0032 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wbr (.cv r) (syn_cwe) (.cv e)) p0028 p0031
  have p0033 :=
    @g_simpr
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))
  have p0034 := @g_simpr (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))
      (syn_wss (.cv x) (.cv e)) p0033 p0034
  have p0036 := @g_vex x
  have p0037 :=
    @g_a1i (.classMem (.cv x) (syn_cvv))
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      p0036
  have p0038 :=
    @g_werestrndv
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      (.cv x) (.cv e) (.cv r) p0032 p0035 p0037
  have p0040 := @g_simpl (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))
  have p0041 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e)))
      (.classMem (.cv x) (.cv d)) p0033 p0040
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (.classMem (.cv d) (syn_cncs)) p0028 p0023
  have p0049 := @g_ncseqnc (.cv d) (.cv x)
  have p0050 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      (.classMem (.cv d) (syn_cncs))
      (syn_wb (.classEq (.cv d) (syn_cnc (.cv x))) (.classMem (.cv x) (.cv d))) p0048
      p0049
  have p0051 :=
    @g_mpbird
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      (.classEq (.cv d) (syn_cnc (.cv x))) (.classMem (.cv x) (.cv d)) p0041 p0050
  have p0052 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x))
      (.classEq (.cv d) (syn_cnc (.cv x))) p0038 p0051
  have p0054 := @g_vex r
  have p0057 := @g_xpex (.cv x) (.cv x) p0036 p0036
  have p0058 := @g_inex (.cv r) (syn_cxp (.cv x) (.cv x)) p0054 p0057
  have p0059 :=
    @g_pm3_2i (.classMem (.cv x) (syn_cvv))
      (.classMem (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cvv)) p0036 p0058
  have p0060 :=
    @g_simpr (.classEq (.cv a) (.cv x))
      (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))))
  have p0061 :=
    @g_simpl (.classEq (.cv a) (.cv x))
      (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))))
  have p0062 :=
    @g_breq12d
      (syn_wa (.classEq (.cv a) (.cv x))
        (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x)))))
      (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (.cv a) (.cv x) (syn_cwe) p0060
      p0061
  have p0064 :=
    @g_nceqd
      (syn_wa (.classEq (.cv a) (.cv x))
        (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x)))))
      (.cv a) (.cv x) p0061
  have p0065 :=
    @g_eqeq2d
      (syn_wa (.classEq (.cv a) (.cv x))
        (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x)))))
      (syn_cnc (.cv a)) (syn_cnc (.cv x)) (.cv d) p0064
  have p0066 :=
    @g_anbi12d
      (syn_wa (.classEq (.cv a) (.cv x))
        (.classEq (.cv s) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x)))))
      (syn_wbr (.cv s) (syn_cwe) (.cv a))
      (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x))
      (.classEq (.cv d) (syn_cnc (.cv a))) (.classEq (.cv d) (syn_cnc (.cv x))) p0062
      p0065
  have p0067 :=
    @g_spc2egv
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv a)) (.classEq (.cv d) (syn_cnc (.cv a))))
      (syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x))
        (.classEq (.cv d) (syn_cnc (.cv x))))
      a s (.cv x) (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cvv) (syn_cvv)
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0066
  have p0068 := Nominal.mp p0059 p0067
  have p0069 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      (syn_wa (syn_wbr (syn_cin (.cv r) (syn_cxp (.cv x) (.cv x))) (syn_cwe) (.cv x))
        (.classEq (.cv d) (syn_cnc (.cv x))))
      (syn_wex a (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv a))
            (.classEq (.cv d) (syn_cnc (.cv a))))))
      p0052 p0068
  have p0070 := @g_elhwcardswev d s a dv_cache_0013 dv_cache_0012 dv_cache_0014
  have p0071 :=
    @g_biimpri (.classMem (.cv d) (syn_chwcards (syn_cvv)))
      (syn_wex a (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv a))
            (.classEq (.cv d) (syn_cnc (.cv a))))))
      p0070
  have p0072 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa
            (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
            (syn_wbr (.cv d) (syn_clec) C))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
        (syn_wa (.classMem (.cv x) (.cv d)) (syn_wss (.cv x) (.cv e))))
      (syn_wex a (syn_wex s (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv a))
            (.classEq (.cv d) (syn_cnc (.cv a))))))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0069 p0071
  have p0073 :=
    @g_rexlimdvaa
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wss (.cv x) (.cv e)) (.classMem (.cv d) (syn_chwcards (syn_cvv))) x (.cv d)
      dv_cache_0015 dv_cache_0016 p0072
  have p0074 :=
    @g_mpd
      (syn_wa (syn_wa
          (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
          (syn_wbr (.cv d) (syn_clec) C))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e)))))
      (syn_wrex x (.cv d) (syn_wss (.cv x) (.cv e)))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0027 p0073
  have p0075 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0074
  have p0076 :=
    @g_exlimdvv
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) e r dv_cache_0017 dv_cache_0018
      dv_cache_0019 dv_cache_0020 p0075
  have p0077 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv d) (syn_cncs)) (.classMem C (syn_chwcards (syn_cvv))))
        (syn_wbr (.cv d) (syn_clec) C))
      (syn_wex e (syn_wex r
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv e)) (.classEq C (syn_cnc (.cv e))))))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0010 p0076
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

@[expose]
noncomputable def g_wppgammaimagetceqndv (C : Class) (k : Var) (F : Class) (G : Class)
    (d : Var) (dv_C_d : d ∉ C.fv) (dv_C_k : k ∉ C.fv) (dv_F_d : d ∉ F.fv)
    (dv_F_k : k ∉ F.fv) (_dv_G_d : d ∉ G.fv) (dv_G_k : k ∉ G.fv) (dv_d_k : d ≠ k)
    (hyp_wppgammaimagetceqndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_wppgammaimagetceqndv_2 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv))))
    (hyp_wppgammaimagetceqndv_3 : Nominal.NPrf (.classMem G (syn_cvv)))
    (hyp_wppgammaimagetceqndv_4 : Nominal.NPrf (.classMem (syn_ctc C) (syn_chwcards (syn_cvv))))
    (hyp_wppgammaimagetceqndv_5 : Nominal.NPrf (.all k
          (syn_wb (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
            (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d))))))) :
    Nominal.NPrf (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_cwppgamma G (syn_ctc C))) :=
  by
  have dv_cache_0001 : k ∉ ((syn_ctc C)).fv := by
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
  have dv_cache_0005 : d ∉ ((syn_cwppgamma F C)).fv :=
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
  have dv_cache_0006 : d ∉ ((syn_cwppcand F C)).fv :=
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
    d ∉ ((Wff.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (syn_cwppgamma F C)))).fv :=
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
  have dv_cache_0008 : d ∉ ((Wff.classEq (.cv k) (syn_ctc (syn_cwppgamma F C)))).fv :=
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
  have dv_cache_0009 : k ∉ ((syn_ctc (syn_cwppgamma F C))).fv :=
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
      ((syn_wb (.classMem (syn_ctc (syn_cwppgamma F C)) (syn_cwppcand G (syn_ctc C)))
          (syn_wrex d (syn_cwppcand F C)
            (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d)))))).fv :=
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
    d ∉ ((syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (.cv k))).fv :=
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
  have dv_cache_0012 : k ∉ ((syn_cwppgamma G (syn_ctc C))).fv :=
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
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem (syn_ctc C) (syn_chwcards (syn_cvv)))
      hyp_wppgammaimagetceqndv_3 hyp_wppgammaimagetceqndv_4
  have p0001 := @g_wppgammaminhwndv (syn_ctc C) k G dv_cache_0001 dv_cache_0002
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_simpl (.classMem (syn_cwppgamma G (syn_ctc C)) (syn_cwppcand G (syn_ctc C)))
      (syn_wral k (syn_cwppcand G (syn_ctc C))
        (syn_wbr (syn_cwppgamma G (syn_ctc C)) (syn_clec) (.cv k)))
  have p0004 := Nominal.mp p0002 p0003
  have p0008 :=
    @g_simpr (.classMem (syn_cwppgamma G (syn_ctc C)) (syn_cwppcand G (syn_ctc C)))
      (syn_wral k (syn_cwppcand G (syn_ctc C))
        (syn_wbr (syn_cwppgamma G (syn_ctc C)) (syn_clec) (.cv k)))
  have p0009 := Nominal.mp p0002 p0008
  have p0010 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv)))
      hyp_wppgammaimagetceqndv_1 hyp_wppgammaimagetceqndv_2
  have p0011 := @g_wppgammaminhwndv C d F dv_cache_0003 dv_cache_0004
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
      (syn_wral d (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)))
  have p0014 := Nominal.mp p0012 p0013
  have p0015 := @g_eqid (syn_ctc (syn_cwppgamma F C))
  have p0016 :=
    @g_pm3_2i (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
      (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (syn_cwppgamma F C))) p0014 p0015
  have p0017 := @g_tceq (.cv d) (syn_cwppgamma F C)
  have p0018 :=
    @g_eqeq2d (.classEq (.cv d) (syn_cwppgamma F C)) (syn_ctc (.cv d))
      (syn_ctc (syn_cwppgamma F C)) (syn_ctc (syn_cwppgamma F C)) p0017
  have p0019 :=
    @g_rspcev (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d)))
      (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (syn_cwppgamma F C))) d
      (syn_cwppgamma F C) (syn_cwppcand F C) dv_cache_0005 dv_cache_0006 dv_cache_0007
      p0018
  have p0020 := Nominal.mp p0016 p0019
  have p0026 := @g_elwppcand C (syn_cwppgamma F C) F
  have p0027 :=
    @g_biimpi (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv)))
          (syn_wbr (syn_cwppgamma F C) (syn_clec) C))
        (.classMem (syn_cwppgamma F C) (syn_cwppreach F C)))
      p0026
  have p0028 := Nominal.mp p0014 p0027
  have p0029 :=
    @g_simpl
      (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv)))
        (syn_wbr (syn_cwppgamma F C) (syn_clec) C))
      (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))
  have p0030 := Nominal.mp p0028 p0029
  have p0031 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cwppgamma F C) (syn_clec) C)
  have p0032 := Nominal.mp p0030 p0031
  have p0033 := @g_hwcardssnc (syn_cvv)
  have p0034 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (syn_cwppgamma F C) p0033
  have p0035 := Nominal.mp p0032 p0034
  have p0036 := @g_tccl (syn_cwppgamma F C)
  have p0037 := Nominal.mp p0035 p0036
  have p0038 := @g_elex (syn_ctc (syn_cwppgamma F C)) (syn_cncs)
  have p0039 := Nominal.mp p0037 p0038
  have p0040 := @g_id (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C)))
  have p0041 :=
    @g_eleq1d (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C))) (.cv k)
      (syn_ctc (syn_cwppgamma F C)) (syn_cwppcand G (syn_ctc C)) p0040
  have p0043 :=
    @g_eqeq1d (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C))) (.cv k)
      (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d)) p0040
  have p0044 :=
    @g_rexbidv (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C)))
      (.classEq (.cv k) (syn_ctc (.cv d)))
      (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d))) d (syn_cwppcand F C)
      dv_cache_0008 p0043
  have p0045 :=
    @g_bibi12d (.classEq (.cv k) (syn_ctc (syn_cwppgamma F C)))
      (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (.classMem (syn_ctc (syn_cwppgamma F C)) (syn_cwppcand G (syn_ctc C)))
      (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wrex d (syn_cwppcand F C) (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d))))
      p0041 p0044
  have p0046 :=
    @g_spcv
      (syn_wb (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d)))))
      (syn_wb (.classMem (syn_ctc (syn_cwppgamma F C)) (syn_cwppcand G (syn_ctc C)))
        (syn_wrex d (syn_cwppcand F C)
          (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d)))))
      k (syn_ctc (syn_cwppgamma F C)) dv_cache_0009 dv_cache_0010 p0039 p0045
  have p0047 := Nominal.mp hyp_wppgammaimagetceqndv_5 p0046
  have p0048 :=
    @g_mpbir (.classMem (syn_ctc (syn_cwppgamma F C)) (syn_cwppcand G (syn_ctc C)))
      (syn_wrex d (syn_cwppcand F C) (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_ctc (.cv d))))
      p0020 p0047
  have p0049 :=
    @g_sp
      (syn_wb (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
        (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d)))))
      k
  have p0050 := Nominal.mp hyp_wppgammaimagetceqndv_5 p0049
  have p0051 :=
    @g_biimpi (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d)))) p0050
  have p0052 :=
    @g_simpl (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0056 :=
    @g_simpr (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
      (syn_wral d (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)))
  have p0057 := Nominal.mp p0012 p0056
  have p0058 :=
    @g_rsp (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)) d (syn_cwppcand F C)
  have p0059 := Nominal.mp p0057 p0058
  have p0060 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv d) (syn_cwppcand F C))
      (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d)) p0052 p0059
  have p0076 :=
    @g_a1i (.classMem (syn_cwppgamma F C) (syn_cncs))
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      p0035
  have p0078 := @g_elwppcand C (.cv d) F
  have p0079 :=
    @g_biimpi (.classMem (.cv d) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C)))
      p0078
  have p0080 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv d) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C)))
      p0052 p0079
  have p0081 :=
    @g_simpl
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (.classMem (.cv d) (syn_cwppreach F C))
  have p0082 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv)))
          (syn_wbr (.cv d) (syn_clec) C)) (.classMem (.cv d) (syn_cwppreach F C)))
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      p0080 p0081
  have p0083 :=
    @g_simpl (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C)
  have p0084 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (.classMem (.cv d) (syn_chwcards (syn_cvv))) (syn_wbr (.cv d) (syn_clec) C))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) p0082 p0083
  have p0086 := @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs) (.cv d) p0033
  have p0087 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (.cv d) (syn_chwcards (syn_cvv))) (.classMem (.cv d) (syn_cncs)) p0084
      p0086
  have p0088 :=
    @g_jca
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.classMem (syn_cwppgamma F C) (syn_cncs)) (.classMem (.cv d) (syn_cncs)) p0076
      p0087
  have p0089 := @g_tlecg (syn_cwppgamma F C) (.cv d)
  have p0090 :=
    @g_syl
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wa (.classMem (syn_cwppgamma F C) (syn_cncs)) (.classMem (.cv d) (syn_cncs)))
      (syn_wb (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d))
        (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (syn_ctc (.cv d))))
      p0088 p0089
  have p0091 :=
    @g_mpbid
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv d))
      (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (syn_ctc (.cv d))) p0060 p0090
  have p0092 :=
    @g_simpr (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d)))
  have p0093 :=
    @g_breq2d
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (.cv k) (syn_ctc (.cv d)) (syn_ctc (syn_cwppgamma F C)) (syn_clec) p0092
  have p0094 :=
    @g_mpbird
      (syn_wa (.classMem (.cv d) (syn_cwppcand F C)) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (.cv k))
      (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (syn_ctc (.cv d))) p0091 p0093
  have p0095 :=
    @g_rexlimiva (.classEq (.cv k) (syn_ctc (.cv d)))
      (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (.cv k)) d (syn_cwppcand F C)
      dv_cache_0011 p0094
  have p0096 :=
    @g_syl (.classMem (.cv k) (syn_cwppcand G (syn_ctc C)))
      (syn_wrex d (syn_cwppcand F C) (.classEq (.cv k) (syn_ctc (.cv d))))
      (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (.cv k)) p0051 p0095
  have p0097 :=
    @g_rgen (syn_wbr (syn_ctc (syn_cwppgamma F C)) (syn_clec) (.cv k)) k
      (syn_cwppcand G (syn_ctc C)) p0096
  have p0098 :=
    @g_wppcandleastuniqclndv (syn_cwppgamma G (syn_ctc C)) (syn_ctc (syn_cwppgamma F C))
      (syn_ctc C) k G dv_cache_0012 dv_cache_0009 dv_cache_0001 dv_cache_0002 p0004 p0009
      p0048 p0097
  have p0099 :=
    @g_eqcomi (syn_cwppgamma G (syn_ctc C)) (syn_ctc (syn_cwppgamma F C)) p0098
  exact p0099

@[expose]
noncomputable def g_wppgammareachndv (C : Class) (F : Class)
    (hyp_wppgammareachndv_1 : Nominal.NPrf (.classMem F (syn_cvv)))
    (hyp_wppgammareachndv_2 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf (.classMem (syn_cwppgamma F C) (syn_cwppreach F C)) :=
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
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem C (syn_chwcards (syn_cvv)))
      hyp_wppgammareachndv_1 hyp_wppgammareachndv_2
  have p0001 := @g_wppgammaminhwndv C k F dv_cache_0001 dv_cache_0002
  have p0002 := Nominal.mp p0000 p0001
  have p0003 :=
    @g_simpl (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
      (syn_wral k (syn_cwppcand F C) (syn_wbr (syn_cwppgamma F C) (syn_clec) (.cv k)))
  have p0004 := Nominal.mp p0002 p0003
  have p0005 := @g_elwppcand C (syn_cwppgamma F C) F
  have p0006 :=
    @g_biimpi (.classMem (syn_cwppgamma F C) (syn_cwppcand F C))
      (syn_wa (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv)))
          (syn_wbr (syn_cwppgamma F C) (syn_clec) C))
        (.classMem (syn_cwppgamma F C) (syn_cwppreach F C)))
      p0005
  have p0007 := Nominal.mp p0004 p0006
  have p0008 :=
    @g_simpr
      (syn_wa (.classMem (syn_cwppgamma F C) (syn_chwcards (syn_cvv)))
        (syn_wbr (syn_cwppgamma F C) (syn_clec) C))
      (.classMem (syn_cwppgamma F C) (syn_cwppreach F C))
  have p0009 := Nominal.mp p0007 p0008
  exact p0009

@[expose]
noncomputable def g_wpphitexvndv (C : Class) (F : Class) (I : Class)
    (hyp_wpphitexvndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cwpphit F I C) (syn_cvv)) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphit F I C))
  have p0001 :=
    @g_a1i
      (.classEq (syn_cwpphit F I C)
        (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))))
      (.classMem F (syn_cvv)) p0000
  have p0002 := @g_eqid (syn_cfrec F I)
  have p0003 := @g_frecexg (syn_cfrec F I) F I (syn_cvv) p0002
  have p0004 := @g_cnvexg (syn_cfrec F I) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem F (syn_cvv)) (.classMem (syn_cfrec F I) (syn_cvv))
      (.classMem (syn_ccnv (syn_cfrec F I)) (syn_cvv)) p0003 p0004
  have p0006 := @g_lecex
  have p0007 := @g_snex C
  have p0008 :=
    @g_pm3_2i (.classMem (syn_clec) (syn_cvv)) (.classMem (syn_csn C) (syn_cvv)) p0006
      p0007
  have p0009 := @g_imaexg (syn_clec) (syn_csn C) (syn_cvv) (syn_cvv)
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_a1i (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)) (.classMem F (syn_cvv))
      p0010
  have p0012 :=
    @g_jca (.classMem F (syn_cvv)) (.classMem (syn_ccnv (syn_cfrec F I)) (syn_cvv))
      (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)) p0005 p0011
  have p0013 :=
    @g_imaexg (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)
      (syn_cvv)
  have p0014 :=
    @g_syl (.classMem F (syn_cvv))
      (syn_wa (.classMem (syn_ccnv (syn_cfrec F I)) (syn_cvv))
        (.classMem (syn_cima (syn_clec) (syn_csn C)) (syn_cvv)))
      (.classMem (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C)))
        (syn_cvv))
      p0012 p0013
  have p0015 :=
    @g_eqeltrd (.classMem F (syn_cvv)) (syn_cwpphit F I C)
      (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))) (syn_cvv)
      p0001 p0014
  have p0016 := Nominal.mp hyp_wpphitexvndv_1 p0015
  exact p0016

@[expose]
noncomputable def g_elwpphitvndv (C : Class) (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (syn_wb (.classMem N (syn_cwpphit F I C))
          (syn_wa (.classMem N (syn_cnnc))
            (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N))))) :=
  by
  have p0000 := (Nominal.classEqRefl (syn_cwpphit F I C))
  have p0001 :=
    @g_eleq2i (syn_cwpphit F I C)
      (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))) N p0000
  have p0002 :=
    @g_a1i
      (syn_wb (.classMem N (syn_cwpphit F I C)) (.classMem N
          (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C)))))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      p0001
  have p0003 := @g_wpporbitfnndv F I
  have p0004 := @g_elpreima (syn_cnnc) N (syn_cima (syn_clec) (syn_csn C)) (syn_cfrec F I)
  have p0005 :=
    @g_syl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wfn (syn_cfrec F I) (syn_cnnc))
      (syn_wb (.classMem N
          (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))))
        (syn_wa (.classMem N (syn_cnnc))
          (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cima (syn_clec) (syn_csn C)))))
      p0003 p0004
  have p0006 := @g_elimasn (syn_clec) C (syn_cfv (syn_cfrec F I) N)
  have p0007 := (Nominal.biimpRefl (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N)))
  have p0008 :=
    @g_bicomi (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N))
      (.classMem (syn_cop C (syn_cfv (syn_cfrec F I) N)) (syn_clec)) p0007
  have p0009 :=
    @g_bitri (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cima (syn_clec) (syn_csn C)))
      (.classMem (syn_cop C (syn_cfv (syn_cfrec F I) N)) (syn_clec))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0006 p0008
  have p0010 :=
    @g_anbi2i (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cima (syn_clec) (syn_csn C)))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N)) (.classMem N (syn_cnnc)) p0009
  have p0011 :=
    @g_a1i
      (syn_wb (syn_wa (.classMem N (syn_cnnc))
          (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cima (syn_clec) (syn_csn C))))
        (syn_wa (.classMem N (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N))))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      p0010
  have p0012 :=
    @g_bitrd
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))))
      (syn_wa (.classMem N (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cima (syn_clec) (syn_csn C))))
      (syn_wa (.classMem N (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N)))
      p0005 p0011
  have p0013 :=
    @g_bitrd
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cwpphit F I C))
      (.classMem N (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C))))
      (syn_wa (.classMem N (syn_cnnc)) (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) N)))
      p0002 p0012
  exact p0013

@[expose]
noncomputable def g_wpphitminexvndv (x : Var) (C : Class) (S : Class) (m : Var) (n : Var)
    (F : Class) (I : Class) (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_x : x ∉ C.fv)
    (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_x : x ∉ F.fv) (dv_I_m : m ∉ I.fv)
    (dv_I_n : n ∉ I.fv) (dv_I_x : x ∉ I.fv) (dv_S_m : m ∉ S.fv) (dv_S_n : n ∉ S.fv)
    (_dv_S_x : x ∉ S.fv) (dv_m_n : m ≠ n) (dv_m_x : m ≠ x) (dv_n_x : n ≠ x)
    (hyp_wpphitminexvndv_1 : Nominal.NPrf (.classMem F (syn_cvv))) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wbr S (syn_cwe) (syn_cnnc))
          (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C))))
        (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m) (syn_cwpphit F I C))
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F I C))
                (syn_wbr (.cv m) S (.cv n))))))) :=
  by
  have dv_cache_0001 : x ∉ ((syn_cwpphit F I C)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwpphit,
          Finset.mem_union, dv_C_x, dv_F_x, dv_I_x, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0003 : m ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0004 : n ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0007 : x ∉ ((Wff.classMem (.cv m) (syn_cwpphit F I C))).fv :=
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
      ((syn_wa (syn_wbr S (syn_cwe) (syn_cnnc))
          (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C))))).fv :=
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
      ((syn_wa (syn_wbr S (syn_cwe) (syn_cnnc))
          (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C))))).fv :=
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
  have dv_cache_0010 : m ∉ ((Wff.classMem (.cv x) (syn_cwpphit F I C))).fv :=
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
  have dv_cache_0011 : n ∉ ((Wff.classMem (.cv x) (syn_cwpphit F I C))).fv :=
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
  have dv_cache_0012 : x ∉ ((Wff.classMem (.cv n) (syn_cwpphit F I C))).fv :=
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
  have p0000 := @g_abid2 x (syn_cwpphit F I C) dv_cache_0001
  have p0001 := @g_wpphitexvndv C F I hyp_wpphitminexvndv_1
  have p0002 :=
    @g_eqeltri (.cab x (.classMem (.cv x) (syn_cwpphit F I C))) (syn_cwpphit F I C)
      (syn_cvv) p0000 p0001
  have p0003 := @g_eleq1 (.cv x) (.cv m) (syn_cwpphit F I C)
  have p0004 := @g_eleq1 (.cv x) (.cv n) (syn_cwpphit F I C)
  have p0005 :=
    @g_simpl (syn_wbr S (syn_cwe) (syn_cnnc))
      (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C)))
  have p0006 :=
    @g_simpr (syn_wbr S (syn_cwe) (syn_cnnc))
      (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C)))
  have p0007_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq x m) (syn_wb (.classMem (.cv x) (syn_cwpphit F I C))
          (.classMem (.cv m) (syn_cwpphit F I C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint
          syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0007_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x n) (syn_wb (.classMem (.cv x) (syn_cwpphit F I C))
          (.classMem (.cv n) (syn_cwpphit F I C)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cwpphit syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_ccnv syn_copab syn_cfrec syn_cclos1 syn_cint
          syn_csn syn_cpprod syn_ctxp syn_cin syn_ccom syn_cmpt syn_cvv syn_cplc syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0007 :=
    @g_weds
      (syn_wa (syn_wbr S (syn_cwe) (syn_cnnc))
        (syn_wrex x (syn_cnnc) (.classMem (.cv x) (syn_cwpphit F I C))))
      (.classMem (.cv x) (syn_cwpphit F I C)) (.classMem (.cv m) (syn_cwpphit F I C))
      (.classMem (.cv n) (syn_cwpphit F I C)) x m n (syn_cnnc) S dv_cache_0002
      dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
      dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      dv_cache_0015 p0002 p0007_e01_recanon p0007_e02_recanon p0005 p0006
  exact p0007

@[expose]
noncomputable def g_elwpphitsucvndv (C : Class) (F : Class) (I : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
        (syn_wb (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I C))
          (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))) :=
  by
  have p0000 :=
    @g_simpl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0001 := @g_elwpphitvndv C F I (syn_cplc N (syn_c1c))
  have p0002 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wb (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I C))
        (syn_wa (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc))
          (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c))))))
      p0000 p0001
  have p0003 := @g_wpporbitsucndv F I N
  have p0004 :=
    @g_breq2d
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c)))
      (syn_cfv F (syn_cfv (syn_cfrec F I) N)) C (syn_clec) p0003
  have p0005 :=
    @g_anbi2d
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c))))
      (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))
      (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc)) p0004
  have p0006 :=
    @g_bitrd
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I C))
      (syn_wa (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc))
        (syn_wbr C (syn_clec) (syn_cfv (syn_cfrec F I) (syn_cplc N (syn_c1c)))))
      (syn_wa (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc))
        (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))
      p0002 p0005
  have p0007 :=
    @g_simpr
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0008 := @g_peano2 N
  have p0009 :=
    @g_syl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (.classMem N (syn_cnnc)) (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc)) p0007 p0008
  have p0010 :=
    @g_biantrurd
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc))
      (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) p0009
  have p0011 :=
    @g_bicomd
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N)))
      (syn_wa (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc))
        (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))
      p0010
  have p0012 :=
    @g_bitrd
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (.classMem (syn_cplc N (syn_c1c)) (syn_cwpphit F I C))
      (syn_wa (.classMem (syn_cplc N (syn_c1c)) (syn_cnnc))
        (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))))
      (syn_wbr C (syn_clec) (syn_cfv F (syn_cfv (syn_cfrec F I) N))) p0006 p0011
  exact p0012

@[expose]
noncomputable def g_wpphitnestptndv (F : Class) (H : Class) (I : Class) (L : Class)
    (N : Class) (_dv_F_N : Disjoint F.fv N.fv) (_dv_I_N : Disjoint I.fv N.fv) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
              (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
            (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
              (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
        (.imp (.classMem N (syn_cwpphit F I H)) (.classMem N (syn_cwpphit F I L)))) :=
  by
  have p0000 :=
    @g_simpl
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
          (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))
  have p0001 :=
    @g_simpr
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0002 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (.classMem N (syn_cnnc)) p0000 p0001
  have p0003 :=
    @g_a1d
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (.classMem N (syn_cnnc)) (.classMem N (syn_cwpphit F I H)) p0002
  have p0004 :=
    @g_simpr
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
          (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))
  have p0005 :=
    @g_simpr
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
        (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs)))
      (syn_wbr L (syn_clec) H)
  have p0006 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
          (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))
      (syn_wbr L (syn_clec) H) p0004 p0005
  have p0007 :=
    @g_a1d
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (syn_wbr L (syn_clec) H) (.classMem N (syn_cwpphit F I H)) p0006
  have p0009 :=
    @g_simpl
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem N (syn_cnnc))
  have p0010 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
          (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      p0000 p0009
  have p0011 := @g_elwpphitvndv H F I N
  have p0012 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wb (.classMem N (syn_cwpphit F I H)) (syn_wa (.classMem N (syn_cnnc))
          (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N))))
      p0010 p0011
  have p0013 :=
    @g_biimpd
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (.classMem N (syn_cwpphit F I H))
      (syn_wa (.classMem N (syn_cnnc)) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N)))
      p0012
  have p0014 :=
    @g_simpr (.classMem N (syn_cnnc)) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N))
  have p0015 :=
    @g_syl6
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (.classMem N (syn_cwpphit F I H))
      (syn_wa (.classMem N (syn_cnnc)) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N)))
      (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0013 p0014
  have p0016 :=
    @g_jcad
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (.classMem N (syn_cwpphit F I H)) (syn_wbr L (syn_clec) H)
      (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0007 p0015
  have p0018 :=
    @g_simpl
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
        (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs)))
      (syn_wbr L (syn_clec) H)
  have p0019 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (syn_wa (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
          (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H))
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
        (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs)))
      p0004 p0018
  have p0020 := @g_lectr L H (syn_cfv (syn_cfrec F I) N)
  have p0021 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
        (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs)))
      (.imp (syn_wa (syn_wbr L (syn_clec) H) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N)))
        (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)))
      p0019 p0020
  have p0022 :=
    @g_syld
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (.classMem N (syn_cwpphit F I H))
      (syn_wa (syn_wbr L (syn_clec) H) (syn_wbr H (syn_clec) (syn_cfv (syn_cfrec F I) N)))
      (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0016 p0021
  have p0023 :=
    @g_jcad
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (.classMem N (syn_cwpphit F I H)) (.classMem N (syn_cnnc))
      (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)) p0003 p0022
  have p0027 := @g_elwpphitvndv L F I N
  have p0028 :=
    @g_syl
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (syn_wb (.classMem N (syn_cwpphit F I L)) (syn_wa (.classMem N (syn_cnnc))
          (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N))))
      p0010 p0027
  have p0029 :=
    @g_biimprd
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (.classMem N (syn_cwpphit F I L))
      (syn_wa (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)))
      p0028
  have p0030 :=
    @g_syld
      (syn_wa (syn_wa (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
            (syn_wss (syn_crn F) (syn_cdm F))) (.classMem N (syn_cnnc))) (syn_wa
          (syn_w3a (.classMem L (syn_cncs)) (.classMem H (syn_cncs))
            (.classMem (syn_cfv (syn_cfrec F I) N) (syn_cncs))) (syn_wbr L (syn_clec) H)))
      (.classMem N (syn_cwpphit F I H))
      (syn_wa (.classMem N (syn_cnnc)) (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F I) N)))
      (.classMem N (syn_cwpphit F I L)) p0023 p0029
  exact p0030


end NFChoice.DirectNominalPrf.WPPReplay

end
