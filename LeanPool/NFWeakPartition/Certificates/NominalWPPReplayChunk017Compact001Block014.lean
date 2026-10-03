/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block013

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk017Compact001Part062`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_hwcardslecconnexndv (K : Class) (L : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
          (.classMem L (syn_chwcards (syn_cvv))))
        (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K))) :=
  by
  let proofSupport : Finset Var := K.fv ∪ L.fv
  let r : Var := freshVar proofSupport 0
  let d : Var := freshVar proofSupport 1
  let s : Var := freshVar proofSupport 2
  let e : Var := freshVar proofSupport 3
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_r_not_K : r ∉ K.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_L : r ∉ L.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_d_not_K : d ∉ K.fv := by
    intro h
    exact fresh_d (Finset.mem_union_left _ (h))
  have fresh_d_not_L : d ∉ L.fv := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_s_not_K : s ∉ K.fv := by
    intro h
    exact fresh_s (Finset.mem_union_left _ (h))
  have fresh_s_not_L : s ∉ L.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_e : e ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_e_not_K : e ∉ K.fv := by
    intro h
    exact fresh_e (Finset.mem_union_left _ (h))
  have fresh_e_not_L : e ∉ L.fv := by
    intro h
    exact fresh_e (Finset.mem_union_right _ (h))
  have fresh_r_ne_d : r ≠ d :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_d_ne_r : d ≠ r := Ne.symm fresh_r_ne_d
  have fresh_r_ne_s : r ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_s_ne_r : s ≠ r := Ne.symm fresh_r_ne_s
  have fresh_r_ne_e : r ≠ e :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_e_ne_r : e ≠ r := Ne.symm fresh_r_ne_e
  have fresh_d_ne_s : d ≠ s :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_s_ne_d : s ≠ d := Ne.symm fresh_d_ne_s
  have fresh_d_ne_e : d ≠ e :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
  have fresh_s_ne_e : s ≠ e :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_e_ne_s : e ≠ s := Ne.symm fresh_s_ne_e
  have dv_cache_0001 : d ∉ (K).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_d_not_K, not_false_eq_true])
  have dv_cache_0002 : r ∉ (K).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_K, not_false_eq_true])
  have dv_cache_0003 : d ≠ r :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show d ≠ r from (by exact fresh_d_ne_r))
  have dv_cache_0004 : e ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_e_not_L, not_false_eq_true])
  have dv_cache_0005 : s ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_L, not_false_eq_true])
  have dv_cache_0006 : e ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show e ≠ s from (by exact fresh_e_ne_s))
  have dv_cache_0007 :
    e ∉ ((syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_e_not_K, fresh_e_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    s ∉ ((syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_s_not_K, fresh_s_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    e ∉
      ((syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d))
            (.classEq K (syn_cnc (.cv d)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_e_not_K, fresh_e_not_L, fresh_e_ne_r, fresh_e_ne_d,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    s ∉
      ((syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv)))) (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d))
            (.classEq K (syn_cnc (.cv d)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_s_not_K, fresh_s_not_L, fresh_s_ne_r, fresh_s_ne_d,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 :
    d ∉ ((syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_d_not_K, fresh_d_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    r ∉ ((syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec, Finset.mem_union,
          fresh_r_not_K, fresh_r_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    d ∉
      ((syn_wa (.classMem K (syn_chwcards (syn_cvv)))
          (.classMem L (syn_chwcards (syn_cvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_d_not_K, fresh_d_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    r ∉
      ((syn_wa (.classMem K (syn_chwcards (syn_cvv)))
          (.classMem L (syn_chwcards (syn_cvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          fresh_r_not_K, fresh_r_not_L, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    @g_simpl (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))
  have p0002 := @g_elex K (syn_chwcards (syn_cvv))
  have p0003 :=
    @g_syl
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (.classMem K (syn_chwcards (syn_cvv))) (.classMem K (syn_cvv)) p0000 p0002
  have p0004 := @g_elhwcardsweclndv K r d dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    @g_syl
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (.classMem K (syn_cvv))
      (syn_wb (.classMem K (syn_chwcards (syn_cvv))) (syn_wex d (syn_wex r
            (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))))
      p0003 p0004
  have p0006 :=
    @g_mpbid
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (.classMem K (syn_chwcards (syn_cvv)))
      (syn_wex d (syn_wex r
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))))
      p0000 p0005
  have p0007 :=
    @g_simpl
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
  have p0008 :=
    @g_simpr (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv)))
  have p0010 := @g_elex L (syn_chwcards (syn_cvv))
  have p0011 :=
    @g_syl
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (.classMem L (syn_chwcards (syn_cvv))) (.classMem L (syn_cvv)) p0008 p0010
  have p0012 := @g_elhwcardsweclndv L s e dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0013 :=
    @g_syl
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (.classMem L (syn_cvv))
      (syn_wb (.classMem L (syn_chwcards (syn_cvv))) (syn_wex e (syn_wex s
            (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))))
      p0011 p0012
  have p0014 :=
    @g_mpbid
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (.classMem L (syn_chwcards (syn_cvv)))
      (syn_wex e (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))))
      p0008 p0013
  have p0015 :=
    @g_syl
      (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
          (.classMem L (syn_chwcards (syn_cvv))))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (syn_wex e (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))))
      p0007 p0014
  have p0016 :=
    @g_simpl
      (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
          (.classMem L (syn_chwcards (syn_cvv))))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
  have p0017 :=
    @g_simpr
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
  have p0018 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
          (.classMem L (syn_chwcards (syn_cvv))))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))) p0016
      p0017
  have p0019 :=
    @g_simpl (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0020 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_wbr (.cv r) (syn_cwe) (.cv d)) p0018 p0019
  have p0021 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
          (.classMem L (syn_chwcards (syn_cvv))))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
  have p0022 :=
    @g_simpl (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))
  have p0023 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
      (syn_wbr (.cv s) (syn_cwe) (.cv e)) p0021 p0022
  have p0024 :=
    @g_jca
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wbr (.cv s) (syn_cwe) (.cv e)) p0020 p0023
  have p0025 := @g_wecomparisonnclecandndv e s r d
  have p0026 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (syn_wbr (.cv s) (syn_cwe) (.cv e)))
      (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e)))
        (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d))))
      p0024 p0025
  have p0030 :=
    @g_simpr (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))
  have p0031 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (.classEq K (syn_cnc (.cv d))) p0018 p0030
  have p0032 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      K (syn_cnc (.cv d)) p0031
  have p0034 :=
    @g_simpr (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))
  have p0035 :=
    @g_syl
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
      (.classEq L (syn_cnc (.cv e))) p0021 p0034
  have p0036 :=
    @g_eqcomd
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      L (syn_cnc (.cv e)) p0035
  have p0037 :=
    @g_breq12d
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_cnc (.cv d)) K (syn_cnc (.cv e)) L (syn_clec) p0032 p0036
  have p0048 :=
    @g_breq12d
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_cnc (.cv e)) L (syn_cnc (.cv d)) K (syn_clec) p0036 p0032
  have p0049 :=
    @g_orbi12d
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e))) (syn_wbr K (syn_clec) L)
      (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d))) (syn_wbr L (syn_clec) K)
      p0037 p0048
  have p0050 :=
    @g_mpbid
      (syn_wa (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
            (.classMem L (syn_chwcards (syn_cvv))))
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
        (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e)))))
      (syn_wo (syn_wbr (syn_cnc (.cv d)) (syn_clec) (syn_cnc (.cv e)))
        (syn_wbr (syn_cnc (.cv e)) (syn_clec) (syn_cnc (.cv d))))
      (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) p0026 p0049
  have p0051 :=
    @g_ex
      (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
          (.classMem L (syn_chwcards (syn_cvv))))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
      (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) p0050
  have p0052 :=
    @g_exlimdvv
      (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
          (.classMem L (syn_chwcards (syn_cvv))))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
      (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))
      (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) e s dv_cache_0007
      dv_cache_0008 dv_cache_0009 dv_cache_0010 p0051
  have p0053 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem K (syn_chwcards (syn_cvv)))
          (.classMem L (syn_chwcards (syn_cvv))))
        (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d)))))
      (syn_wex e (syn_wex s
          (syn_wa (syn_wbr (.cv s) (syn_cwe) (.cv e)) (.classEq L (syn_cnc (.cv e))))))
      (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) p0015 p0052
  have p0054 :=
    @g_ex
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) p0053
  have p0055 :=
    @g_exlimdvv
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))
      (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) d r dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 p0054
  have p0056 :=
    @g_mpd
      (syn_wa (.classMem K (syn_chwcards (syn_cvv))) (.classMem L (syn_chwcards (syn_cvv))))
      (syn_wex d (syn_wex r
          (syn_wa (syn_wbr (.cv r) (syn_cwe) (.cv d)) (.classEq K (syn_cnc (.cv d))))))
      (syn_wo (syn_wbr K (syn_clec) L) (syn_wbr L (syn_clec) K)) p0006 p0055
  exact p0056

@[expose]
noncomputable def g_wpporbithwcldmndv (F : Class) (I : Class) (q : Var)
    (_dv_F_q : q ∉ F.fv) (_dv_I_q : q ∉ I.fv)
    (hyp_wpporbithwcldmndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wpporbithwcldmndv_2 : Nominal.NPrf (.classMem I (syn_cdm F)))
    (hyp_wpporbithwcldmndv_3 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wpporbithwcldmndv_4 : Nominal.NPrf (.classEq (syn_cdm F) (syn_chwcards (syn_cvv)))) :
    Nominal.NPrf
      (syn_wral q (syn_cnnc)
        (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_chwcards (syn_cvv)))) :=
  by
  have p0000 :=
    @g_n_3pm3_2i (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
      (syn_wss (syn_crn F) (syn_cdm F)) hyp_wpporbithwcldmndv_1 hyp_wpporbithwcldmndv_2
      hyp_wpporbithwcldmndv_3
  have p0001 := @g_id (.classMem (.cv q) (syn_cnnc))
  have p0002 := @g_frecdomfv F I (.cv q)
  have p0003 :=
    @g_sylancr (.classMem (.cv q) (syn_cnnc))
      (syn_w3a (.classMem F (syn_cfuns)) (.classMem I (syn_cdm F))
        (syn_wss (syn_crn F) (syn_cdm F)))
      (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cdm F)) p0000 p0001 p0002
  have p0004 :=
    @g_eleq2i (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cfv (syn_cfrec F I) (.cv q))
      hyp_wpporbithwcldmndv_4
  have p0005 :=
    @g_sylib (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_cdm F))
      (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_chwcards (syn_cvv))) p0003 p0004
  have p0006 := Nominal.gen p0005 q
  have p0007 :=
    (Nominal.biimpRefl (syn_wral q (syn_cnnc)
        (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_chwcards (syn_cvv)))))
  have p0008 :=
    @g_mpbir
      (syn_wral q (syn_cnnc)
        (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_chwcards (syn_cvv))))
      (.all q (.imp (.classMem (.cv q) (syn_cnnc))
          (.classMem (syn_cfv (syn_cfrec F I) (.cv q)) (syn_chwcards (syn_cvv)))))
      p0006 p0007
  exact p0008


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part063`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppgammaprefixeqhwselfmapndv (y : Var) (F : Class) (G : Class)
    (L : Class) (dv_F_y : y ∉ F.fv) (dv_G_y : y ∉ G.fv) (dv_L_y : y ∉ L.fv)
    (hyp_wppgammaprefixeqhwselfmapndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppgammaprefixeqhwselfmapndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppgammaprefixeqhwselfmapndv_3 :
      Nominal.NPrf (.classEq (syn_cdm F) (syn_chwcards (syn_cvv))))
    (hyp_wppgammaprefixeqhwselfmapndv_4 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_wppgammaprefixeqhwselfmapndv_5 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G)))
    (hyp_wppgammaprefixeqhwselfmapndv_6 :
      Nominal.NPrf (.classEq (syn_cdm G) (syn_chwcards (syn_cvv))))
    (hyp_wppgammaprefixeqhwselfmapndv_7 : Nominal.NPrf (.classMem L (syn_chwcards (syn_cvv))))
    (hyp_wppgammaprefixeqhwselfmapndv_8 : Nominal.NPrf (syn_wral y (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv y) (syn_clec) L)
            (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))))) :
    Nominal.NPrf (.classEq (syn_cwppgamma F L) (syn_cwppgamma G L)) :=
  by
  let proofSupport : Finset Var := ({ y } : Finset Var) ∪ F.fv ∪ G.fv ∪ L.fv
  let q : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_q_ne_y : q ≠ y := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_q : y ≠ q := Ne.symm fresh_q_ne_y
  have fresh_q_not_F : q ∉ F.fv := by
    intro h
    exact
      fresh_q
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_q_not_G : q ∉ G.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_q_not_L : q ∉ L.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_k_not_F : k ∉ F.fv := by
    intro h
    exact
      fresh_k
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_k_not_G : k ∉ G.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_k_not_L : k ∉ L.fv := by
    intro h
    exact fresh_k (Finset.mem_union_right _ (h))
  have dv_cache_0001 : k ∉ (L).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_L, not_false_eq_true])
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
  have dv_cache_0003 : q ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_F, not_false_eq_true])
  have dv_cache_0004 : q ∉ ((syn_cwppgamma F L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, fresh_q_not_L, fresh_q_not_F, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, or_false,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_chwcards (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
          (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
            (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, dv_G_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : q ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_G, not_false_eq_true])
  have dv_cache_0009 : y ∉ ((syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, dv_F_y, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    y ∉
      ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
          (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
            (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, dv_F_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : k ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_G, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((syn_cwppgamma G L)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          Finset.mem_union, fresh_q_not_L, fresh_q_not_G, or_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, dv_G_y, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    y ∉
      ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
          (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
            (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_F_y, dv_L_y, dv_G_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 : y ∉ ((syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, or_false,
          not_false_eq_true])
  have dv_cache_0016 :
    y ∉
      ((Wff.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
          (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
            (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cfrec,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppgamma,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clec,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_q, dv_G_y, dv_L_y, dv_F_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : q ∉ (L).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_q_not_L, not_false_eq_true])
  have p0000 := @g_elex F (syn_cfuns)
  have p0001 := Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_1 p0000
  have p0002 :=
    @g_pm3_2i (.classMem F (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0001
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0003 := @g_wppgammaminhwndv L k F dv_cache_0001 dv_cache_0002
  have p0004 := Nominal.mp p0002 p0003
  have p0005 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_cwppcand F L))
      (syn_wral k (syn_cwppcand F L) (syn_wbr (syn_cwppgamma F L) (syn_clec) (.cv k)))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 := @g_elwppcand L (syn_cwppgamma F L) F
  have p0008 :=
    @g_mpbi (.classMem (syn_cwppgamma F L) (syn_cwppcand F L))
      (syn_wa (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv)))
          (syn_wbr (syn_cwppgamma F L) (syn_clec) L))
        (.classMem (syn_cwppgamma F L) (syn_cwppreach F L)))
      p0006 p0007
  have p0009 :=
    @g_simpl
      (syn_wa (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv)))
        (syn_wbr (syn_cwppgamma F L) (syn_clec) L))
      (.classMem (syn_cwppgamma F L) (syn_cwppreach F L))
  have p0010 := Nominal.mp p0008 p0009
  have p0011 :=
    @g_simpl (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cwppgamma F L) (syn_clec) L)
  have p0012 := Nominal.mp p0010 p0011
  have p0013 :=
    @g_eleq2i (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppgamma F L)
      hyp_wppgammaprefixeqhwselfmapndv_3
  have p0014 :=
    @g_mpbir (.classMem (syn_cwppgamma F L) (syn_cdm F))
      (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) p0012 p0013
  have p0028 :=
    @g_eleq2i (syn_cdm G) (syn_chwcards (syn_cvv)) (syn_cwppgamma F L)
      hyp_wppgammaprefixeqhwselfmapndv_6
  have p0029 :=
    @g_mpbir (.classMem (syn_cwppgamma F L) (syn_cdm G))
      (.classMem (syn_cwppgamma F L) (syn_chwcards (syn_cvv))) p0012 p0028
  have p0045 :=
    @g_wpporbithwcldmndv F (syn_cwppgamma F L) q dv_cache_0003 dv_cache_0004
      hyp_wppgammaprefixeqhwselfmapndv_1 p0014 hyp_wppgammaprefixeqhwselfmapndv_2
      hyp_wppgammaprefixeqhwselfmapndv_3
  have p0046 :=
    @g_a1i (.classMem L (syn_chwcards (syn_cvv)))
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0047 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0048 :=
    @g_jca
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (.classMem L (syn_chwcards (syn_cvv)))
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      p0046 p0047
  have p0049 :=
    @g_hwcardslecconnexndv L (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))
  have p0050 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wa (.classMem L (syn_chwcards (syn_cvv)))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      p0048 p0049
  have p0051 :=
    @g_notnot (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
  have p0052 :=
    @g_biimpi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))))
      p0051
  have p0053 :=
    @g_pm2_21
      (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))
      (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
  have p0054 :=
    @g_syl (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      p0052 p0053
  have p0055 :=
    @g_id (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
  have p0056 :=
    @g_a1d (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
      (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
      (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))
      p0055
  have p0057 :=
    @g_jaoi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) p0054
      p0056
  have p0058 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      p0050 p0057
  have p0059 :=
    @g_ralimiaa
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      q (syn_cnnc) p0058
  have p0060 := Nominal.mp p0045 p0059
  have p0078 :=
    @g_a1i
      (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L)
          (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))))
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      hyp_wppgammaprefixeqhwselfmapndv_8
  have p0079 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
  have p0080 :=
    @g_breq1d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) L (syn_clec) p0079
  have p0082 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) F p0079
  have p0084 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) G p0079
  have p0085 :=
    @g_eqeq12d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      (syn_cfv F (.cv y)) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      (syn_cfv G (.cv y)) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      p0082 p0084
  have p0086 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      (syn_wbr (.cv y) (syn_clec) L)
      (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
      (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))
      (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
        (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))
      p0080 p0085
  have p0087 :=
    @g_rspcv
      (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))
      (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))))
      y (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))
      dv_cache_0005 dv_cache_0006 dv_cache_0007 p0086
  have p0088 :=
    @g_mpd
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L)
          (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))))
      (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))))
      p0078 p0087
  have p0089 :=
    @g_impcom
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
      (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
        (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))
      p0088
  have p0090 :=
    @g_eqcomd
      (syn_wa (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
      (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))) p0089
  have p0091 :=
    @g_expcom (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
        (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))))
      p0090
  have p0092 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
          (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))))
      p0047 p0091
  have p0093 :=
    @g_ralimiaa
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))
          (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma F L)) (.cv q)))))
      q (syn_cnnc) p0092
  have p0094 := Nominal.mp p0045 p0093
  have p0110 :=
    @g_wpporbithwcldmndv G (syn_cwppgamma F L) q dv_cache_0008 dv_cache_0004
      hyp_wppgammaprefixeqhwselfmapndv_4 p0029 hyp_wppgammaprefixeqhwselfmapndv_5
      hyp_wppgammaprefixeqhwselfmapndv_6
  have p0111 :=
    @g_a1i (.classMem L (syn_chwcards (syn_cvv)))
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0112 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0113 :=
    @g_jca
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (.classMem L (syn_chwcards (syn_cvv)))
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      p0111 p0112
  have p0114 :=
    @g_hwcardslecconnexndv L (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))
  have p0115 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wa (.classMem L (syn_chwcards (syn_cvv)))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      p0113 p0114
  have p0116 :=
    @g_notnot (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
  have p0117 :=
    @g_biimpi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
      (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))))
      p0116
  have p0118 :=
    @g_pm2_21
      (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))
      (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
  have p0119 :=
    @g_syl (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
      (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      p0117 p0118
  have p0120 :=
    @g_id (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
  have p0121 :=
    @g_a1d (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
      (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
      (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))
      p0120
  have p0122 :=
    @g_jaoi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L) p0119
      p0121
  have p0123 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      p0115 p0122
  have p0124 :=
    @g_ralimiaa
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L))
      q (syn_cnnc) p0123
  have p0125 := Nominal.mp p0110 p0124
  have p0143 :=
    @g_a1i
      (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L)
          (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))))
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      hyp_wppgammaprefixeqhwselfmapndv_8
  have p0144 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
  have p0145 :=
    @g_breq1d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) L (syn_clec) p0144
  have p0147 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) F p0144
  have p0149 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) G p0144
  have p0150 :=
    @g_eqeq12d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
      (syn_cfv F (.cv y)) (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
      (syn_cfv G (.cv y)) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
      p0147 p0149
  have p0151 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
      (syn_wbr (.cv y) (syn_clec) L)
      (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
      (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))
      (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
        (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))))
      p0145 p0150
  have p0152 :=
    @g_rspcv
      (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))
      (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))))
      y (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv))
      dv_cache_0009 dv_cache_0006 dv_cache_0010 p0151
  have p0153 :=
    @g_mpd
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L)
          (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))))
      (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))))
      p0143 p0152
  have p0154 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))))
      p0112 p0153
  have p0155 :=
    @g_ralimiaa
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma F L)) (.cv q)))))
      q (syn_cnnc) p0154
  have p0156 := Nominal.mp p0110 p0155
  have p0157 := @g_elex G (syn_cfuns)
  have p0158 := Nominal.mp hyp_wppgammaprefixeqhwselfmapndv_4 p0157
  have p0159 :=
    @g_pm3_2i (.classMem G (syn_cvv)) (.classMem L (syn_chwcards (syn_cvv))) p0158
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0160 := @g_wppgammaminhwndv L k G dv_cache_0001 dv_cache_0011
  have p0161 := Nominal.mp p0159 p0160
  have p0162 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_cwppcand G L))
      (syn_wral k (syn_cwppcand G L) (syn_wbr (syn_cwppgamma G L) (syn_clec) (.cv k)))
  have p0163 := Nominal.mp p0161 p0162
  have p0164 := @g_elwppcand L (syn_cwppgamma G L) G
  have p0165 :=
    @g_mpbi (.classMem (syn_cwppgamma G L) (syn_cwppcand G L))
      (syn_wa (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv)))
          (syn_wbr (syn_cwppgamma G L) (syn_clec) L))
        (.classMem (syn_cwppgamma G L) (syn_cwppreach G L)))
      p0163 p0164
  have p0166 :=
    @g_simpl
      (syn_wa (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv)))
        (syn_wbr (syn_cwppgamma G L) (syn_clec) L))
      (.classMem (syn_cwppgamma G L) (syn_cwppreach G L))
  have p0167 := Nominal.mp p0165 p0166
  have p0168 :=
    @g_simpl (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cwppgamma G L) (syn_clec) L)
  have p0169 := Nominal.mp p0167 p0168
  have p0170 :=
    @g_eleq2i (syn_cdm F) (syn_chwcards (syn_cvv)) (syn_cwppgamma G L)
      hyp_wppgammaprefixeqhwselfmapndv_3
  have p0171 :=
    @g_mpbir (.classMem (syn_cwppgamma G L) (syn_cdm F))
      (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) p0169 p0170
  have p0185 :=
    @g_eleq2i (syn_cdm G) (syn_chwcards (syn_cvv)) (syn_cwppgamma G L)
      hyp_wppgammaprefixeqhwselfmapndv_6
  have p0186 :=
    @g_mpbir (.classMem (syn_cwppgamma G L) (syn_cdm G))
      (.classMem (syn_cwppgamma G L) (syn_chwcards (syn_cvv))) p0169 p0185
  have p0202 :=
    @g_wpporbithwcldmndv F (syn_cwppgamma G L) q dv_cache_0003 dv_cache_0012
      hyp_wppgammaprefixeqhwselfmapndv_1 p0171 hyp_wppgammaprefixeqhwselfmapndv_2
      hyp_wppgammaprefixeqhwselfmapndv_3
  have p0203 :=
    @g_a1i (.classMem L (syn_chwcards (syn_cvv)))
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0204 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0205 :=
    @g_jca
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (.classMem L (syn_chwcards (syn_cvv)))
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      p0203 p0204
  have p0206 :=
    @g_hwcardslecconnexndv L (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))
  have p0207 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wa (.classMem L (syn_chwcards (syn_cvv)))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      p0205 p0206
  have p0208 :=
    @g_notnot (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
  have p0209 :=
    @g_biimpi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))))
      p0208
  have p0210 :=
    @g_pm2_21
      (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))
      (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
  have p0211 :=
    @g_syl (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      p0209 p0210
  have p0212 :=
    @g_id (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
  have p0213 :=
    @g_a1d (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
      (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
      (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))
      p0212
  have p0214 :=
    @g_jaoi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) p0211
      p0213
  have p0215 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      p0207 p0214
  have p0216 :=
    @g_ralimiaa
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      q (syn_cnnc) p0215
  have p0217 := Nominal.mp p0202 p0216
  have p0235 :=
    @g_a1i
      (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L)
          (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))))
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      hyp_wppgammaprefixeqhwselfmapndv_8
  have p0236 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
  have p0237 :=
    @g_breq1d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) L (syn_clec) p0236
  have p0239 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) F p0236
  have p0241 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) G p0236
  have p0242 :=
    @g_eqeq12d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      (syn_cfv F (.cv y)) (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      (syn_cfv G (.cv y)) (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      p0239 p0241
  have p0243 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      (syn_wbr (.cv y) (syn_clec) L)
      (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
      (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))
      (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
        (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))
      p0237 p0242
  have p0244 :=
    @g_rspcv
      (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))
      (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))))
      y (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))
      dv_cache_0013 dv_cache_0006 dv_cache_0014 p0243
  have p0245 :=
    @g_mpd
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L)
          (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))))
      (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))))
      p0235 p0244
  have p0246 :=
    @g_impcom
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
      (.classEq (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
        (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))
      p0245
  have p0247 :=
    @g_eqcomd
      (syn_wa (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
      (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))) p0246
  have p0248 :=
    @g_expcom (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
        (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))))
      p0247
  have p0249 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
          (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))))
      p0204 p0248
  have p0250 :=
    @g_ralimiaa
      (.classMem (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv G (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))
          (syn_cfv F (syn_cfv (syn_cfrec F (syn_cwppgamma G L)) (.cv q)))))
      q (syn_cnnc) p0249
  have p0251 := Nominal.mp p0202 p0250
  have p0267 :=
    @g_wpporbithwcldmndv G (syn_cwppgamma G L) q dv_cache_0008 dv_cache_0012
      hyp_wppgammaprefixeqhwselfmapndv_4 p0186 hyp_wppgammaprefixeqhwselfmapndv_5
      hyp_wppgammaprefixeqhwselfmapndv_6
  have p0268 :=
    @g_a1i (.classMem L (syn_chwcards (syn_cvv)))
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      hyp_wppgammaprefixeqhwselfmapndv_7
  have p0269 :=
    @g_simpr (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
  have p0270 :=
    @g_jca
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (.classMem L (syn_chwcards (syn_cvv)))
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      p0268 p0269
  have p0271 :=
    @g_hwcardslecconnexndv L (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))
  have p0272 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wa (.classMem L (syn_chwcards (syn_cvv)))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      p0270 p0271
  have p0273 :=
    @g_notnot (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
  have p0274 :=
    @g_biimpi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
      (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))))
      p0273
  have p0275 :=
    @g_pm2_21
      (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))
      (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
  have p0276 :=
    @g_syl (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
      (.neg (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      p0274 p0275
  have p0277 :=
    @g_id (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
  have p0278 :=
    @g_a1d (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
      (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
      (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))
      p0277
  have p0279 :=
    @g_jaoi (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L) p0276
      p0278
  have p0280 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (syn_wo (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      p0272 p0279
  have p0281 :=
    @g_ralimiaa
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (.neg (syn_wbr L (syn_clec) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))
        (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L))
      q (syn_cnnc) p0280
  have p0282 := Nominal.mp p0267 p0281
  have p0300 :=
    @g_a1i
      (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L)
          (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))))
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      hyp_wppgammaprefixeqhwselfmapndv_8
  have p0301 :=
    @g_id (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
  have p0302 :=
    @g_breq1d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) L (syn_clec) p0301
  have p0304 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) F p0301
  have p0306 :=
    @g_fveq2d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
      (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) G p0301
  have p0307 :=
    @g_eqeq12d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
      (syn_cfv F (.cv y)) (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
      (syn_cfv G (.cv y)) (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
      p0304 p0306
  have p0308 :=
    @g_imbi12d (.classEq (.cv y) (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
      (syn_wbr (.cv y) (syn_clec) L)
      (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
      (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))
      (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
        (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))))
      p0302 p0307
  have p0309 :=
    @g_rspcv
      (.imp (syn_wbr (.cv y) (syn_clec) L) (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y))))
      (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))))
      y (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv))
      dv_cache_0015 dv_cache_0006 dv_cache_0016 p0308
  have p0310 :=
    @g_mpd
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) L)
          (.classEq (syn_cfv F (.cv y)) (syn_cfv G (.cv y)))))
      (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))))
      p0300 p0309
  have p0311 :=
    @g_syl
      (syn_wa (.classMem (.cv q) (syn_cnnc))
        (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q))
          (syn_chwcards (syn_cvv))))
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))))
      p0269 p0310
  have p0312 :=
    @g_ralimiaa
      (.classMem (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_chwcards (syn_cvv)))
      (.imp (syn_wbr (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)) (syn_clec) L)
        (.classEq (syn_cfv F (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))
          (syn_cfv G (syn_cfv (syn_cfrec G (syn_cwppgamma G L)) (.cv q)))))
      q (syn_cnnc) p0311
  have p0313 := Nominal.mp p0267 p0312
  have p0314 :=
    @g_wppgammaprefixeqpointndv F G L q dv_cache_0003 dv_cache_0008 dv_cache_0017
      hyp_wppgammaprefixeqhwselfmapndv_1 hyp_wppgammaprefixeqhwselfmapndv_2
      hyp_wppgammaprefixeqhwselfmapndv_4 hyp_wppgammaprefixeqhwselfmapndv_5
      hyp_wppgammaprefixeqhwselfmapndv_7 p0014 p0029 p0060 p0094 p0125 p0156 p0171 p0186
      p0217 p0251 p0282 p0313
  exact p0314


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk017Compact001Part064`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_wppstopgammaprefixeqndv (C : Class) (F : Class) (p : Var)
    (dv_C_p : p ∉ C.fv) (dv_F_p : p ∉ F.fv)
    (hyp_wppstopgammaprefixeqndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopgammaprefixeqndv_2 :
      Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))))
    (hyp_wppstopgammaprefixeqndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv))))
    (hyp_wppstopgammaprefixeqndv_4 : Nominal.NPrf (syn_wbr (syn_ctc C) (syn_clec) C))
    (hyp_wppstopgammaprefixeqndv_5 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F))))) :
    Nominal.NPrf
      (.classEq (syn_cwppgamma (syn_cwppstopstep F (syn_ctc C)) (syn_ctc C))
        (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))) :=
  by
  let proofSupport : Finset Var := C.fv ∪ F.fv ∪ ({ p } : Finset Var)
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_F : y ∉ F.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_ne_p : y ≠ p := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
  have dv_cache_0001 : p ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
  have dv_cache_0002 : p ∉ (F).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0003 : p ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show p ≠ y from (by exact fresh_p_ne_y))
  have dv_cache_0004 : y ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_y_not_C, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_y_not_C, fresh_y_not_F, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, fresh_y_not_C,
          not_false_eq_true])
  have p0000 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0001 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0002 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
  have p0003 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopgammaprefixeqndv_1
      hyp_wppstopgammaprefixeqndv_2
  have p0004 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopgammaprefixeqndv_1
      hyp_wppstopgammaprefixeqndv_2
  have p0005 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopgammaprefixeqndv_1
      hyp_wppstopgammaprefixeqndv_2
  have p0006 := @g_hwcardstcclndv C
  have p0007 := Nominal.mp hyp_wppstopgammaprefixeqndv_3 p0006
  have p0008 :=
    @g_wppstopstepsamebelowdndv y C F p dv_cache_0001 dv_cache_0002 dv_cache_0003
      hyp_wppstopgammaprefixeqndv_1 hyp_wppstopgammaprefixeqndv_2
      hyp_wppstopgammaprefixeqndv_3 hyp_wppstopgammaprefixeqndv_4
      hyp_wppstopgammaprefixeqndv_5
  have p0009 := Nominal.gen p0008 y
  have p0010 :=
    (Nominal.biimpRefl (syn_wral y (syn_chwcards (syn_cvv))
        (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
          (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y))
            (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y))))))
  have p0011 :=
    @g_mpbir
      (syn_wral y (syn_chwcards (syn_cvv)) (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
          (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y))
            (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y)))))
      (.all y (.imp (.classMem (.cv y) (syn_chwcards (syn_cvv)))
          (.imp (syn_wbr (.cv y) (syn_clec) (syn_ctc C))
            (.classEq (syn_cfv (syn_cwppstopstep F C) (.cv y))
              (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (.cv y))))))
      p0009 p0010
  have p0012 :=
    @g_wppgammaprefixeqhwselfmapndv y (syn_cwppstopstep F C)
      (syn_cwppstopstep F (syn_ctc C)) (syn_ctc C) dv_cache_0004 dv_cache_0005
      dv_cache_0006 p0000 p0001 p0002 p0003 p0004 p0005 p0007 p0011
  have p0013 :=
    @g_eqcomi (syn_cwppgamma (syn_cwppstopstep F C) (syn_ctc C))
      (syn_cwppgamma (syn_cwppstopstep F (syn_ctc C)) (syn_ctc C)) p0012
  exact p0013

@[expose]
noncomputable def g_wpphitstartcongrndv (C : Class) (F : Class) (I : Class) (J : Class) :
    Nominal.NPrf
      (.imp (.classEq I J) (.classEq (syn_cwpphit F I C) (syn_cwpphit F J C))) :=
  by
  have p0000 := @g_id (.classEq I J)
  have p0001 := @g_eqid F
  have p0002 := @g_jctil (.classEq I J) (.classEq I J) (.classEq F F) p0000 p0001
  have p0003 := @g_freceq12 F F I J
  have p0004 :=
    @g_syl (.classEq I J) (syn_wa (.classEq F F) (.classEq I J))
      (.classEq (syn_cfrec F I) (syn_cfrec F J)) p0002 p0003
  have p0005 := @g_cnveqd (.classEq I J) (syn_cfrec F I) (syn_cfrec F J) p0004
  have p0006 :=
    @g_imaeq1d (.classEq I J) (syn_ccnv (syn_cfrec F I)) (syn_ccnv (syn_cfrec F J))
      (syn_cima (syn_clec) (syn_csn C)) p0005
  have p0007 := (Nominal.classEqRefl (syn_cwpphit F I C))
  have p0008 := (Nominal.classEqRefl (syn_cwpphit F J C))
  have p0009 :=
    @g_n_3eqtr4g (.classEq I J)
      (syn_cima (syn_ccnv (syn_cfrec F I)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cima (syn_ccnv (syn_cfrec F J)) (syn_cima (syn_clec) (syn_csn C)))
      (syn_cwpphit F I C) (syn_cwpphit F J C) p0006 p0007 p0008
  exact p0009

@[expose]
noncomputable def g_wppcrossgammaleasthitpairhwndv (C : Class) (k : Var) (m : Var)
    (n : Var) (F : Class) (G : Class) (q : Var) (p : Var) (dv_C_k : k ∉ C.fv)
    (dv_C_m : m ∉ C.fv) (dv_C_n : n ∉ C.fv) (dv_C_p : p ∉ C.fv) (dv_C_q : q ∉ C.fv)
    (_dv_F_k : k ∉ F.fv) (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_p : p ∉ F.fv)
    (_dv_F_q : q ∉ F.fv) (dv_G_k : k ∉ G.fv) (_dv_G_m : m ∉ G.fv) (_dv_G_n : n ∉ G.fv)
    (dv_G_p : p ∉ G.fv) (dv_G_q : q ∉ G.fv) (_dv_k_m : k ≠ m) (_dv_k_n : k ≠ n)
    (_dv_k_p : k ≠ p) (dv_k_q : k ≠ q) (dv_m_n : m ≠ n) (_dv_m_p : m ≠ p)
    (_dv_m_q : m ≠ q) (_dv_n_p : n ≠ p) (_dv_n_q : n ≠ q) (_dv_p_q : p ≠ q)
    (hyp_wppcrossgammaleasthitpairhwndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppcrossgammaleasthitpairhwndv_2 : Nominal.NPrf (syn_wss (syn_crn F) (syn_cdm F)))
    (hyp_wppcrossgammaleasthitpairhwndv_3 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm F)))))
    (hyp_wppcrossgammaleasthitpairhwndv_4 : Nominal.NPrf (.classMem G (syn_cfuns)))
    (hyp_wppcrossgammaleasthitpairhwndv_5 : Nominal.NPrf (syn_wss (syn_crn G) (syn_cdm G)))
    (hyp_wppcrossgammaleasthitpairhwndv_6 : Nominal.NPrf (syn_wral p (syn_chwcards (syn_cvv))
          (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc C)) (.classMem (.cv p) (syn_cdm G)))))
    (hyp_wppcrossgammaleasthitpairhwndv_7 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv))))
    (hyp_wppcrossgammaleasthitpairhwndv_8 : Nominal.NPrf
        (.classEq (syn_ctc (syn_cwppgamma F C)) (syn_cwppgamma G (syn_ctc C)))) :
    Nominal.NPrf
      (syn_wa (syn_wrex m (syn_cnnc)
          (syn_wa (.classMem (.cv m) (syn_cwpphit F (syn_cwppgamma F C) C))
            (syn_wral n (syn_cnnc)
              (.imp (.classMem (.cv n) (syn_cwpphit F (syn_cwppgamma F C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wrex k (syn_cnnc)
          (syn_wa (.classMem (.cv k) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
            (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q)
                  (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))))) :=
  by
  have dv_cache_0001 : m ∉ (C).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_m, not_false_eq_true])
  have dv_cache_0002 : n ∉ (C).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0003 : p ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_p, not_false_eq_true])
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
  have dv_cache_0005 : n ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_n, not_false_eq_true])
  have dv_cache_0006 : p ∉ (F).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_F_p, not_false_eq_true])
  have dv_cache_0007 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show m ≠ n from (by exact dv_m_n))
  have dv_cache_0008 : k ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, dv_C_k,
          not_false_eq_true])
  have dv_cache_0009 : q ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, dv_C_q,
          not_false_eq_true])
  have dv_cache_0010 : p ∉ ((syn_ctc C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, dv_C_p,
          not_false_eq_true])
  have dv_cache_0011 : k ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_k, not_false_eq_true])
  have dv_cache_0012 : q ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_q, not_false_eq_true])
  have dv_cache_0013 : p ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_p, not_false_eq_true])
  have dv_cache_0014 : k ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show k ≠ q from (by exact dv_k_q))
  have p0000 :=
    @g_wppgammaleasthithwndv C m n F p dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
      hyp_wppcrossgammaleasthitpairhwndv_1 hyp_wppcrossgammaleasthitpairhwndv_2
      hyp_wppcrossgammaleasthitpairhwndv_3 hyp_wppcrossgammaleasthitpairhwndv_7
  have p0001 := @g_hwcardstcclndv C
  have p0002 := Nominal.mp hyp_wppcrossgammaleasthitpairhwndv_7 p0001
  have p0003 :=
    @g_wppgammaleasthithwndv (syn_ctc C) k q G p dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014
      hyp_wppcrossgammaleasthitpairhwndv_4 hyp_wppcrossgammaleasthitpairhwndv_5
      hyp_wppcrossgammaleasthitpairhwndv_6 p0002
  have p0004 :=
    @g_eqcomi (syn_ctc (syn_cwppgamma F C)) (syn_cwppgamma G (syn_ctc C))
      hyp_wppcrossgammaleasthitpairhwndv_8
  have p0005 :=
    @g_wpphitstartcongrndv (syn_ctc C) G (syn_cwppgamma G (syn_ctc C))
      (syn_ctc (syn_cwppgamma F C))
  have p0006 := Nominal.mp p0004 p0005
  have p0007 :=
    @g_eleq2i (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C))
      (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)) (.cv k) p0006
  have p0011 :=
    @g_eleq2i (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C))
      (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)) (.cv q) p0006
  have p0012 :=
    @g_imbi1i
      (.classMem (.cv q) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C)))
      (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
      (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)) p0011
  have p0013 :=
    @g_ralbii
      (.imp (.classMem (.cv q) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C)))
        (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))
      (.imp (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
        (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))
      q (syn_cnnc) p0012
  have p0014 :=
    @g_anbi12i
      (.classMem (.cv k) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C)))
      (.classMem (.cv k) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
      (syn_wral q (syn_cnnc) (.imp
          (.classMem (.cv q) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))
      (syn_wral q (syn_cnnc) (.imp
          (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
          (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))
      p0007 p0013
  have p0015 :=
    @g_rexbii
      (syn_wa (.classMem (.cv k) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C)))
        (syn_wral q (syn_cnnc) (.imp
            (.classMem (.cv q) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))
      (syn_wa (.classMem (.cv k) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
        (syn_wral q (syn_cnnc) (.imp
            (.classMem (.cv q) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
            (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q)))))
      k (syn_cnnc) p0014
  have p0016 :=
    @g_mpbi
      (syn_wrex k (syn_cnnc) (syn_wa
          (.classMem (.cv k) (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C)))
          (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q)
                (syn_cwpphit G (syn_cwppgamma G (syn_ctc C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))))
      (syn_wrex k (syn_cnnc) (syn_wa
          (.classMem (.cv k) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
          (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q)
                (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))))
      p0003 p0015
  have p0017 :=
    @g_pm3_2i
      (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m) (syn_cwpphit F (syn_cwppgamma F C) C))
          (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit F (syn_cwppgamma F C) C))
              (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n))))))
      (syn_wrex k (syn_cnnc) (syn_wa
          (.classMem (.cv k) (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
          (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q)
                (syn_cwpphit G (syn_ctc (syn_cwppgamma F C)) (syn_ctc C)))
              (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))))
      p0000 p0016
  exact p0017

@[expose]
noncomputable def g_wppstopgammaleasthitpairndv (x : Var) (C : Class) (k : Var) (m : Var)
    (n : Var) (F : Class) (q : Var) (dv_C_k : k ∉ C.fv) (dv_C_m : m ∉ C.fv)
    (dv_C_n : n ∉ C.fv) (dv_C_q : q ∉ C.fv) (dv_C_x : x ∉ C.fv) (dv_F_k : k ∉ F.fv)
    (dv_F_m : m ∉ F.fv) (dv_F_n : n ∉ F.fv) (dv_F_q : q ∉ F.fv) (dv_F_x : x ∉ F.fv)
    (dv_k_m : k ≠ m) (dv_k_n : k ≠ n) (dv_k_q : k ≠ q) (_dv_k_x : k ≠ x) (dv_m_n : m ≠ n)
    (dv_m_q : m ≠ q) (_dv_m_x : m ≠ x) (dv_n_q : n ≠ q) (_dv_n_x : n ≠ x)
    (_dv_q_x : q ≠ x)
    (hyp_wppstopgammaleasthitpairndv_1 : Nominal.NPrf (.classMem F (syn_cfuns)))
    (hyp_wppstopgammaleasthitpairndv_2 :
      Nominal.NPrf (syn_wss (syn_crn F) (syn_chwcards (syn_cvv))))
    (hyp_wppstopgammaleasthitpairndv_3 : Nominal.NPrf (.classMem C (syn_chwcards (syn_cvv))))
    (hyp_wppstopgammaleasthitpairndv_4 : Nominal.NPrf
        (syn_wral x (syn_cdm (syn_cwppstopstep F C))
          (.classEq (syn_ctc (syn_cfv (syn_cwppstopstep F C) (.cv x)))
            (syn_cfv (syn_cwppstopstep F (syn_ctc C)) (syn_ctc (.cv x)))))) :
    Nominal.NPrf
      (syn_wa (syn_wrex m (syn_cnnc) (syn_wa (.classMem (.cv m)
              (syn_cwpphit (syn_cwppstopstep F C) (syn_cwppgamma (syn_cwppstopstep F C) C) C))
            (syn_wral n (syn_cnnc) (.imp (.classMem (.cv n) (syn_cwpphit (syn_cwppstopstep F C)
                    (syn_cwppgamma (syn_cwppstopstep F C) C) C))
                (syn_wbr (.cv m) (syn_ckqrel (syn_clefin)) (.cv n)))))) (syn_wrex k (syn_cnnc)
          (syn_wa (.classMem (.cv k) (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
            (syn_wral q (syn_cnnc) (.imp (.classMem (.cv q)
                  (syn_cwpphit (syn_cwppstopstep F (syn_ctc C))
                    (syn_ctc (syn_cwppgamma (syn_cwppstopstep F C) C)) (syn_ctc C)))
                (syn_wbr (.cv k) (syn_ckqrel (syn_clefin)) (.cv q))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ C.fv ∪ ({ k } : Finset Var) ∪ ({ m } : Finset Var) ∪
          ({ n } : Finset Var) ∪
        F.fv ∪
      ({ q } : Finset Var)
  let p : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_p_not_C : p ∉ C.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_p_ne_k : p ≠ k := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))))
  have fresh_k_ne_p : k ≠ p := Ne.symm fresh_p_ne_k
  have fresh_p_ne_m : p ≠ m := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_m_ne_p : m ≠ p := Ne.symm fresh_p_ne_m
  have fresh_p_ne_n : p ≠ n := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_p : n ≠ p := Ne.symm fresh_p_ne_n
  have fresh_p_not_F : p ∉ F.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_q : p ≠ q := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_ne_x : r ≠ x := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _
                  (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))))
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact
      fresh_r
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _
                (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))))
  have fresh_r_not_F : r ∉ F.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_p_ne_r : p ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : r ∉ ((syn_chwcards (syn_cvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcards,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : p ≠ r := by
    clear dv_cache_0001
    exact (show p ≠ r from (by exact fresh_p_ne_r))
  have dv_cache_0003 : p ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_C, not_false_eq_true])
  have dv_cache_0004 : r ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_r_not_C, not_false_eq_true])
  have dv_cache_0005 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_x, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_p_not_C, fresh_p_not_F, or_false, not_false_eq_true])
  have dv_cache_0007 : r ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, fresh_r_not_C, fresh_r_not_F, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_x, dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_p_not_C, fresh_p_not_F, or_false, not_false_eq_true])
  have dv_cache_0010 : r ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union,
          fresh_r_not_C, fresh_r_not_F, or_false, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_x,
          dv_F_x, or_false, not_false_eq_true])
  have dv_cache_0012 : p ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show p ≠ x from (by exact fresh_p_ne_x))
  have dv_cache_0013 : r ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show r ≠ x from (by exact fresh_r_ne_x))
  have dv_cache_0014 : k ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_k, not_false_eq_true])
  have dv_cache_0015 : m ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_m, not_false_eq_true])
  have dv_cache_0016 : n ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_n, not_false_eq_true])
  have dv_cache_0017 : q ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_C_q, not_false_eq_true])
  have dv_cache_0018 : k ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_k, dv_F_k, or_false, not_false_eq_true])
  have dv_cache_0019 : m ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_m, dv_F_m, or_false, not_false_eq_true])
  have dv_cache_0020 : n ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_n, dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0021 : q ∉ ((syn_cwppstopstep F C)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          Finset.mem_union, dv_C_q, dv_F_q, or_false, not_false_eq_true])
  have dv_cache_0022 : k ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_k,
          dv_F_k, or_false, not_false_eq_true])
  have dv_cache_0023 : m ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_m,
          dv_F_m, or_false, not_false_eq_true])
  have dv_cache_0024 : n ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_n,
          dv_F_n, or_false, not_false_eq_true])
  have dv_cache_0025 : q ∉ ((syn_cwppstopstep F (syn_ctc C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cwppstopstep,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc, Finset.mem_union, dv_C_q,
          dv_F_q, or_false, not_false_eq_true])
  have dv_cache_0026 : k ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show k ≠ m from (by exact dv_k_m))
  have dv_cache_0027 : k ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show k ≠ n from (by exact dv_k_n))
  have dv_cache_0028 : k ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show k ≠ p from (by exact fresh_k_ne_p))
  have dv_cache_0029 : k ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show k ≠ q from (by exact dv_k_q))
  have dv_cache_0030 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show m ≠ n from (by exact dv_m_n))
  have dv_cache_0031 : m ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact (show m ≠ p from (by exact fresh_m_ne_p))
  have dv_cache_0032 : m ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact (show m ≠ q from (by exact dv_m_q))
  have dv_cache_0033 : n ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show n ≠ p from (by exact fresh_n_ne_p))
  have dv_cache_0034 : n ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show n ≠ q from (by exact dv_n_q))
  have dv_cache_0035 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have p0000 :=
    @g_wppstopstepfunsndv C F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0001 :=
    @g_wppstopsteprndmndv C F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0002 :=
    @g_wppstopstepdmndv C F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0003 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv)) (.cv p) p0002
  have p0004 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0003
  have p0005 := Nominal.gen p0004 p
  have p0006 :=
    (Nominal.biimpRefl (syn_wral p (syn_chwcards (syn_cvv))
        (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))))
  have p0007 :=
    @g_mpbir
      (syn_wral p (syn_chwcards (syn_cvv)) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))
      (.all p (.imp (.classMem (.cv p) (syn_chwcards (syn_cvv)))
          (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))))
      p0005 p0006
  have p0008 :=
    Nominal.ax1 (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (syn_wbr (.cv p) (syn_clec) C)
  have p0009 :=
    @g_a1i
      (.imp (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
        (.imp (syn_wbr (.cv p) (syn_clec) C)
          (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))))
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0008
  have p0010 :=
    @g_ralimia (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (.imp (syn_wbr (.cv p) (syn_clec) C) (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))))
      p (syn_chwcards (syn_cvv)) p0009
  have p0011 := Nominal.mp p0007 p0010
  have p0012 :=
    @g_wppstopstepfunsndv (syn_ctc C) F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0013 :=
    @g_wppstopsteprndmndv (syn_ctc C) F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0014 :=
    @g_wppstopstepdmndv (syn_ctc C) F hyp_wppstopgammaleasthitpairndv_1
      hyp_wppstopgammaleasthitpairndv_2
  have p0015 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv)) (.cv p)
      p0014
  have p0016 :=
    @g_biimpri (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0015
  have p0017 := Nominal.gen p0016 p
  have p0018 :=
    (Nominal.biimpRefl (syn_wral p (syn_chwcards (syn_cvv))
        (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))
  have p0019 :=
    @g_mpbir
      (syn_wral p (syn_chwcards (syn_cvv))
        (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))
      (.all p (.imp (.classMem (.cv p) (syn_chwcards (syn_cvv)))
          (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))
      p0017 p0018
  have p0020 :=
    Nominal.ax1 (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))
      (syn_wbr (.cv p) (syn_clec) (syn_ctc C))
  have p0021 :=
    @g_a1i
      (.imp (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))
        (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc C))
          (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0020
  have p0022 :=
    @g_ralimia (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))
      (.imp (syn_wbr (.cv p) (syn_clec) (syn_ctc C))
        (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))
      p (syn_chwcards (syn_cvv)) p0021
  have p0023 := Nominal.mp p0019 p0022
  have p0031 := @g_hwcardstcclndv (.cv p)
  have p0033 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F (syn_ctc C))) (syn_chwcards (syn_cvv))
      (syn_ctc (.cv p)) p0014
  have p0034 :=
    @g_sylibr (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (.classMem (syn_ctc (.cv p)) (syn_chwcards (syn_cvv)))
      (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0031 p0033
  have p0035 :=
    @g_jca (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))) p0004 p0034
  have p0036 := Nominal.gen p0035 p
  have p0037 :=
    (Nominal.biimpRefl (syn_wral p (syn_chwcards (syn_cvv))
        (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
          (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))))
  have p0038 :=
    @g_mpbir
      (syn_wral p (syn_chwcards (syn_cvv))
        (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
          (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))
      (.all p (.imp (.classMem (.cv p) (syn_chwcards (syn_cvv)))
          (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
            (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))))
      p0036 p0037
  have p0039 :=
    Nominal.ax1
      (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
        (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))
      (syn_wbr (.cv p) (syn_clec) C)
  have p0040 :=
    @g_a1i
      (.imp (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
          (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))
        (.imp (syn_wbr (.cv p) (syn_clec) C)
          (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
            (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))))
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0039
  have p0041 :=
    @g_ralimia
      (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
        (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C)))))
      (.imp (syn_wbr (.cv p) (syn_clec) C)
        (syn_wa (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
          (.classMem (syn_ctc (.cv p)) (syn_cdm (syn_cwppstopstep F (syn_ctc C))))))
      p (syn_chwcards (syn_cvv)) p0040
  have p0042 := Nominal.mp p0038 p0041
  have p0044 :=
    @g_a1i (.classMem (syn_cwppstopstep F C) (syn_cfuns))
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc)))
      p0000
  have p0045 :=
    @g_simpl (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))
  have p0049 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc)))
      (.classMem (.cv p) (syn_chwcards (syn_cvv)))
      (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C))) p0045 p0004
  have p0051 :=
    @g_a1i (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C)))
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc)))
      p0001
  have p0052 :=
    @g_n_3jca
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc)))
      (.classMem (syn_cwppstopstep F C) (syn_cfuns))
      (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
      (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))) p0044
      p0049 p0051
  have p0053 :=
    @g_simpr (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc))
  have p0054 :=
    @g_jca
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc)))
      (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns))
        (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
        (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))))
      (.classMem (.cv r) (syn_cnnc)) p0052 p0053
  have p0055 := @g_frecdomfv (syn_cwppstopstep F C) (.cv p) (.cv r)
  have p0056 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc)))
      (syn_wa (syn_w3a (.classMem (syn_cwppstopstep F C) (syn_cfuns))
          (.classMem (.cv p) (syn_cdm (syn_cwppstopstep F C)))
          (syn_wss (syn_crn (syn_cwppstopstep F C)) (syn_cdm (syn_cwppstopstep F C))))
        (.classMem (.cv r) (syn_cnnc)))
      (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r))
        (syn_cdm (syn_cwppstopstep F C)))
      p0054 p0055
  have p0058 :=
    @g_eleq2i (syn_cdm (syn_cwppstopstep F C)) (syn_chwcards (syn_cvv))
      (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) p0002
  have p0059 :=
    @g_sylib
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc)))
      (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r))
        (syn_cdm (syn_cwppstopstep F C)))
      (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r))
        (syn_chwcards (syn_cvv)))
      p0056 p0058
  have p0060 := @g_hwcardssnc (syn_cvv)
  have p0061 :=
    @g_sseli (syn_chwcards (syn_cvv)) (syn_cncs)
      (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) p0060
  have p0062 :=
    @g_syl
      (syn_wa (.classMem (.cv p) (syn_chwcards (syn_cvv))) (.classMem (.cv r) (syn_cnnc)))
      (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r))
        (syn_chwcards (syn_cvv)))
      (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))
      p0059 p0061
  have p0063 :=
    @g_rgen2
      (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))
      p r (syn_chwcards (syn_cvv)) (syn_cnnc) dv_cache_0001 dv_cache_0002 p0062
  have p0064 :=
    Nominal.ax1
      (syn_wral r (syn_cnnc)
        (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)))
      (syn_wbr (.cv p) (syn_clec) C)
  have p0065 :=
    @g_a1i
      (.imp (syn_wral r (syn_cnnc)
          (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)))
        (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc)
            (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r))
              (syn_cncs)))))
      (.classMem (.cv p) (syn_chwcards (syn_cvv))) p0064
  have p0066 :=
    @g_ralimia
      (syn_wral r (syn_cnnc)
        (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs)))
      (.imp (syn_wbr (.cv p) (syn_clec) C) (syn_wral r (syn_cnnc)
          (.classMem (syn_cfv (syn_cfrec (syn_cwppstopstep F C) (.cv p)) (.cv r)) (syn_cncs))))
      p (syn_chwcards (syn_cvv)) p0065
  have p0067 := Nominal.mp p0063 p0066
  have p0068 :=
    @g_wppgammatchwboundedeqndv x C (syn_cwppstopstep F C)
      (syn_cwppstopstep F (syn_ctc C)) r p dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0002 dv_cache_0012 dv_cache_0013 p0000 p0001 p0012 p0013
      hyp_wppstopgammaleasthitpairndv_4 p0042 p0067 hyp_wppstopgammaleasthitpairndv_3
  have p0069 :=
    @g_wppcrossgammaleasthitpairhwndv C k m n (syn_cwppstopstep F C)
      (syn_cwppstopstep F (syn_ctc C)) q p dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0003 dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0006
      dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0009 dv_cache_0025
      dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
      dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 p0000 p0001 p0011 p0012
      p0013 p0023 hyp_wppstopgammaleasthitpairndv_3 p0068
  exact p0069


end NFChoice.DirectNominalPrf.WPPReplay

end
