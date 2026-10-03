/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block020

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `ReplaySupport.CodeCover1`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbhnqinjcodecoverddndv_stage1 (u : Var) (P : Class) (k : Var)
    (Y : Class) (dv_P_u : u ∉ P.fv)
    (hyp_cfbhnqinjcodecoverddndv_1 : Nominal.NPrf (.classMem P (syn_cvv)))
    (hyp_cfbhnqinjcodecoverddndv_2 : Nominal.NPrf (.classMem Y (syn_cvv))) {Result : Type}
    (continuation : _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ →
        _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → Result) :=
  show Result from
    by
    let proofSupport : Finset Var :=
      ({ u } : Finset Var) ∪ P.fv ∪ ({ k } : Finset Var) ∪ Y.fv
    let r : Var := freshVar proofSupport 0
    let y : Var := freshVar proofSupport 1
    let x : Var := freshVar proofSupport 2
    let f : Var := freshVar proofSupport 3
    let a : Var := freshVar proofSupport 4
    let h : Var := freshVar proofSupport 8
    have fresh_r : r ∉ proofSupport :=
      by
      change freshVar proofSupport 0 ∉ proofSupport
      exact freshVar_not_mem proofSupport 0
    have fresh_r_ne_u : r ≠ u := by
      intro h
      exact
        fresh_r
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_r_ne_k : r ≠ k := by
      intro h
      exact
        fresh_r
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_y : y ∉ proofSupport :=
      by
      change freshVar proofSupport 1 ∉ proofSupport
      exact freshVar_not_mem proofSupport 1
    have fresh_y_ne_u : y ≠ u := by
      intro h
      exact
        fresh_y
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_y_ne_k : y ≠ k := by
      intro h
      exact
        fresh_y
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_x : x ∉ proofSupport :=
      by
      change freshVar proofSupport 2 ∉ proofSupport
      exact freshVar_not_mem proofSupport 2
    have fresh_x_ne_u : x ≠ u := by
      intro h
      exact
        fresh_x
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_x_ne_k : x ≠ k := by
      intro h
      exact
        fresh_x
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_f : f ∉ proofSupport :=
      by
      change freshVar proofSupport 3 ∉ proofSupport
      exact freshVar_not_mem proofSupport 3
    have fresh_f_ne_u : f ≠ u := by
      intro h
      exact
        fresh_f
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_f_ne_k : f ≠ k := by
      intro h
      exact
        fresh_f
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_a : a ∉ proofSupport :=
      by
      change freshVar proofSupport 4 ∉ proofSupport
      exact freshVar_not_mem proofSupport 4
    have fresh_a_ne_u : a ≠ u := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_a_ne_k : a ≠ k := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_k_ne_a : k ≠ a := Ne.symm fresh_a_ne_k
    have fresh_a_not_Y : a ∉ Y.fv := by
      intro h
      exact fresh_a (Finset.mem_union_right _ (h))
    have fresh_r_ne_y : r ≠ y :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 1
      exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
    have fresh_y_ne_r : y ≠ r := Ne.symm fresh_r_ne_y
    have fresh_r_ne_x : r ≠ x :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 2
      exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
    have fresh_x_ne_r : x ≠ r := Ne.symm fresh_r_ne_x
    have fresh_r_ne_f : r ≠ f :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
    have fresh_f_ne_r : f ≠ r := Ne.symm fresh_r_ne_f
    have fresh_y_ne_x : y ≠ x :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 2
      exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
    have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
    have fresh_y_ne_f : y ≠ f :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
    have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
    have fresh_x_ne_f : x ≠ f :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
    have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
    have dv_cache_0001 : u ∉ (P).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [dv_P_u, not_false_eq_true])
    have dv_cache_0002 : f ≠ r := by exact (show f ≠ r from (by exact fresh_f_ne_r))
    have dv_cache_0003 : f ≠ x := by exact (show f ≠ x from (by exact fresh_f_ne_x))
    have dv_cache_0004 : f ≠ y := by exact (show f ≠ y from (by exact fresh_f_ne_y))
    have dv_cache_0005 : r ≠ x := by exact (show r ≠ x from (by exact fresh_r_ne_x))
    have dv_cache_0006 : r ≠ y := by exact (show r ≠ y from (by exact fresh_r_ne_y))
    have dv_cache_0007 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
    have dv_cache_0008 :
      f ∉ ((syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_f_ne_k, fresh_f_ne_u, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0009 :
      f ∉
        ((Wff.imp (syn_wa
              (syn_wf1o (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv x)
                (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
              (syn_cpwpull (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
              (syn_cwe) (.cv x)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, fresh_f_ne_k, fresh_f_ne_u,
            fresh_f_ne_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0010 :
      x ∉ ((syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_k, fresh_x_ne_u, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0011 :
      x ∉
        ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
                (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
              (syn_wbr (.cv r) (syn_cwe) (.cv y))) (syn_wbr
              (syn_cpwpull (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
              (syn_cwe) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_k, fresh_x_ne_u, fresh_x_ne_y, fresh_x_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0012 :
      y ∉ ((syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_k, fresh_y_ne_u, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0013 :
      y ∉
        ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
                (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
                (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_wbr (.cv r) (syn_cwe)
                (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_cpwpull (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
              (syn_cwe) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_k, fresh_y_ne_u, fresh_y_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0014 : r ∉ ((syn_cfv (syn_c1st) (.cv u))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_r_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0015 :
      r ∉
        ((Wff.imp (syn_wa (syn_wf1o (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
                (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
                (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
              (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
                (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))) (syn_wbr
              (syn_cpwpull (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
                (syn_cfv (syn_c1st) (.cv u)))
              (syn_cwe) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_r_ne_k, fresh_r_ne_u, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0016 :
      f ∉
        ((Wff.imp (syn_wfo (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv x)
              (.cv y)) (syn_wss
              (syn_cpwpull (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
              (syn_cxp (.cv x) (.cv x))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
            Finset.mem_singleton, fresh_f_ne_x, fresh_f_ne_y, fresh_f_ne_k, fresh_f_ne_u,
            fresh_f_ne_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0017 :
      x ∉
        ((Wff.imp (syn_wfo (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)) (syn_wss
              (syn_cpwpull (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
              (syn_cxp (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
                (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_k, fresh_x_ne_u, fresh_x_ne_y, fresh_x_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0018 :
      y ∉
        ((Wff.imp (syn_wfo (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
              (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
              (syn_cpwpull (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
              (syn_cxp (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
                (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_k, fresh_y_ne_u, fresh_y_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0019 :
      r ∉
        ((Wff.imp (syn_wfo (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
              (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
              (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))) (syn_wss
              (syn_cpwpull (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
                (syn_cfv (syn_c1st) (.cv u)))
              (syn_cxp (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
                (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
            Finset.mem_singleton, fresh_r_ne_k, fresh_r_ne_u, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0020 :
      Disjoint ((syn_crn (.cv k))).fv ((syn_cfv (syn_c1st) (.cv a))).fv := by
      exact
        (show Disjoint ((syn_crn (.cv k))).fv ((syn_cfv (syn_c1st) (.cv a))).fv from (by
            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
            exact
              (show Disjoint (((Class.cv k)).fv) ((((Class.cv a)).fv) ∪ (((syn_c1st)).fv))
                from
                (Finset.disjoint_union_right.mpr
                  ⟨(show Disjoint (((Class.cv k)).fv) (((Class.cv a)).fv) from
                      (by
                        rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                        exact
                          (show Disjoint (({ k } : Finset Var)) (((Class.cv a)).fv) from
                            (by
                              rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                              exact
                                (show
                                  Disjoint (({ k } : Finset Var)) (({ a } : Finset Var))
                                  from
                                  (Finset.disjoint_singleton_left.mpr
                                    (show k ∉ ({ a } : Finset Var) from
                                      (by
                                        simpa only [Finset.mem_singleton] using
                                          (show k ≠ a from
                                            (by exact fresh_k_ne_a)))))))))),
                    (show Disjoint (((Class.cv k)).fv) (((syn_c1st)).fv) from
                      (by
                        rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                        exact
                          (show Disjoint (({ k } : Finset Var)) (((syn_c1st)).fv) from
                            (by
                              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                              exact
                                (show Disjoint (({ k } : Finset Var)) ((∅ : Finset Var))
                                  from (by simp))))))⟩))))
    have dv_cache_0021 : Disjoint (Y).fv ((syn_cfv (syn_c1st) (.cv a))).fv := by
      exact
        (show Disjoint (Y).fv ((syn_cfv (syn_c1st) (.cv a))).fv from (by
            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
            exact
              (show Disjoint ((Y).fv) ((((Class.cv a)).fv) ∪ (((syn_c1st)).fv)) from
                (Finset.disjoint_union_right.mpr
                  ⟨(show Disjoint ((Y).fv) (((Class.cv a)).fv) from
                      (by
                        rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                        exact
                          (show Disjoint ((Y).fv) (({ a } : Finset Var)) from
                            (Finset.disjoint_singleton_right.mpr
                              (show a ∉ (Y).fv from (by exact fresh_a_not_Y)))))),
                    (show Disjoint ((Y).fv) (((syn_c1st)).fv) from
                      (by
                        rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                        exact
                          (show Disjoint ((Y).fv) ((∅ : Finset Var)) from
                            (by simp))))⟩))))
    have dv_cache_0022 : a ∉ ((syn_chwcn (syn_crn (.cv k)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_k,
            not_false_eq_true])
    have dv_cache_0023 : a ∉ ((syn_chwcn Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            fresh_a_not_Y, not_false_eq_true])
    have dv_cache_0024 : a ∉ ((syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_u, fresh_a_not_Y, fresh_a_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    let syntaxFormula0000 : Wff :=
      (syn_wss (syn_cfv (syn_c1st) (.cv u))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0001 : Wff :=
      (syn_wa (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0000)
    let syntaxFormula0002 : Wff :=
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0003 : Wff :=
      (syn_wa (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0004 : Wff :=
      (syn_wf1o (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0005 : Wff :=
      (.classEq (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c2nd) (.cv u)))
    let syntaxFormula0006 : Wff :=
      (.classEq (syn_cfv (syn_c2nd) (.cv u))
        (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0007 : Wff :=
      (.classEq (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0008 : Wff :=
      (.classEq (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0009 : Wff :=
      (syn_wf1o (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0010 : Wff := (syn_wb syntaxFormula0004 syntaxFormula0009)
    let syntaxFormula0011 : Wff :=
      (syn_wf1o (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0012 : Wff :=
      (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
        (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0013 : Wff :=
      (syn_wb syntaxFormula0012
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0014 : Wff :=
      (syn_wb (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        syntaxFormula0012)
    let syntaxFormula0015 : Wff :=
      (.imp (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        syntaxFormula0012)
    let syntaxFormula0016 : Wff :=
      (syn_wbr (.cv r) (syn_cwe) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxClass0017 : Class :=
      (syn_ccom (syn_ccnv (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))) (.cv r))
    let syntaxClass0018 : Class :=
      (syn_ccom (syn_ccnv (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cfv (syn_c1st) (.cv u)))
    let syntaxClass0019 : Class :=
      (syn_cpwpull (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv r))
    let syntaxClass0020 : Class :=
      (syn_ccom syntaxClass0017 (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxClass0021 : Class :=
      (syn_cpwpull (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c1st) (.cv u)))
    let syntaxClass0022 : Class :=
      (syn_ccom syntaxClass0018 (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0023 : Wff := (syn_wa syntaxFormula0011 syntaxFormula0016)
    let syntaxFormula0024 : Wff := (syn_wa syntaxFormula0011 syntaxFormula0012)
    let syntaxFormula0025 : Wff :=
      (syn_wbr syntaxClass0019 (syn_cwe)
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0026 : Wff :=
      (syn_wbr syntaxClass0021 (syn_cwe)
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0027 : Wff :=
      (syn_wf1o (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
    let syntaxFormula0028 : Wff :=
      (syn_wa syntaxFormula0027 (syn_wbr (.cv r) (syn_cwe) (.cv y)))
    let syntaxFormula0029 : Wff :=
      (syn_wf1o (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
    let syntaxFormula0030 : Wff :=
      (syn_wa syntaxFormula0029 (syn_wbr (.cv r) (syn_cwe) (.cv y)))
    let syntaxFormula0031 : Wff := (syn_wbr syntaxClass0019 (syn_cwe) (.cv x))
    let syntaxFormula0032 : Wff := (.imp syntaxFormula0030 syntaxFormula0031)
    let syntaxFormula0033 : Wff := (.imp syntaxFormula0028 syntaxFormula0025)
    let syntaxFormula0034 : Wff := (.imp syntaxFormula0023 syntaxFormula0025)
    let syntaxClass0035 : Class :=
      (syn_ccom (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)))
    let syntaxClass0036 : Class :=
      (syn_ccom syntaxClass0035 (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0037 : Wff :=
      (syn_wbr syntaxClass0036 (syn_cwe)
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0038 : Wff :=
      (syn_wss (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (.cv k)))
    let syntaxFormula0039 : Wff :=
      (syn_wb syntaxFormula0038
        (syn_wss (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k))))
    let syntaxFormula0040 : Wff :=
      (syn_wb (syn_wss (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k)))
        syntaxFormula0038)
    let syntaxFormula0041 : Wff :=
      (.imp (syn_wss (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k)))
        syntaxFormula0038)
    let syntaxClass0042 : Class :=
      (syn_cop syntaxClass0036 (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0043 : Wff :=
      (.classMem syntaxClass0042 (syn_chwcodes (syn_crn (.cv k))))
    let syntaxFormula0044 : Wff :=
      (syn_wfo (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxClass0045 : Class :=
      (syn_cxp (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0046 : Wff := (syn_wss syntaxClass0019 syntaxClass0045)
    let syntaxFormula0047 : Wff := (syn_wss syntaxClass0021 syntaxClass0045)
    let syntaxFormula0048 : Wff :=
      (syn_wfo (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
    let syntaxFormula0049 : Wff :=
      (syn_wfo (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv x) (.cv y))
    let syntaxFormula0050 : Wff := (syn_wss syntaxClass0019 (syn_cxp (.cv x) (.cv x)))
    let syntaxFormula0051 : Wff := (.imp syntaxFormula0049 syntaxFormula0050)
    let syntaxFormula0052 : Wff := (.imp syntaxFormula0048 syntaxFormula0046)
    let syntaxFormula0053 : Wff := (.imp syntaxFormula0044 syntaxFormula0046)
    let syntaxFormula0054 : Wff := (syn_wss syntaxClass0036 syntaxClass0045)
    let syntaxClass0055 : Class := (syn_cfv (syn_c2nd) syntaxClass0042)
    let syntaxClass0056 : Class := (syn_cfv (syn_c1st) syntaxClass0042)
    let syntaxClass0057 : Class := (syn_cxp syntaxClass0055 syntaxClass0055)
    let syntaxFormula0058 : Wff := (syn_wss syntaxClass0056 syntaxClass0057)
    let syntaxFormula0059 : Wff :=
      (.classMem syntaxClass0042 (syn_chwcn (syn_crn (.cv k))))
    let syntaxFormula0060 : Wff :=
      (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwcn (syn_crn (.cv k))))
    let syntaxFormula0061 : Wff :=
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv a)) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_chwcodes (syn_crn (.cv k))))
    let syntaxFormula0062 : Wff :=
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_crn (.cv k))))
    let syntaxFormula0063 : Wff :=
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) Y))
    let syntaxFormula0064 : Wff :=
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv a)) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_chwcodes Y))
    let syntaxFormula0065 : Wff :=
      (syn_wss (syn_cfv (syn_c1st) (.cv a))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c2nd) (.cv a))))
    let syntaxFormula0066 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_chwcodes Y)) syntaxFormula0065)
    let syntaxFormula0067 : Wff :=
      (.classMem (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        (syn_chnord Y))
    let syntaxFormula0068 : Wff :=
      (syn_wa (syn_wfn (syn_chnqinc Y (syn_cun P Y)) (syn_chnord Y)) syntaxFormula0067)
    let syntaxClass0069 : Class :=
      (syn_cfv (syn_chnqinc Y (syn_cun P Y))
        (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y)))
    let syntaxFormula0070 : Wff :=
      (.classMem syntaxClass0069 (syn_crn (syn_chnqinc Y (syn_cun P Y))))
    let syntaxFormula0071 : Wff :=
      (syn_wbr (syn_cec (.cv u) (syn_chwniso P)) (syn_ccnv (syn_chnqmap1 P)) (syn_csn (.cv u)))
    have p0000 := @g_ssun2 Y P
    have p0001 := @g_unex P Y hyp_cfbhnqinjcodecoverddndv_1 hyp_cfbhnqinjcodecoverddndv_2
    have p0002 := @g_hnqincfn (syn_cun P Y) Y p0000 hyp_cfbhnqinjcodecoverddndv_2 p0001
    have p0003 :=
      @g_a1i (syn_wfn (syn_chnqinc Y (syn_cun P Y)) (syn_chnord Y))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) p0002
    have p0004 := @g_f1f1orn (syn_cfv (syn_c2nd) (.cv u)) Y (.cv k)
    have p0005 := @g_id (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
    have p0006 :=
      @g_a1ii
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
          (syn_wf1o (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k))))
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
          (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y))
        p0004 p0005
    have p0007 := @g_f1of1 (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)) (.cv k)
    have p0008 :=
      @g_syl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wf1o (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k))) p0006 p0007
    have p0009 := @g_hwcnselfbasendv u P dv_cache_0001
    have p0010 := @g_id (.classMem (.cv u) (syn_chwcn P))
    have p0011 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P))
          (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.imp (.classMem (.cv u) (syn_chwcn P)) (.classMem (.cv u) (syn_chwcn P))) p0009
        p0010
    have p0012 := @g_hwcnpair u (syn_cfv (syn_c2nd) (.cv u))
    have p0013 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv u) (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))))
        p0011 p0012
    have p0014 := @g_vex u
    have p0015 := @g_elhwcncl (syn_cfv (syn_c2nd) (.cv u)) (.cv u)
    have p0016 := Nominal.mp p0014 p0015
    have p0017 :=
      @g_biimpi (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        syntaxFormula0001 p0016
    have p0018 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0001
        p0011 p0017
    have p0019 :=
      @g_simpl (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
        syntaxFormula0000
    have p0020 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0001
        (.classMem (.cv u) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u)))) p0018 p0019
    have p0021 :=
      @g_eqeltrrd (.classMem (.cv u) (syn_chwcn P)) (.cv u)
        (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))) p0013 p0020
    have p0022 := @g_fvex (.cv u) (syn_c1st)
    have p0023 := @g_fvex (.cv u) (syn_c2nd)
    have p0024 :=
      @g_elhwcodesclndv (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))
        (syn_cfv (syn_c2nd) (.cv u)) p0022 p0023
    have p0025 :=
      @g_sylib (.classMem (.cv u) (syn_chwcn P))
        (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
        syntaxFormula0002 p0021 p0024
    have p0026 :=
      @g_simpr
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
    have p0027 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0002
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u))) p0025 p0026
    have p0028 :=
      @g_a1d (.classMem (.cv u) (syn_chwcn P))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) p0027
    have p0029 :=
      @g_pm3_2 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
    have p0030 :=
      @g_syl9 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k))) syntaxFormula0003
        p0028 p0029
    have p0031 :=
      @g_syl5 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)))
        (.classMem (.cv u) (syn_chwcn P))
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0003) p0008
        p0030
    have p0032 :=
      @g_pm2_43d (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0003 p0031
    have p0033 :=
      @g_f1ores (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k))
        (syn_cfv (syn_c2nd) (.cv u)) (.cv k)
    have p0034 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0003
        syntaxFormula0004 p0032 p0033
    have p0035 :=
      @g_f1odm (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
    have p0036 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0004
        syntaxFormula0005 p0034 p0035
    have p0037 :=
      @g_eqcom (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c2nd) (.cv u))
    have p0038 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0005
        syntaxFormula0006 p0036 p0037
    have p0039 :=
      @g_f1ofo (syn_cfv (syn_c2nd) (.cv u))
        (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
    have p0040 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0004
        (syn_wfo (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        p0034 p0039
    have p0041 :=
      @g_forn (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
    have p0042 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wfo (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_cfv (syn_c2nd) (.cv u)) (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        syntaxFormula0007 p0040 p0041
    have p0043 :=
      @g_eqcom (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
    have p0044 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0007
        syntaxFormula0008 p0042 p0043
    have p0045 :=
      @g_jcad (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0006
        syntaxFormula0008 p0038 p0044
    have p0046 :=
      @g_f1oeq23 (syn_cfv (syn_c2nd) (.cv u))
        (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
    have p0047 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wa syntaxFormula0006 syntaxFormula0008) syntaxFormula0010 p0045 p0046
    have p0048 := @g_bi1 syntaxFormula0004 syntaxFormula0009
    have p0049 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0010
        (.imp syntaxFormula0004 syntaxFormula0009) p0047 p0048
    have p0050 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0004
        syntaxFormula0009 p0034 p0049
    have p0051 :=
      @g_f1ocnv (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
    have p0052 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0009
        syntaxFormula0011 p0050 p0051
    have p0053 :=
      @g_simpl
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv u)))
    have p0054 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0002
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        p0025 p0053
    have p0055 :=
      @g_a1d (.classMem (.cv u) (syn_chwcn P))
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) p0054
    have p0056 :=
      @g_breq2 (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c1st) (.cv u)) (syn_cwe)
    have p0057 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0005
        syntaxFormula0013 p0036 p0056
    have p0058 :=
      @g_bicom syntaxFormula0012
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
    have p0059 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0013
        syntaxFormula0014 p0057 p0058
    have p0060 :=
      @g_bi1 (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        syntaxFormula0012
    have p0061 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0014
        syntaxFormula0015 p0059 p0060
    have p0062 :=
      @g_id (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
    have p0063 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P))
          (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0015))
        (.imp (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
          (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u))))
        p0061 p0062
    have p0064 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wbr (syn_cfv (syn_c1st) (.cv u)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv u)))
        syntaxFormula0012 p0055 p0063
    have p0065 :=
      @g_jcad (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0011
        syntaxFormula0012 p0052 p0064
    have p0067 := @g_biid syntaxFormula0011
    have p0068 :=
      @g_a1i (syn_wb syntaxFormula0011 syntaxFormula0011)
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0067
    have p0069 := @g_id (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u)))
    have p0070 :=
      @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r)
        (syn_cfv (syn_c1st) (.cv u))
        (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0069
    have p0071 :=
      @g_anbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) syntaxFormula0011
        syntaxFormula0011 syntaxFormula0016 syntaxFormula0012 p0068 p0070
    have p0073 :=
      @g_coeq2d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) (.cv r)
        (syn_cfv (syn_c1st) (.cv u))
        (syn_ccnv (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))) p0069
    have p0074 :=
      @g_coeq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) syntaxClass0017
        syntaxClass0018 (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) p0073
    have p0075 := (Nominal.classEqRefl syntaxClass0019)
    have p0076 := @g_eqcomi syntaxClass0019 syntaxClass0020 p0075
    have p0077 := (Nominal.classEqRefl syntaxClass0021)
    have p0078 := @g_eqcomi syntaxClass0021 syntaxClass0022 p0077
    have p0079 :=
      @g_n_3eqtr3g (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) syntaxClass0020
        syntaxClass0022 syntaxClass0019 syntaxClass0021 p0074 p0076 p0078
    have p0080 :=
      @g_breq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) syntaxClass0019
        syntaxClass0021 (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cwe) p0079
    have p0081 :=
      @g_imbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) syntaxFormula0023
        syntaxFormula0024 syntaxFormula0025 syntaxFormula0026 p0071 p0080
    have p0082 := @g_vex k
    have p0084 := @g_resex (.cv k) (syn_cfv (syn_c2nd) (.cv u)) p0082 p0023
    have p0085 := @g_dmex (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))) p0084
    have p0086 :=
      @g_f1oeq3 (.cv y) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
    have p0087 :=
      @g_id (.classEq (.cv y) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    have p0088 :=
      @g_breq2d
        (.classEq (.cv y) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv y) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv r)
        (syn_cwe) p0087
    have p0089 :=
      @g_anbi12d
        (.classEq (.cv y) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        syntaxFormula0027 syntaxFormula0011 (syn_wbr (.cv r) (syn_cwe) (.cv y))
        syntaxFormula0016 p0086 p0088
    have p0090 := @g_biid syntaxFormula0025
    have p0091 :=
      @g_a1i (syn_wb syntaxFormula0025 syntaxFormula0025)
        (.classEq (.cv y) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))) p0090
    have p0092 :=
      @g_imbi12d
        (.classEq (.cv y) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        syntaxFormula0028 syntaxFormula0023 syntaxFormula0025 syntaxFormula0025 p0089
        p0091
    have p0095 := @g_rnex (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))) p0084
    have p0096 :=
      @g_f1oeq2 (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)
        (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
    have p0097 := @g_biid (syn_wbr (.cv r) (syn_cwe) (.cv y))
    have p0098 :=
      @g_a1i
        (syn_wb (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classEq (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))) p0097
    have p0099 :=
      @g_anbi12d
        (.classEq (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        syntaxFormula0029 syntaxFormula0027 (syn_wbr (.cv r) (syn_cwe) (.cv y))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)) p0096 p0098
    have p0100 :=
      @g_id (.classEq (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    have p0101 :=
      @g_breq2d
        (.classEq (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) syntaxClass0019
        (syn_cwe) p0100
    have p0102 :=
      @g_imbi12d
        (.classEq (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        syntaxFormula0030 syntaxFormula0028 syntaxFormula0031 syntaxFormula0025 p0099
        p0101
    have p0105 := @g_cnvex (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))) p0084
    have p0106 :=
      @g_f1oeq1 (.cv x) (.cv y) (.cv f)
        (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
    have p0108 :=
      @g_a1i
        (syn_wb (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        p0097
    have p0109 :=
      @g_anbi12d
        (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wf1o (.cv f) (.cv x) (.cv y)) syntaxFormula0029
        (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)) p0106
        p0108
    have p0110 :=
      @g_id (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
    have p0111 :=
      @g_cnveqd
        (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) p0110
    have p0112 :=
      @g_coeq1d
        (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_ccnv (.cv f))
        (syn_ccnv (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))) (.cv r)
        p0111
    have p0114 :=
      @g_coeq12d
        (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_ccom (syn_ccnv (.cv f)) (.cv r)) syntaxClass0017 (.cv f)
        (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) p0112 p0110
    have p0115 := (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r)))
    have p0116 :=
      @g_eqcomi (syn_cpwpull (.cv f) (.cv r))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0115
    have p0119 :=
      @g_n_3eqtr3g
        (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) syntaxClass0020
        (syn_cpwpull (.cv f) (.cv r)) syntaxClass0019 p0114 p0116 p0076
    have p0120 :=
      @g_breq1d
        (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpwpull (.cv f) (.cv r)) syntaxClass0019 (.cv x) (syn_cwe) p0119
    have p0121 :=
      @g_imbi12d
        (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0030 (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x))
        syntaxFormula0031 p0109 p0120
    have p0122 :=
      @g_pwpullwesetimpndv x y f r dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
        dv_cache_0006 dv_cache_0007
    have p0123 :=
      @g_vtocl
        (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
          (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x)))
        syntaxFormula0032 f (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        dv_cache_0008 dv_cache_0009 p0105 p0121 p0122
    have p0124 :=
      @g_vtocl syntaxFormula0032 syntaxFormula0033 x
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0010
        dv_cache_0011 p0095 p0102 p0123
    have p0125 :=
      @g_vtocl syntaxFormula0033 syntaxFormula0034 y
        (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0012
        dv_cache_0013 p0085 p0092 p0124
    have p0126 :=
      @g_vtocl syntaxFormula0034 (.imp syntaxFormula0024 syntaxFormula0026) r
        (syn_cfv (syn_c1st) (.cv u)) dv_cache_0014 dv_cache_0015 p0022 p0081 p0125
    have p0127 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0024
        syntaxFormula0026 p0065 p0126
    have p0129 := @g_cnvcnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))
    have p0130 :=
      @g_coeq1i (syn_ccnv (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u)) p0129
    have p0131 :=
      @g_coeq1i syntaxClass0018 syntaxClass0035
        (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) p0130
    have p0132 := @g_eqtri syntaxClass0021 syntaxClass0022 syntaxClass0036 p0077 p0131
    have p0133 := @g_eqid (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
    have p0134 :=
      @g_breq12i syntaxClass0021 syntaxClass0036
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (syn_cwe) p0132 p0133
    have p0135 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0026
        syntaxFormula0037 p0127 p0134
    have p0136 := @g_imassrn (.cv k) (syn_cfv (syn_c2nd) (.cv u))
    have p0137 := @g_f1ofo (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)) (.cv k)
    have p0138 :=
      @g_syl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wf1o (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)))
        (syn_wfo (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k))) p0006 p0137
    have p0139 := @g_forn (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)) (.cv k)
    have p0140 :=
      @g_syl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wfo (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)))
        (.classEq (syn_crn (.cv k)) (syn_crn (.cv k))) p0138 p0139
    have p0141 :=
      @g_syl5sseq (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (syn_crn (.cv k))
        (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k)) p0136 p0140
    have p0142 :=
      @g_sseq1 (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k))
    have p0143 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0007
        syntaxFormula0039 p0042 p0142
    have p0144 :=
      @g_bicom syntaxFormula0038
        (syn_wss (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k)))
    have p0145 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0039
        syntaxFormula0040 p0143 p0144
    have p0146 :=
      @g_bi1 (syn_wss (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k)))
        syntaxFormula0038
    have p0147 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0040
        syntaxFormula0041 p0145 p0146
    have p0148 :=
      @g_id (syn_wss (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k)))
    have p0149 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P))
          (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0041))
        (.imp (syn_wss (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k)))
          (syn_wss (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k))))
        p0147 p0148
    have p0150 :=
      @g_mpdi (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wss (syn_cima (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_crn (.cv k)))
        syntaxFormula0038 p0141 p0149
    have p0151 :=
      @g_jcad (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0037
        syntaxFormula0038 p0135 p0150
    have p0155 :=
      @g_coex (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))) (syn_cfv (syn_c1st) (.cv u))
        p0084 p0022
    have p0159 :=
      @g_coex syntaxClass0035 (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        p0155 p0105
    have p0163 :=
      @g_elhwcodesclndv syntaxClass0036
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (syn_crn (.cv k)) p0159
        p0095
    have p0164 :=
      @g_syl6ibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wa syntaxFormula0037 syntaxFormula0038) syntaxFormula0043 p0151 p0163
    have p0165 :=
      @g_f1ofo (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
    have p0166 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0011
        syntaxFormula0044 p0052 p0165
    have p0168 := @g_biid syntaxFormula0044
    have p0169 :=
      @g_a1i (syn_wb syntaxFormula0044 syntaxFormula0044)
        (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) p0168
    have p0178 :=
      @g_sseq1d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) syntaxClass0019
        syntaxClass0021 syntaxClass0045 p0079
    have p0179 :=
      @g_imbi12d (.classEq (.cv r) (syn_cfv (syn_c1st) (.cv u))) syntaxFormula0044
        syntaxFormula0044 syntaxFormula0046 syntaxFormula0047 p0169 p0178
    have p0183 :=
      @g_foeq3 (.cv y) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
    have p0184 := @g_biid syntaxFormula0046
    have p0185 :=
      @g_a1i (syn_wb syntaxFormula0046 syntaxFormula0046)
        (.classEq (.cv y) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))) p0184
    have p0186 :=
      @g_imbi12d
        (.classEq (.cv y) (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        syntaxFormula0048 syntaxFormula0044 syntaxFormula0046 syntaxFormula0046 p0183
        p0185
    have p0190 :=
      @g_foeq2 (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv y)
        (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
    have p0193 :=
      @g_xpeq12d
        (.classEq (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) (.cv x)
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) p0100 p0100
    have p0194 :=
      @g_sseq2d
        (.classEq (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cxp (.cv x) (.cv x)) syntaxClass0045 syntaxClass0019 p0193
    have p0195 :=
      @g_imbi12d
        (.classEq (.cv x) (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        syntaxFormula0049 syntaxFormula0048 syntaxFormula0050 syntaxFormula0046 p0190
        p0194
    have p0199 :=
      @g_foeq1 (.cv x) (.cv y) (.cv f)
        (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
    have p0210 :=
      @g_sseq1d
        (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cpwpull (.cv f) (.cv r)) syntaxClass0019 (syn_cxp (.cv x) (.cv x)) p0119
    have p0211 :=
      @g_imbi12d
        (.classEq (.cv f) (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_wfo (.cv f) (.cv x) (.cv y)) syntaxFormula0049
        (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x)))
        syntaxFormula0050 p0199 p0210
    have p0212 :=
      @g_pwpullssxpsetimpndv x y f r dv_cache_0002 dv_cache_0003 dv_cache_0004
        dv_cache_0005 dv_cache_0006 dv_cache_0007
    have p0213 :=
      @g_vtocl
        (.imp (syn_wfo (.cv f) (.cv x) (.cv y))
          (syn_wss (syn_cpwpull (.cv f) (.cv r)) (syn_cxp (.cv x) (.cv x))))
        syntaxFormula0051 f (syn_ccnv (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        dv_cache_0008 dv_cache_0016 p0105 p0211 p0212
    have p0214 :=
      @g_vtocl syntaxFormula0051 syntaxFormula0052 x
        (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0010
        dv_cache_0017 p0095 p0195 p0213
    have p0215 :=
      @g_vtocl syntaxFormula0052 syntaxFormula0053 y
        (syn_cdm (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0012
        dv_cache_0018 p0085 p0186 p0214
    have p0216 :=
      @g_vtocl syntaxFormula0053 (.imp syntaxFormula0044 syntaxFormula0047) r
        (syn_cfv (syn_c1st) (.cv u)) dv_cache_0014 dv_cache_0019 p0022 p0179 p0215
    have p0217 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0044
        syntaxFormula0047 p0166 p0216
    have p0223 := @g_eqcomi syntaxClass0021 syntaxClass0036 p0132
    have p0224 := @g_sseq1i syntaxClass0036 syntaxClass0021 syntaxClass0045 p0223
    have p0225 :=
      @g_syl6ibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0047
        syntaxFormula0054 p0217 p0224
    have p0237 :=
      @g_opfv1st syntaxClass0036 (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        p0159 p0095
    have p0249 :=
      @g_opfv2nd syntaxClass0036 (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        p0159 p0095
    have p0262 :=
      @g_xpeq12i syntaxClass0055 (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        syntaxClass0055 (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u)))) p0249
        p0249
    have p0263 :=
      @g_sseq12i syntaxClass0056 syntaxClass0036 syntaxClass0057 syntaxClass0045 p0237
        p0262
    have p0264 :=
      @g_syl6ibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0054
        syntaxFormula0058 p0225 p0263
    have p0265 :=
      @g_jcad (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0043
        syntaxFormula0058 p0164 p0264
    have p0277 :=
      @g_opex syntaxClass0036 (syn_crn (syn_cres (.cv k) (syn_cfv (syn_c2nd) (.cv u))))
        p0159 p0095
    have p0278 := @g_elhwcncl (syn_crn (.cv k)) syntaxClass0042
    have p0279 := Nominal.mp p0277 p0278
    have p0280 :=
      @g_syl6ibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wa syntaxFormula0043 syntaxFormula0058) syntaxFormula0059 p0265 p0279
    have p0282 := @g_hncodetrnfnvalndv u (.cv k) p0082 p0014
    have p0283 :=
      @g_a1i (.classEq (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) syntaxClass0042)
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) p0282
    have p0284 :=
      @g_eleq1d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) syntaxClass0042
        (syn_chwcn (syn_crn (.cv k))) p0283
    have p0285 :=
      @g_biimprd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0060
        syntaxFormula0059 p0284
    have p0286 :=
      @g_sylcom (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0059
        syntaxFormula0060 p0280 p0285
    have p0287 := @g_hwcnraw a (syn_crn (.cv k))
    have p0288 := @g_hwcnpair a (syn_crn (.cv k))
    have p0289 :=
      @g_eleq1d (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) (.cv a)
        (syn_cop (syn_cfv (syn_c1st) (.cv a)) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_chwcodes (syn_crn (.cv k))) p0288
    have p0290 :=
      @g_mpbid (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv a) (syn_chwcodes (syn_crn (.cv k)))) syntaxFormula0061 p0287 p0289
    have p0291 := @g_fvex (.cv a) (syn_c1st)
    have p0292 := @g_fvex (.cv a) (syn_c2nd)
    have p0293 :=
      @g_elhwcodes (syn_crn (.cv k)) (syn_cfv (syn_c2nd) (.cv a))
        (syn_cfv (syn_c1st) (.cv a)) dv_cache_0020 p0291 p0292
    have p0294 := @g_biimpi syntaxFormula0061 syntaxFormula0062 p0293
    have p0295 :=
      @g_syl (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0061
        syntaxFormula0062 p0290 p0294
    have p0296 :=
      @g_simpld (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_crn (.cv k))) p0295
    have p0306 :=
      @g_simprd (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_crn (.cv k))) p0295
    have p0307 := @g_f1f (syn_cfv (syn_c2nd) (.cv u)) Y (.cv k)
    have p0308 :=
      @g_a1ii
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
          (syn_wf (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y))
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
          (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y))
        p0307 p0005
    have p0309 := @g_frn (syn_cfv (syn_c2nd) (.cv u)) Y (.cv k)
    have p0310 :=
      @g_syl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wf (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (syn_wss (syn_crn (.cv k)) Y)
        p0308 p0309
    have p0311 :=
      @g_a1d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wss (syn_crn (.cv k)) Y) (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        p0310
    have p0312 := @g_sstr (syn_cfv (syn_c2nd) (.cv a)) (syn_crn (.cv k)) Y
    have p0313 :=
      @g_ex (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_crn (.cv k)))
        (syn_wss (syn_crn (.cv k)) Y) (syn_wss (syn_cfv (syn_c2nd) (.cv a)) Y) p0312
    have p0314 :=
      @g_syl9 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) (syn_wss (syn_crn (.cv k)) Y)
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_crn (.cv k)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) Y) p0311 p0313
    have p0315 :=
      @g_syl5 (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_crn (.cv k)))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.imp (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
          (syn_wss (syn_cfv (syn_c2nd) (.cv a)) Y))
        p0306 p0314
    have p0316 :=
      @g_pm2_43d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) Y) p0315
    have p0317 :=
      @g_pm3_2
        (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) Y)
    have p0318 :=
      @g_syl9 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) Y)
        (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        syntaxFormula0063 p0316 p0317
    have p0319 :=
      @g_syl5 (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.imp (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0063) p0296
        p0318
    have p0320 :=
      @g_pm2_43d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0063 p0319
    have p0323 :=
      @g_elhwcodes Y (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c1st) (.cv a))
        dv_cache_0021 p0291 p0292
    have p0324 := @g_biimpri syntaxFormula0064 syntaxFormula0063 p0323
    have p0325 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0063
        syntaxFormula0064 p0320 p0324
    have p0327 :=
      @g_eleq1d (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) (.cv a)
        (syn_cop (syn_cfv (syn_c1st) (.cv a)) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_chwcodes Y) p0288
    have p0328 :=
      @g_biimprd (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv a) (syn_chwcodes Y)) syntaxFormula0064 p0327
    have p0329 :=
      @g_sylcom (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0064
        (.classMem (.cv a) (syn_chwcodes Y)) p0325 p0328
    have p0330 := @g_hwcnsupp a (syn_crn (.cv k))
    have p0331 := @g_pm3_2 (.classMem (.cv a) (syn_chwcodes Y)) syntaxFormula0065
    have p0332 :=
      @g_syl5 (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0065
        (.classMem (.cv a) (syn_chwcodes Y)) syntaxFormula0066 p0330 p0331
    have p0333 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv a) (syn_chwcodes Y))
        (.imp (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0066) p0329
        p0332
    have p0334 :=
      @g_pm2_43d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0066 p0333
    have p0335 := @g_elhwcn a Y
    have p0336 := @g_biimpri (.classMem (.cv a) (syn_chwcn Y)) syntaxFormula0066 p0335
    have p0337 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0066
        (.classMem (.cv a) (syn_chwcn Y)) p0334 p0336
    have p0338 :=
      @g_ssrdv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) a
        (syn_chwcn (syn_crn (.cv k))) (syn_chwcn Y) dv_cache_0022 dv_cache_0023
        dv_cache_0024 p0337
    have p0339 :=
      @g_sseld (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_chwcn (syn_crn (.cv k))) (syn_chwcn Y)
        (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) p0338
    have p0340 :=
      @g_sylcom (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0060
        (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwcn Y)) p0286 p0339
    have p0341 :=
      @g_hwnisoclasselhnordcl Y (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))
        hyp_cfbhnqinjcodecoverddndv_2
    have p0342 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwcn Y))
        syntaxFormula0067 p0340 p0341
    have p0343 :=
      @g_pm3_2 (syn_wfn (syn_chnqinc Y (syn_cun P Y)) (syn_chnord Y)) syntaxFormula0067
    have p0344 :=
      @g_syl9 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0067
        (syn_wfn (syn_chnqinc Y (syn_cun P Y)) (syn_chnord Y)) syntaxFormula0068 p0342
        p0343
    have p0345 :=
      @g_syl5 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wfn (syn_chnqinc Y (syn_cun P Y)) (syn_chnord Y))
        (.classMem (.cv u) (syn_chwcn P))
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0068) p0003
        p0344
    have p0346 :=
      @g_pm2_43d (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0068 p0345
    have p0347 :=
      @g_fnfvelrn (syn_chnord Y)
        (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        (syn_chnqinc Y (syn_cun P Y))
    have p0348 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0068
        syntaxFormula0070 p0346 p0347
    have p0349 := @g_hnqmap1valcl P (.cv u) hyp_cfbhnqinjcodecoverddndv_1
    have p0350 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P))
          (.classEq (syn_cfv (syn_chnqmap1 P) (syn_csn (.cv u)))
            (syn_cec (.cv u) (syn_chwniso P))))
        (.imp (.classMem (.cv u) (syn_chwcn P)) (.classMem (.cv u) (syn_chwcn P))) p0349
        p0010
    have p0351 := @g_snelpw1 (.cv u) (syn_chwcn P)
    have p0352 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P)) (.classMem (.cv u) (syn_chwcn P))
        (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn P))) p0010 p0351
    have p0353 := @g_hnqmap1fn P hyp_cfbhnqinjcodecoverddndv_1
    have p0354 :=
      @g_jctil (.classMem (.cv u) (syn_chwcn P))
        (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn P)))
        (syn_wfn (syn_chnqmap1 P) (syn_cpw1 (syn_chwcn P))) p0352 p0353
    have p0355 :=
      @g_fnbrfvb (syn_cpw1 (syn_chwcn P)) (syn_csn (.cv u))
        (syn_cec (.cv u) (syn_chwniso P)) (syn_chnqmap1 P)
    have p0356 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P))
        (syn_wa (syn_wfn (syn_chnqmap1 P) (syn_cpw1 (syn_chwcn P)))
          (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn P))))
        (syn_wb (.classEq (syn_cfv (syn_chnqmap1 P) (syn_csn (.cv u)))
            (syn_cec (.cv u) (syn_chwniso P)))
          (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 P) (syn_cec (.cv u) (syn_chwniso P))))
        p0354 p0355
    have p0357 :=
      @g_mpbid (.classMem (.cv u) (syn_chwcn P))
        (.classEq (syn_cfv (syn_chnqmap1 P) (syn_csn (.cv u)))
          (syn_cec (.cv u) (syn_chwniso P)))
        (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 P) (syn_cec (.cv u) (syn_chwniso P)))
        p0350 p0356
    have p0358 :=
      @g_brcnv (syn_cec (.cv u) (syn_chwniso P)) (syn_csn (.cv u)) (syn_chnqmap1 P)
    have p0359 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 P) (syn_cec (.cv u) (syn_chwniso P)))
        syntaxFormula0071 p0357 p0358
    have p0360 := @g_ssun1 P Y
    have p0361 := @g_hwcnssbase (syn_cun P Y) P p0360
    have p0362 := @g_ssel (syn_chwcn P) (syn_chwcn (syn_cun P Y)) (.cv u)
    have p0363 := Nominal.mp p0361 p0362
    exact
      continuation p0000 p0001 p0006 p0010 p0011 p0013 p0022 p0023 p0036 p0050 p0069 p0082
        p0084 p0140 p0282 p0286 p0288 p0291 p0292 p0296 p0306 p0310 p0330 p0340 p0346
        p0348 p0359 p0360 p0363

end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `ReplaySupport.CodeCover2`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbhnqinjcodecoverddndv_stage2 (u : Var) (P : Class) (k : Var)
    (Y : Class) (dv_P_u : u ∉ P.fv)
    (hyp_cfbhnqinjcodecoverddndv_1 : Nominal.NPrf (.classMem P (syn_cvv))) (p0001 : _)
    (p0010 : _) (p0011 : _) (p0023 : _) (p0291 : _) (p0292 : _) (p0359 : _) (p0360 : _)
    (p0363 : _) {Result : Type}
    (continuation : _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ →
        _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ →
        _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ →
        _ → _ → Result) :=
  show Result from
    by
    let proofSupport : Finset Var :=
      ({ u } : Finset Var) ∪ P.fv ∪ ({ k } : Finset Var) ∪ Y.fv
    let y : Var := freshVar proofSupport 1
    let x : Var := freshVar proofSupport 2
    let a : Var := freshVar proofSupport 4
    let z : Var := freshVar proofSupport 5
    let p : Var := freshVar proofSupport 6
    let q : Var := freshVar proofSupport 7
    let h : Var := freshVar proofSupport 8
    have fresh_y : y ∉ proofSupport :=
      by
      change freshVar proofSupport 1 ∉ proofSupport
      exact freshVar_not_mem proofSupport 1
    have fresh_y_ne_u : y ≠ u := by
      intro h
      exact
        fresh_y
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_y_not_P : y ∉ P.fv := by
      intro h
      exact
        fresh_y
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_x : x ∉ proofSupport :=
      by
      change freshVar proofSupport 2 ∉ proofSupport
      exact freshVar_not_mem proofSupport 2
    have fresh_x_ne_u : x ≠ u := by
      intro h
      exact
        fresh_x
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_x_not_P : x ∉ P.fv := by
      intro h
      exact
        fresh_x
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_x_not_Y : x ∉ Y.fv := by
      intro h
      exact fresh_x (Finset.mem_union_right _ (h))
    have fresh_a : a ∉ proofSupport :=
      by
      change freshVar proofSupport 4 ∉ proofSupport
      exact freshVar_not_mem proofSupport 4
    have fresh_a_ne_u : a ≠ u := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_u_ne_a : u ≠ a := Ne.symm fresh_a_ne_u
    have fresh_a_not_P : a ∉ P.fv := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_a_not_Y : a ∉ Y.fv := by
      intro h
      exact fresh_a (Finset.mem_union_right _ (h))
    have fresh_p : p ∉ proofSupport :=
      by
      change freshVar proofSupport 6 ∉ proofSupport
      exact freshVar_not_mem proofSupport 6
    have fresh_p_ne_u : p ≠ u := by
      intro h
      exact
        fresh_p
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_p_not_P : p ∉ P.fv := by
      intro h
      exact
        fresh_p
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_p_not_Y : p ∉ Y.fv := by
      intro h
      exact fresh_p (Finset.mem_union_right _ (h))
    have fresh_q : q ∉ proofSupport :=
      by
      change freshVar proofSupport 7 ∉ proofSupport
      exact freshVar_not_mem proofSupport 7
    have fresh_q_ne_u : q ≠ u := by
      intro h
      exact
        fresh_q
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_q_not_P : q ∉ P.fv := by
      intro h
      exact
        fresh_q
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_q_not_Y : q ∉ Y.fv := by
      intro h
      exact fresh_q (Finset.mem_union_right _ (h))
    have fresh_h : h ∉ proofSupport :=
      by
      change freshVar proofSupport 8 ∉ proofSupport
      exact freshVar_not_mem proofSupport 8
    have fresh_h_ne_u : h ≠ u := by
      intro h
      exact
        fresh_h
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_h_not_P : h ∉ P.fv := by
      intro h
      exact
        fresh_h
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_h_not_Y : h ∉ Y.fv := by
      intro h
      exact fresh_h (Finset.mem_union_right _ (h))
    have fresh_y_ne_x : y ≠ x :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 2
      exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
    have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
    have fresh_y_ne_p : y ≠ p :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
    have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
    have fresh_y_ne_q : y ≠ q :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
    have fresh_q_ne_y : q ≠ y := Ne.symm fresh_y_ne_q
    have fresh_y_ne_h : y ≠ h :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 8
      exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
    have fresh_h_ne_y : h ≠ y := Ne.symm fresh_y_ne_h
    have fresh_x_ne_p : x ≠ p :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
    have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
    have fresh_x_ne_q : x ≠ q :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
    have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
    have fresh_x_ne_h : x ≠ h :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 8
      exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
    have fresh_h_ne_x : h ≠ x := Ne.symm fresh_x_ne_h
    have fresh_z_ne_p : z ≠ p :=
      by
      change freshVar proofSupport 5 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
    have fresh_p_ne_z : p ≠ z := Ne.symm fresh_z_ne_p
    have fresh_z_ne_q : z ≠ q :=
      by
      change freshVar proofSupport 5 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
    have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
    have fresh_p_ne_q : p ≠ q :=
      by
      change freshVar proofSupport 6 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
    have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
    have dv_cache_0001 : u ∉ (P).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [dv_P_u, not_false_eq_true])
    have dv_cache_0007 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
    have dv_cache_0025 : x ∉ ((syn_csn (.cv u))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_u,
            not_false_eq_true])
    have dv_cache_0026 :
      x ∉
        ((syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso P)) (syn_ccnv (syn_chnqmap1 P))
              (syn_csn (.cv u))) (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 (syn_cun P Y))
              (syn_cec (.cv u) (syn_chwniso (syn_cun P Y)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_P, fresh_x_not_Y, or_false,
            not_false_eq_true])
    have dv_cache_0027 : x ∉ ((syn_cec (.cv u) (syn_chwniso P))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_P, or_false,
            not_false_eq_true])
    have dv_cache_0028 : x ∉ ((syn_cec (.cv u) (syn_chwniso (syn_cun P Y)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_P, fresh_x_not_Y, or_false,
            not_false_eq_true])
    have dv_cache_0029 : x ∉ ((syn_chnqmap1 (syn_cun P Y))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            fresh_x_not_P, fresh_x_not_Y, or_false, not_false_eq_true])
    have dv_cache_0030 : x ∉ ((syn_ccnv (syn_chnqmap1 P))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, fresh_x_not_P,
            not_false_eq_true])
    have dv_cache_0031 :
      x ∉
        ((syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
              (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_csn (.cv u)))
            (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 (syn_cun P Y))
              (syn_cec (.cv u) (syn_chwniso (syn_cun P Y)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_P, fresh_x_not_Y,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0032 :
      x ∉ ((syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0033 :
      x ∉ ((syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0034 : p ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_p_ne_x, not_false_eq_true])
    have dv_cache_0035 : p ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_p_ne_y, not_false_eq_true])
    have dv_cache_0036 : p ∉ ((syn_chnqmap1 (syn_cun P Y))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            fresh_p_not_P, fresh_p_not_Y, or_false, not_false_eq_true])
    have dv_cache_0037 :
      p ∉ ((syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_p_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0038 :
      p ∉
        ((syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 (syn_cun P Y))
                (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))) (.cv y))
            (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 (syn_cun P Y))
                (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))) (.cv z)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_not_P,
            fresh_p_not_Y, fresh_p_ne_u, fresh_p_ne_z, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0039 : q ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_q_ne_x, not_false_eq_true])
    have dv_cache_0040 : q ∉ ((Class.cv z)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_q_ne_z, not_false_eq_true])
    have dv_cache_0041 : q ∉ ((syn_chnqmap1 (syn_cun P Y))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            fresh_q_not_P, fresh_q_not_Y, or_false, not_false_eq_true])
    have dv_cache_0042 :
      q ∉ ((syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0043 :
      q ∉
        ((syn_wa (syn_wa (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 (syn_cun P Y))
                  (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))) (.cv y))
              (syn_wbr (.cv x) (syn_ccom (syn_chnqmap1 (syn_cun P Y))
                  (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))) (.cv z))) (syn_wa
              (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) (.cv p))
              (syn_wbr (.cv p) (syn_chnqmap1 (syn_cun P Y)) (.cv y))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, fresh_q_not_P,
            fresh_q_not_Y, fresh_q_ne_u, fresh_q_ne_z, fresh_q_ne_p,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0044 :
      Disjoint ((syn_cfv (syn_c2nd) (.cv u))).fv ((syn_cfv (syn_c1st) (.cv a))).fv := by
      exact
        (show Disjoint ((syn_cfv (syn_c2nd) (.cv u))).fv ((syn_cfv (syn_c1st) (.cv a))).fv from
          (by
            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv ((syn_c2nd))
                ((Class.cv u)),
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv ((syn_c1st))
                ((Class.cv a))];
            exact
              (show
                Disjoint ((((Class.cv u)).fv) ∪ (((syn_c2nd)).fv))
                  ((((Class.cv a)).fv) ∪ (((syn_c1st)).fv))
                from
                (Finset.disjoint_union_left.mpr
                  ⟨(show
                      Disjoint (((Class.cv u)).fv)
                        ((((Class.cv a)).fv) ∪ (((syn_c1st)).fv))
                      from
                      (Finset.disjoint_union_right.mpr
                        ⟨(show Disjoint (((Class.cv u)).fv) (((Class.cv a)).fv) from
                            (by
                              rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                              exact
                                (show Disjoint (({ u } : Finset Var)) (((Class.cv a)).fv)
                                  from
                                  (by
                                    rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                                    exact
                                      (show
                                        Disjoint (({ u } : Finset Var))
                                          (({ a } : Finset Var))
                                        from
                                        (Finset.disjoint_singleton_left.mpr
                                          (show u ∉ ({ a } : Finset Var) from
                                            (by
                                              simpa only [Finset.mem_singleton] using
                                                (show u ≠ a from
                                                  (by exact fresh_u_ne_a)))))))))),
                          (show Disjoint (((Class.cv u)).fv) (((syn_c1st)).fv) from
                            (by
                              rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                              exact
                                (show Disjoint (({ u } : Finset Var)) (((syn_c1st)).fv)
                                  from
                                  (by
                                    rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                                    exact
                                      (show
                                        Disjoint (({ u } : Finset Var)) ((∅ : Finset Var))
                                        from (by simp))))))⟩)),
                    (show
                      Disjoint (((syn_c2nd)).fv) ((((Class.cv a)).fv) ∪ (((syn_c1st)).fv))
                      from
                      (Finset.disjoint_union_right.mpr
                        ⟨(show Disjoint (((syn_c2nd)).fv) (((Class.cv a)).fv) from
                            (by
                              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd];
                              exact
                                (show Disjoint ((∅ : Finset Var)) (((Class.cv a)).fv) from
                                  (by simp)))),
                          (show Disjoint (((syn_c2nd)).fv) (((syn_c1st)).fv) from
                            (by
                              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd];
                              exact
                                (show Disjoint ((∅ : Finset Var)) (((syn_c1st)).fv) from
                                  (by simp))))⟩))⟩))))
    have dv_cache_0045 : Disjoint ((syn_cun P Y)).fv ((syn_cfv (syn_c1st) (.cv a))).fv :=
      by
      exact
        (show Disjoint ((syn_cun P Y)).fv ((syn_cfv (syn_c1st) (.cv a))).fv from (by
            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
            exact
              (show
                Disjoint (((P).fv) ∪ ((Y).fv)) ((((Class.cv a)).fv) ∪ (((syn_c1st)).fv))
                from
                (Finset.disjoint_union_left.mpr
                  ⟨(show Disjoint ((P).fv) ((((Class.cv a)).fv) ∪ (((syn_c1st)).fv)) from
                      (Finset.disjoint_union_right.mpr
                        ⟨(show Disjoint ((P).fv) (((Class.cv a)).fv) from
                            (by
                              rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                              exact
                                (show Disjoint ((P).fv) (({ a } : Finset Var)) from
                                  (Finset.disjoint_singleton_right.mpr
                                    (show a ∉ (P).fv from (by exact fresh_a_not_P)))))),
                          (show Disjoint ((P).fv) (((syn_c1st)).fv) from
                            (by
                              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                              exact
                                (show Disjoint ((P).fv) ((∅ : Finset Var)) from
                                  (by simp))))⟩)),
                    (show Disjoint ((Y).fv) ((((Class.cv a)).fv) ∪ (((syn_c1st)).fv)) from
                      (Finset.disjoint_union_right.mpr
                        ⟨(show Disjoint ((Y).fv) (((Class.cv a)).fv) from
                            (by
                              rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                              exact
                                (show Disjoint ((Y).fv) (({ a } : Finset Var)) from
                                  (Finset.disjoint_singleton_right.mpr
                                    (show a ∉ (Y).fv from (by exact fresh_a_not_Y)))))),
                          (show Disjoint ((Y).fv) (((syn_c1st)).fv) from
                            (by
                              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                              exact
                                (show Disjoint ((Y).fv) ((∅ : Finset Var)) from
                                  (by simp))))⟩))⟩))))
    have dv_cache_0046 : a ∉ ((syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0047 : a ∉ ((syn_chwcn (syn_cun P Y))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            fresh_a_not_P, fresh_a_not_Y, or_false, not_false_eq_true])
    have dv_cache_0048 : a ∉ ((Wff.classMem (.cv u) (syn_chwcn P))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_u, fresh_a_not_P, or_false,
            not_false_eq_true])
    have dv_cache_0049 : y ∉ ((syn_cuni (.cv q))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_q,
            not_false_eq_true])
    have dv_cache_0050 : x ∉ ((syn_cuni (.cv p))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_p,
            not_false_eq_true])
    have dv_cache_0051 : h ∉ ((syn_cfv (syn_c2nd) (.cv u))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_h_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0052 : h ≠ x := by exact (show h ≠ x from (by exact fresh_h_ne_x))
    have dv_cache_0053 : h ≠ y := by exact (show h ≠ y from (by exact fresh_h_ne_y))
    have dv_cache_0054 : h ∉ ((syn_cun P Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
            Finset.mem_union, fresh_h_not_P, fresh_h_not_Y, or_false, not_false_eq_true])
    have dv_cache_0055 : x ∉ ((Wff.classMem (.cv u) (syn_chwcn P))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_P, or_false,
            not_false_eq_true])
    have dv_cache_0056 :
      x ∉
        ((Wff.imp (syn_wa
              (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
              (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))) (.imp
              (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
              (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (.cv y))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_p, fresh_x_ne_u, fresh_x_ne_y, fresh_x_not_P,
            fresh_x_not_Y, compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0057 : y ∉ ((Wff.classMem (.cv u) (syn_chwcn P))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_u, fresh_y_not_P, or_false,
            not_false_eq_true])
    have dv_cache_0058 : y ∉ ((syn_cuni (.cv p))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_p,
            not_false_eq_true])
    let syntaxFormula0065 : Wff :=
      (syn_wss (syn_cfv (syn_c1st) (.cv a))
        (syn_cxp (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c2nd) (.cv a))))
    let syntaxFormula0071 : Wff :=
      (syn_wbr (syn_cec (.cv u) (syn_chwniso P)) (syn_ccnv (syn_chnqmap1 P)) (syn_csn (.cv u)))
    let syntaxFormula0072 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (syn_csn (.cv u)))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0073 : Wff :=
      (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 (syn_cun P Y))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0074 : Wff :=
      (syn_wbr (.cv x) (syn_chnqmap1 (syn_cun P Y))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0075 : Wff :=
      (syn_wa (syn_wbr (syn_cec (.cv u) (syn_chwniso P)) (syn_ccnv (syn_chnqmap1 P)) (.cv x))
        syntaxFormula0074)
    let syntaxFormula0076 : Wff := (syn_wa syntaxFormula0071 syntaxFormula0073)
    let syntaxFormula0077 : Wff := (syn_wex x syntaxFormula0075)
    let syntaxFormula0078 : Wff :=
      (syn_wbr (syn_cec (.cv u) (syn_chwniso P)) (syn_chnqinc P (syn_cun P Y))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0079 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv u)))
        (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0080 : Wff :=
      (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0081 : Wff :=
      (syn_wfn (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0082 : Wff := (syn_wa syntaxFormula0081 syntaxFormula0080)
    let syntaxFormula0083 : Wff :=
      (syn_wbr (syn_csn (.cv u)) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0084 : Wff := (syn_wb syntaxFormula0079 syntaxFormula0083)
    let syntaxFormula0085 : Wff :=
      (syn_wbr (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) (syn_csn (.cv u)))
    let syntaxFormula0086 : Wff :=
      (syn_wbr (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) (.cv x))
    let syntaxFormula0087 : Wff := (syn_wa syntaxFormula0086 syntaxFormula0074)
    let syntaxFormula0088 : Wff := (syn_wa syntaxFormula0085 syntaxFormula0073)
    let syntaxFormula0089 : Wff := (syn_wex x syntaxFormula0087)
    let syntaxClass0090 : Class :=
      (syn_ccom (syn_chnqmap1 (syn_cun P Y))
        (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0091 : Wff :=
      (syn_wbr (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        syntaxClass0090 (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0092 : Wff :=
      (syn_wbr (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0093 : Wff := (syn_wbr (.cv x) syntaxClass0090 (.cv y))
    let syntaxFormula0094 : Wff := (syn_wbr (.cv x) syntaxClass0090 (.cv z))
    let syntaxFormula0095 : Wff := (syn_wa syntaxFormula0093 syntaxFormula0094)
    let syntaxFormula0096 : Wff :=
      (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) (.cv p))
    let syntaxFormula0097 : Wff :=
      (syn_wa syntaxFormula0096 (syn_wbr (.cv p) (syn_chnqmap1 (syn_cun P Y)) (.cv y)))
    let syntaxFormula0098 : Wff := (syn_wex p syntaxFormula0097)
    let syntaxFormula0099 : Wff :=
      (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) (.cv q))
    let syntaxFormula0100 : Wff :=
      (syn_wa syntaxFormula0099 (syn_wbr (.cv q) (syn_chnqmap1 (syn_cun P Y)) (.cv z)))
    let syntaxFormula0101 : Wff := (syn_wex q syntaxFormula0100)
    let syntaxFormula0102 : Wff := (syn_wa syntaxFormula0095 syntaxFormula0097)
    let syntaxFormula0103 : Wff := (syn_wa syntaxFormula0102 syntaxFormula0100)
    let syntaxFormula0104 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv p)) (.cv x))
    let syntaxFormula0105 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv q)) (.cv x))
    let syntaxFormula0106 : Wff :=
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))))
    let syntaxFormula0107 : Wff :=
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv a)) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0108 : Wff :=
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0109 : Wff :=
      (syn_wa (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cun P Y)))
    let syntaxFormula0110 : Wff :=
      (.classMem (syn_cop (syn_cfv (syn_c1st) (.cv a)) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_chwcodes (syn_cun P Y)))
    let syntaxFormula0111 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_chwcodes (syn_cun P Y))) syntaxFormula0065)
    let syntaxFormula0112 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (syn_csn (syn_cuni (.cv p))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0113 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p))
        (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (syn_csn (syn_cuni (.cv p)))))
    let syntaxFormula0114 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0115 : Wff := (syn_wb syntaxFormula0113 syntaxFormula0114)
    let syntaxFormula0116 : Wff := (.imp syntaxFormula0113 syntaxFormula0114)
    let syntaxFormula0117 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv p))
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv q)))
    let syntaxClass0118 : Class :=
      (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (syn_cuni (.cv p))))
    let syntaxFormula0119 : Wff :=
      (.classEq syntaxClass0118
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0120 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv p))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0121 : Wff := (syn_wa syntaxFormula0106 syntaxFormula0117)
    let syntaxClass0122 : Class :=
      (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (syn_cuni (.cv q))))
    let syntaxFormula0123 : Wff :=
      (.classEq syntaxClass0122
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0124 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv q))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0125 : Wff :=
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0126 : Wff :=
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0127 : Wff :=
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_cuni (.cv q)))
    let syntaxFormula0128 : Wff := (syn_wb syntaxFormula0126 syntaxFormula0127)
    let syntaxFormula0129 : Wff :=
      (syn_wa (.classMem (.cv x) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0130 : Wff :=
      (syn_wa (.classMem (.cv x) (syn_chwcn (syn_cun P Y)))
        (.classMem (.cv y) (syn_chwcn (syn_cun P Y))))
    let syntaxFormula0131 : Wff :=
      (syn_wa (.classMem (.cv x) (syn_chwcodes (syn_cun P Y)))
        (.classMem (.cv y) (syn_chwcodes (syn_cun P Y))))
    let syntaxFormula0132 : Wff :=
      (syn_wa syntaxFormula0129
        (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y)))
    let syntaxFormula0133 : Wff :=
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
        (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))
    let syntaxFormula0134 : Wff := (syn_wex h syntaxFormula0133)
    let syntaxFormula0135 : Wff := (syn_wa syntaxFormula0131 syntaxFormula0134)
    let syntaxFormula0136 : Wff :=
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0137 : Wff :=
      (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (.cv y)))
    let syntaxFormula0138 : Wff := (.imp syntaxFormula0136 syntaxFormula0137)
    let syntaxFormula0139 : Wff :=
      (.imp (.classEq (.cv x) (syn_cuni (.cv p))) syntaxFormula0138)
    let syntaxFormula0140 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0138)
    let syntaxFormula0141 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv)))
    let syntaxFormula0142 : Wff :=
      (.imp syntaxFormula0127
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q))))
    let syntaxFormula0143 : Wff := (.imp syntaxFormula0125 syntaxFormula0142)
    let syntaxFormula0144 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0143)
    let syntaxFormula0145 : Wff :=
      (.imp (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0144)
    have p0364 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P)) (.classMem (.cv u) (syn_chwcn (syn_cun P Y))))
        (.imp (.classMem (.cv u) (syn_chwcn P)) (.classMem (.cv u) (syn_chwcn P))) p0363
        p0010
    have p0366 := @g_hnqmap1valcl (syn_cun P Y) (.cv u) p0001
    have p0367 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv u) (syn_chwcn (syn_cun P Y))) syntaxFormula0072 p0364 p0366
    have p0368 := @g_snelpw1 (.cv u) (syn_chwcn (syn_cun P Y))
    have p0369 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv u) (syn_chwcn (syn_cun P Y)))
        (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn (syn_cun P Y)))) p0364 p0368
    have p0370 := @g_hnqmap1fn (syn_cun P Y) p0001
    have p0371 :=
      @g_jctil (.classMem (.cv u) (syn_chwcn P))
        (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn (syn_cun P Y))))
        (syn_wfn (syn_chnqmap1 (syn_cun P Y)) (syn_cpw1 (syn_chwcn (syn_cun P Y)))) p0369
        p0370
    have p0372 :=
      @g_fnbrfvb (syn_cpw1 (syn_chwcn (syn_cun P Y))) (syn_csn (.cv u))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))) (syn_chnqmap1 (syn_cun P Y))
    have p0373 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P))
        (syn_wa (syn_wfn (syn_chnqmap1 (syn_cun P Y)) (syn_cpw1 (syn_chwcn (syn_cun P Y))))
          (.classMem (syn_csn (.cv u)) (syn_cpw1 (syn_chwcn (syn_cun P Y)))))
        (syn_wb syntaxFormula0072 syntaxFormula0073) p0371 p0372
    have p0374 :=
      @g_mpbid (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0072 syntaxFormula0073 p0367
        p0373
    have p0375 :=
      @g_jca (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0071 syntaxFormula0073 p0359
        p0374
    have p0376 := @g_snex (.cv u)
    have p0377 := @g_id (.classEq (.cv x) (syn_csn (.cv u)))
    have p0378 :=
      @g_breq2d (.classEq (.cv x) (syn_csn (.cv u))) (.cv x) (syn_csn (.cv u))
        (syn_cec (.cv u) (syn_chwniso P)) (syn_ccnv (syn_chnqmap1 P)) p0377
    have p0380 :=
      @g_breq1d (.classEq (.cv x) (syn_csn (.cv u))) (.cv x) (syn_csn (.cv u))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))) (syn_chnqmap1 (syn_cun P Y)) p0377
    have p0381 :=
      @g_anbi12d (.classEq (.cv x) (syn_csn (.cv u)))
        (syn_wbr (syn_cec (.cv u) (syn_chwniso P)) (syn_ccnv (syn_chnqmap1 P)) (.cv x))
        syntaxFormula0071 syntaxFormula0074 syntaxFormula0073 p0378 p0380
    have p0382 :=
      @g_spcev syntaxFormula0075 syntaxFormula0076 x (syn_csn (.cv u)) dv_cache_0025
        dv_cache_0026 p0376 p0381
    have p0383 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0076 syntaxFormula0077 p0375
        p0382
    have p0384 :=
      @g_brco x (syn_cec (.cv u) (syn_chwniso P))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))) (syn_chnqmap1 (syn_cun P Y))
        (syn_ccnv (syn_chnqmap1 P)) dv_cache_0027 dv_cache_0028 dv_cache_0029
        dv_cache_0030
    have p0385 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0077
        (syn_wbr (syn_cec (.cv u) (syn_chwniso P))
          (syn_ccom (syn_chnqmap1 (syn_cun P Y)) (syn_ccnv (syn_chnqmap1 P)))
          (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
        p0383 p0384
    have p0386 := (Nominal.classEqRefl (syn_chnqinc P (syn_cun P Y)))
    have p0387 :=
      @g_breqi (syn_cec (.cv u) (syn_chwniso P))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))) (syn_chnqinc P (syn_cun P Y))
        (syn_ccom (syn_chnqmap1 (syn_cun P Y)) (syn_ccnv (syn_chnqmap1 P))) p0386
    have p0388 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wbr (syn_cec (.cv u) (syn_chwniso P))
          (syn_ccom (syn_chnqmap1 (syn_cun P Y)) (syn_ccnv (syn_chnqmap1 P)))
          (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
        syntaxFormula0078 p0385 p0387
    have p0389 := @g_hwnisoclasselhnordcl P (.cv u) hyp_cfbhnqinjcodecoverddndv_1
    have p0390 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P))
          (.classMem (syn_cec (.cv u) (syn_chwniso P)) (syn_chnord P)))
        (.imp (.classMem (.cv u) (syn_chwcn P)) (.classMem (.cv u) (syn_chwcn P))) p0389
        p0010
    have p0391 := @g_hnqincfn (syn_cun P Y) P p0360 hyp_cfbhnqinjcodecoverddndv_1 p0001
    have p0392 :=
      @g_jctil (.classMem (.cv u) (syn_chwcn P))
        (.classMem (syn_cec (.cv u) (syn_chwniso P)) (syn_chnord P))
        (syn_wfn (syn_chnqinc P (syn_cun P Y)) (syn_chnord P)) p0390 p0391
    have p0393 :=
      @g_fnbrfvb (syn_chnord P) (syn_cec (.cv u) (syn_chwniso P))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))) (syn_chnqinc P (syn_cun P Y))
    have p0394 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P))
        (syn_wa (syn_wfn (syn_chnqinc P (syn_cun P Y)) (syn_chnord P))
          (.classMem (syn_cec (.cv u) (syn_chwniso P)) (syn_chnord P)))
        (syn_wb (.classEq
            (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
            (syn_cec (.cv u) (syn_chwniso (syn_cun P Y)))) syntaxFormula0078)
        p0392 p0393
    have p0395 :=
      @g_mpbird (.classMem (.cv u) (syn_chwcn P))
        (.classEq (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
          (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
        syntaxFormula0078 p0388 p0394
    have p0397 := @g_hnqmap1valcl (syn_cfv (syn_c2nd) (.cv u)) (.cv u) p0023
    have p0398 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0079
        p0011 p0397
    have p0399 := @g_snelpw1 (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
    have p0400 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0080
        p0011 p0399
    have p0401 := @g_hnqmap1fn (syn_cfv (syn_c2nd) (.cv u)) p0023
    have p0402 :=
      @g_jctil (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0080 syntaxFormula0081 p0400
        p0401
    have p0403 :=
      @g_fnbrfvb (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) (syn_csn (.cv u))
        (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0404 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0082 syntaxFormula0084 p0402
        p0403
    have p0405 :=
      @g_mpbid (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0079 syntaxFormula0083 p0398
        p0404
    have p0406 :=
      @g_brcnv (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_csn (.cv u)) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0407 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0083 syntaxFormula0085
        p0405 p0406
    have p0408 :=
      @g_jca (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0085 syntaxFormula0073 p0407
        p0374
    have p0411 :=
      @g_breq2d (.classEq (.cv x) (syn_csn (.cv u))) (.cv x) (syn_csn (.cv u))
        (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) p0377
    have p0414 :=
      @g_anbi12d (.classEq (.cv x) (syn_csn (.cv u))) syntaxFormula0086 syntaxFormula0085
        syntaxFormula0074 syntaxFormula0073 p0411 p0380
    have p0415 :=
      @g_spcev syntaxFormula0087 syntaxFormula0088 x (syn_csn (.cv u)) dv_cache_0025
        dv_cache_0031 p0376 p0414
    have p0416 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0088 syntaxFormula0089 p0408
        p0415
    have p0417 :=
      @g_brco x (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))) (syn_chnqmap1 (syn_cun P Y))
        (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0032 dv_cache_0028
        dv_cache_0029 dv_cache_0033
    have p0418 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0089 syntaxFormula0091
        p0416 p0417
    have p0419 :=
      (Nominal.classEqRefl (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y)))
    have p0420 :=
      @g_breqi (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y)))
        (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y)) syntaxClass0090 p0419
    have p0421 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0091 syntaxFormula0092
        p0418 p0420
    have p0422 := @g_simpl syntaxFormula0093 syntaxFormula0094
    have p0423 :=
      @g_brco p (.cv x) (.cv y) (syn_chnqmap1 (syn_cun P Y))
        (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0034 dv_cache_0035
        dv_cache_0036 dv_cache_0037
    have p0424 :=
      @g_sylib syntaxFormula0095 syntaxFormula0093 syntaxFormula0098 p0422 p0423
    have p0425 := Nominal.ax17 syntaxFormula0095 p dv_cache_0038
    have p0426 := @g_simpl syntaxFormula0095 syntaxFormula0097
    have p0427 := @g_simpr syntaxFormula0093 syntaxFormula0094
    have p0428 :=
      @g_brco q (.cv x) (.cv z) (syn_chnqmap1 (syn_cun P Y))
        (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) dv_cache_0039 dv_cache_0040
        dv_cache_0041 dv_cache_0042
    have p0429 :=
      @g_sylib syntaxFormula0095 syntaxFormula0094 syntaxFormula0101 p0427 p0428
    have p0430 := @g_syl syntaxFormula0102 syntaxFormula0095 syntaxFormula0101 p0426 p0429
    have p0431 := Nominal.ax17 syntaxFormula0102 q dv_cache_0043
    have p0432 := @g_simpl syntaxFormula0102 syntaxFormula0100
    have p0433 := @g_simpr syntaxFormula0095 syntaxFormula0097
    have p0434 := @g_syl syntaxFormula0103 syntaxFormula0102 syntaxFormula0097 p0432 p0433
    have p0435 :=
      @g_simpr syntaxFormula0096 (syn_wbr (.cv p) (syn_chnqmap1 (syn_cun P Y)) (.cv y))
    have p0436 :=
      @g_syl syntaxFormula0103 syntaxFormula0097
        (syn_wbr (.cv p) (syn_chnqmap1 (syn_cun P Y)) (.cv y)) p0434 p0435
    have p0439 :=
      @g_fnfun (syn_cpw1 (syn_chwcn (syn_cun P Y))) (syn_chnqmap1 (syn_cun P Y))
    have p0440 := Nominal.mp p0370 p0439
    have p0441 := @g_funbrfv (.cv p) (.cv y) (syn_chnqmap1 (syn_cun P Y))
    have p0442 := Nominal.mp p0440 p0441
    have p0443 :=
      @g_syl syntaxFormula0103 (syn_wbr (.cv p) (syn_chnqmap1 (syn_cun P Y)) (.cv y))
        (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p)) (.cv y)) p0436 p0442
    have p0444 :=
      @g_eqcomd syntaxFormula0103 (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p)) (.cv y)
        p0443
    have p0448 :=
      @g_simpl syntaxFormula0096 (syn_wbr (.cv p) (syn_chnqmap1 (syn_cun P Y)) (.cv y))
    have p0449 := @g_syl syntaxFormula0103 syntaxFormula0097 syntaxFormula0096 p0434 p0448
    have p0450 := @g_brcnv (.cv x) (.cv p) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0451 :=
      @g_sylib syntaxFormula0103 syntaxFormula0096
        (syn_wbr (.cv p) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv x)) p0449 p0450
    have p0453 :=
      @g_fnfun (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0454 := Nominal.mp p0401 p0453
    have p0455 := @g_funbrfv (.cv p) (.cv x) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0456 := Nominal.mp p0454 p0455
    have p0457 :=
      @g_syl syntaxFormula0103
        (syn_wbr (.cv p) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv x))
        syntaxFormula0104 p0451 p0456
    have p0458 := @g_simpr syntaxFormula0102 syntaxFormula0100
    have p0459 :=
      @g_simpl syntaxFormula0099 (syn_wbr (.cv q) (syn_chnqmap1 (syn_cun P Y)) (.cv z))
    have p0460 := @g_syl syntaxFormula0103 syntaxFormula0100 syntaxFormula0099 p0458 p0459
    have p0461 := @g_brcnv (.cv x) (.cv q) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0462 :=
      @g_sylib syntaxFormula0103 syntaxFormula0099
        (syn_wbr (.cv q) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv x)) p0460 p0461
    have p0466 := @g_funbrfv (.cv q) (.cv x) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0467 := Nominal.mp p0454 p0466
    have p0468 :=
      @g_syl syntaxFormula0103
        (syn_wbr (.cv q) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv x))
        syntaxFormula0105 p0462 p0467
    have p0469 :=
      @g_eqtr4d syntaxFormula0103
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv p)) (.cv x)
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv q)) p0457 p0468
    have p0477 := @g_breldm (.cv p) (.cv x) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0478 :=
      @g_syl syntaxFormula0103
        (syn_wbr (.cv p) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv x))
        (.classMem (.cv p) (syn_cdm (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))) p0451
        p0477
    have p0480 :=
      @g_fndm (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0481 := Nominal.mp p0401 p0480
    have p0482 :=
      @g_syl6eleq syntaxFormula0103 (.cv p)
        (syn_cdm (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) p0478 p0481
    have p0488 := @g_breldm (.cv q) (.cv x) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0489 :=
      @g_syl syntaxFormula0103
        (syn_wbr (.cv q) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv x))
        (.classMem (.cv q) (syn_cdm (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))) p0462
        p0488
    have p0493 :=
      @g_syl6eleq syntaxFormula0103 (.cv q)
        (syn_cdm (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) p0489 p0481
    have p0494 :=
      @g_jca syntaxFormula0103
        (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))) p0482
        p0493
    have p0495 :=
      @g_simpl (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
    have p0496 := @g_hnwpw1argcl (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))) p
    have p0497 :=
      @g_simprd (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0496
    have p0498 :=
      @g_syl syntaxFormula0106
        (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0495 p0497
    have p0499 :=
      @g_fveq2d syntaxFormula0106 (.cv p) (syn_csn (syn_cuni (.cv p)))
        (syn_chnqmap1 (syn_cun P Y)) p0498
    have p0502 :=
      @g_simpld (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv p) (syn_csn (syn_cuni (.cv p)))) p0496
    have p0503 :=
      @g_syl syntaxFormula0106
        (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) p0495
        p0502
    have p0504 := @g_hwcnraw a (syn_cfv (syn_c2nd) (.cv u))
    have p0505 := @g_hwcnpair a (syn_cfv (syn_c2nd) (.cv u))
    have p0506 :=
      @g_eleq1d (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) (.cv a)
        (syn_cop (syn_cfv (syn_c1st) (.cv a)) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))) p0505
    have p0507 :=
      @g_mpbid (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv a) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0107
        p0504 p0506
    have p0510 :=
      @g_elhwcodes (syn_cfv (syn_c2nd) (.cv u)) (syn_cfv (syn_c2nd) (.cv a))
        (syn_cfv (syn_c1st) (.cv a)) dv_cache_0044 p0291 p0292
    have p0511 := @g_biimpi syntaxFormula0107 syntaxFormula0108 p0510
    have p0512 :=
      @g_syl (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        syntaxFormula0107 syntaxFormula0108 p0507 p0511
    have p0513 :=
      @g_simpld (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c2nd) (.cv u))) p0512
    have p0523 :=
      @g_simprd (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c2nd) (.cv u))) p0512
    have p0524 := @g_hwcnbase u P dv_cache_0001
    have p0525 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P)) (syn_wss (syn_cfv (syn_c2nd) (.cv u)) P))
        (.imp (.classMem (.cv u) (syn_chwcn P)) (.classMem (.cv u) (syn_chwcn P))) p0524
        p0010
    have p0527 :=
      @g_syl6ss (.classMem (.cv u) (syn_chwcn P)) (syn_cfv (syn_c2nd) (.cv u)) P
        (syn_cun P Y) p0525 p0360
    have p0528 :=
      @g_a1d (.classMem (.cv u) (syn_chwcn P))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) p0527
    have p0529 :=
      @g_sstr (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y)
    have p0530 :=
      @g_ex (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cun P Y)) p0529
    have p0531 :=
      @g_syl9 (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wss (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c2nd) (.cv u)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cun P Y)) p0528 p0530
    have p0532 :=
      @g_syl5 (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c2nd) (.cv u)))
        (.classMem (.cv u) (syn_chwcn P))
        (.imp (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
          (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cun P Y)))
        p0523 p0531
    have p0533 :=
      @g_pm2_43d (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cun P Y)) p0532
    have p0534 :=
      @g_pm3_2
        (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cun P Y))
    have p0535 :=
      @g_syl9 (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wss (syn_cfv (syn_c2nd) (.cv a)) (syn_cun P Y))
        (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        syntaxFormula0109 p0533 p0534
    have p0536 :=
      @g_syl5 (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_wbr (syn_cfv (syn_c1st) (.cv a)) (syn_cwe) (syn_cfv (syn_c2nd) (.cv a)))
        (.classMem (.cv u) (syn_chwcn P))
        (.imp (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0109)
        p0513 p0535
    have p0537 :=
      @g_pm2_43d (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0109
        p0536
    have p0540 :=
      @g_elhwcodes (syn_cun P Y) (syn_cfv (syn_c2nd) (.cv a)) (syn_cfv (syn_c1st) (.cv a))
        dv_cache_0045 p0291 p0292
    have p0541 := @g_biimpri syntaxFormula0110 syntaxFormula0109 p0540
    have p0542 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0109
        syntaxFormula0110 p0537 p0541
    have p0544 :=
      @g_eleq1d (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) (.cv a)
        (syn_cop (syn_cfv (syn_c1st) (.cv a)) (syn_cfv (syn_c2nd) (.cv a)))
        (syn_chwcodes (syn_cun P Y)) p0505
    have p0545 :=
      @g_biimprd (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv a) (syn_chwcodes (syn_cun P Y))) syntaxFormula0110 p0544
    have p0546 :=
      @g_sylcom (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0110
        (.classMem (.cv a) (syn_chwcodes (syn_cun P Y))) p0542 p0545
    have p0547 := @g_hwcnsupp a (syn_cfv (syn_c2nd) (.cv u))
    have p0548 :=
      @g_pm3_2 (.classMem (.cv a) (syn_chwcodes (syn_cun P Y))) syntaxFormula0065
    have p0549 :=
      @g_syl5 (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        syntaxFormula0065 (.classMem (.cv a) (syn_chwcodes (syn_cun P Y)))
        syntaxFormula0111 p0547 p0548
    have p0550 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv a) (syn_chwcodes (syn_cun P Y)))
        (.imp (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0111)
        p0546 p0549
    have p0551 :=
      @g_pm2_43d (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0111
        p0550
    have p0552 := @g_elhwcn a (syn_cun P Y)
    have p0553 :=
      @g_biimpri (.classMem (.cv a) (syn_chwcn (syn_cun P Y))) syntaxFormula0111 p0552
    have p0554 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0111
        (.classMem (.cv a) (syn_chwcn (syn_cun P Y))) p0551 p0553
    have p0555 :=
      @g_ssrdv (.classMem (.cv u) (syn_chwcn P)) a
        (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcn (syn_cun P Y)) dv_cache_0046
        dv_cache_0047 dv_cache_0048 p0554
    have p0556 :=
      @g_sseld (.classMem (.cv u) (syn_chwcn P)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcn (syn_cun P Y)) (syn_cuni (.cv p)) p0555
    have p0557 :=
      @g_syl5 syntaxFormula0106
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv u) (syn_chwcn P))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cun P Y))) p0503 p0556
    have p0558 := @g_hnqmap1valcl (syn_cun P Y) (syn_cuni (.cv p)) p0001
    have p0559 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cun P Y))) syntaxFormula0112 p0557
        p0558
    have p0560 :=
      @g_eqeq2 (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (syn_csn (syn_cuni (.cv p))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)))
        (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p))
    have p0561 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106 syntaxFormula0112
        syntaxFormula0115 p0559 p0560
    have p0562 := @g_bi1 syntaxFormula0113 syntaxFormula0114
    have p0563 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106 syntaxFormula0115
        syntaxFormula0116 p0561 p0562
    have p0564 :=
      @g_mpdi (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106 syntaxFormula0113
        syntaxFormula0114 p0499 p0563
    have p0565 :=
      @g_adantrd (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106 syntaxFormula0114
        syntaxFormula0117 p0564
    have p0570 :=
      @g_fveq2d syntaxFormula0106 (.cv p) (syn_csn (syn_cuni (.cv p)))
        (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) p0498
    have p0575 := @g_hnqmap1valcl (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (.cv p)) p0023
    have p0576 :=
      @g_syl syntaxFormula0106
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        syntaxFormula0119 p0503 p0575
    have p0577 :=
      @g_eqtrd syntaxFormula0106
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv p)) syntaxClass0118
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) p0570
        p0576
    have p0578 := @g_adantr syntaxFormula0106 syntaxFormula0120 syntaxFormula0117 p0577
    have p0579 :=
      @g_eqcomd syntaxFormula0121
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv p))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) p0578
    have p0580 := @g_simpr syntaxFormula0106 syntaxFormula0117
    have p0581 :=
      @g_eqtrd syntaxFormula0121
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv p))
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv q)) p0579 p0580
    have p0582 :=
      @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
    have p0583 := @g_hnwpw1argcl (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))) q
    have p0584 :=
      @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0583
    have p0585 :=
      @g_syl syntaxFormula0106
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0582 p0584
    have p0586 :=
      @g_fveq2d syntaxFormula0106 (.cv q) (syn_csn (syn_cuni (.cv q)))
        (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) p0585
    have p0589 :=
      @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p0583
    have p0590 :=
      @g_syl syntaxFormula0106
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) p0582
        p0589
    have p0591 := @g_hnqmap1valcl (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (.cv q)) p0023
    have p0592 :=
      @g_syl syntaxFormula0106
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        syntaxFormula0123 p0590 p0591
    have p0593 :=
      @g_eqtrd syntaxFormula0106
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv q)) syntaxClass0122
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) p0586
        p0592
    have p0594 := @g_adantr syntaxFormula0106 syntaxFormula0124 syntaxFormula0117 p0593
    have p0595 :=
      @g_eqtrd syntaxFormula0121
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv q))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) p0581
        p0594
    have p0604 :=
      @g_jca syntaxFormula0106
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) p0503
        p0590
    have p0605 := @g_adantr syntaxFormula0106 syntaxFormula0125 syntaxFormula0117 p0604
    have p0606 :=
      @g_hwnisoclasseqbcl (syn_cfv (syn_c2nd) (.cv u)) (syn_cuni (.cv p))
        (syn_cuni (.cv q)) p0023
    have p0607 := @g_syl syntaxFormula0121 syntaxFormula0125 syntaxFormula0128 p0605 p0606
    have p0608 := @g_biimpd syntaxFormula0121 syntaxFormula0126 syntaxFormula0127 p0607
    have p0609 := @g_mpd syntaxFormula0121 syntaxFormula0126 syntaxFormula0127 p0595 p0608
    have p0620 :=
      @g_simpl (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
    have p0621 := @g_elex (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
    have p0622 :=
      @g_syl syntaxFormula0125
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (syn_cuni (.cv p)) (syn_cvv)) p0620 p0621
    have p0623 :=
      @g_simpr (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
    have p0624 := @g_elex (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
    have p0625 :=
      @g_syl syntaxFormula0125
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0623 p0624
    have p0626 :=
      @g_jca syntaxFormula0125 (.classMem (syn_cuni (.cv p)) (syn_cvv))
        (.classMem (syn_cuni (.cv q)) (syn_cvv)) p0622 p0625
    have p0627 := @g_nfcv y (syn_cuni (.cv q)) dv_cache_0049
    have p0628 := @g_issetf y (syn_cuni (.cv q)) p0627
    have p0629 := @g_nfcv x (syn_cuni (.cv p)) dv_cache_0050
    have p0630 := @g_issetf x (syn_cuni (.cv p)) p0629
    have p0631 :=
      @g_simpl (.classMem (.cv x) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
    have p0632 :=
      @g_sseld (.classMem (.cv u) (syn_chwcn P)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcn (syn_cun P Y)) (.cv x) p0555
    have p0633 :=
      @g_syl5 syntaxFormula0129
        (.classMem (.cv x) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv u) (syn_chwcn P)) (.classMem (.cv x) (syn_chwcn (syn_cun P Y)))
        p0631 p0632
    have p0634 :=
      @g_simpr (.classMem (.cv x) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
    have p0635 :=
      @g_sseld (.classMem (.cv u) (syn_chwcn P)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcn (syn_cun P Y)) (.cv y) p0555
    have p0636 :=
      @g_syl5 syntaxFormula0129
        (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv u) (syn_chwcn P)) (.classMem (.cv y) (syn_chwcn (syn_cun P Y)))
        p0634 p0635
    have p0637 :=
      @g_jcad (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0129
        (.classMem (.cv x) (syn_chwcn (syn_cun P Y)))
        (.classMem (.cv y) (syn_chwcn (syn_cun P Y))) p0633 p0636
    have p0638 :=
      @g_adantrd (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0129 syntaxFormula0130
        (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y)) p0637
    have p0639 := @g_hwcnraw x (syn_cun P Y)
    have p0640 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0129
        (.classMem (.cv x) (syn_chwcn (syn_cun P Y)))
        (.classMem (.cv x) (syn_chwcodes (syn_cun P Y))) p0633 p0639
    have p0641 := @g_hwcnraw y (syn_cun P Y)
    have p0642 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0129
        (.classMem (.cv y) (syn_chwcn (syn_cun P Y)))
        (.classMem (.cv y) (syn_chwcodes (syn_cun P Y))) p0636 p0641
    have p0643 :=
      @g_jcad (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0129
        (.classMem (.cv x) (syn_chwcodes (syn_cun P Y)))
        (.classMem (.cv y) (syn_chwcodes (syn_cun P Y))) p0640 p0642
    have p0644 :=
      @g_adantrd (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0129 syntaxFormula0131
        (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y)) p0643
    have p0645 :=
      @g_simpr syntaxFormula0129
        (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
    have p0646 := @g_hwnisohwisob y x (syn_cfv (syn_c2nd) (.cv u)) dv_cache_0007
    have p0647 :=
      @g_biimpi (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
        (syn_wa syntaxFormula0129
          (syn_wbr (.cv x) (syn_chwiso (syn_cfv (syn_c2nd) (.cv u))) (.cv y)))
        p0646
    have p0648 :=
      @g_simprd (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
        syntaxFormula0129
        (syn_wbr (.cv x) (syn_chwiso (syn_cfv (syn_c2nd) (.cv u))) (.cv y)) p0647
    have p0649 :=
      @g_syl syntaxFormula0132
        (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
        (syn_wbr (.cv x) (syn_chwiso (syn_cfv (syn_c2nd) (.cv u))) (.cv y)) p0645 p0648
    have p0650 :=
      @g_brhwisoany y x (syn_cfv (syn_c2nd) (.cv u)) h dv_cache_0051 dv_cache_0052
        dv_cache_0053
    have p0651 :=
      @g_sylib syntaxFormula0132
        (syn_wbr (.cv x) (syn_chwiso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
        (syn_wa (syn_wa (.classMem (.cv x) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
            (.classMem (.cv y) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))) syntaxFormula0134)
        p0649 p0650
    have p0652 :=
      @g_simprd syntaxFormula0132
        (syn_wa (.classMem (.cv x) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u))))
          (.classMem (.cv y) (syn_chwcodes (syn_cfv (syn_c2nd) (.cv u)))))
        syntaxFormula0134 p0651
    have p0653 := @g_pm3_2 syntaxFormula0131 syntaxFormula0134
    have p0654 :=
      @g_syl5 syntaxFormula0132 syntaxFormula0134 syntaxFormula0131 syntaxFormula0135
        p0652 p0653
    have p0655 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0132 syntaxFormula0131
        (.imp syntaxFormula0132 syntaxFormula0135) p0644 p0654
    have p0656 :=
      @g_pm2_43d (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0132 syntaxFormula0135
        p0655
    have p0657 :=
      @g_brhwisoany y x (syn_cun P Y) h dv_cache_0054 dv_cache_0052 dv_cache_0053
    have p0658 :=
      @g_syl6ibr (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0132 syntaxFormula0135
        (syn_wbr (.cv x) (syn_chwiso (syn_cun P Y)) (.cv y)) p0656 p0657
    have p0659 :=
      @g_jcad (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0132 syntaxFormula0130
        (syn_wbr (.cv x) (syn_chwiso (syn_cun P Y)) (.cv y)) p0638 p0658
    have p0660 := @g_hwnisohwisob y x (syn_cun P Y) dv_cache_0007
    have p0661 :=
      @g_syl6ibr (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0132
        (syn_wa syntaxFormula0130 (syn_wbr (.cv x) (syn_chwiso (syn_cun P Y)) (.cv y)))
        (syn_wbr (.cv x) (syn_chwniso (syn_cun P Y)) (.cv y)) p0659 p0660
    have p0662 :=
      @g_exp3a (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0129
        (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
        (syn_wbr (.cv x) (syn_chwniso (syn_cun P Y)) (.cv y)) p0661
    have p0663 :=
      @g_eleq1 (.cv x) (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
    have p0664 := @g_biid (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
    have p0665 :=
      @g_a1i
        (syn_wb (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
          (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classEq (.cv x) (syn_cuni (.cv p))) p0664
    have p0666 :=
      @g_anbi12d (.classEq (.cv x) (syn_cuni (.cv p)))
        (.classMem (.cv x) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) p0663 p0665
    have p0667 :=
      @g_breq1 (.cv x) (syn_cuni (.cv p)) (.cv y)
        (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))
    have p0668 := @g_breq1 (.cv x) (syn_cuni (.cv p)) (.cv y) (syn_chwniso (syn_cun P Y))
    have p0669 :=
      @g_imbi12d (.classEq (.cv x) (syn_cuni (.cv p)))
        (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
        (syn_wbr (.cv x) (syn_chwniso (syn_cun P Y)) (.cv y))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (.cv y)) p0667 p0668
    have p0670 :=
      @g_imbi12d (.classEq (.cv x) (syn_cuni (.cv p))) syntaxFormula0129 syntaxFormula0136
        (.imp (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
          (syn_wbr (.cv x) (syn_chwniso (syn_cun P Y)) (.cv y)))
        syntaxFormula0137 p0666 p0669
    have p0671 :=
      @g_syl5ibcom (.classMem (.cv u) (syn_chwcn P))
        (.imp syntaxFormula0129
          (.imp (syn_wbr (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
            (syn_wbr (.cv x) (syn_chwniso (syn_cun P Y)) (.cv y))))
        (.classEq (.cv x) (syn_cuni (.cv p))) syntaxFormula0138 p0662 p0670
    have p0672 :=
      @g_alrimiv (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0139 x dv_cache_0055 p0671
    have p0673 := @g_nfv syntaxFormula0138 x dv_cache_0056
    have p0674 :=
      @g_n_19_23 (.classEq (.cv x) (syn_cuni (.cv p))) syntaxFormula0138 x p0673
    have p0675 :=
      @g_sylib (.classMem (.cv u) (syn_chwcn P)) (.all x syntaxFormula0139)
        (.imp (syn_wex x (.classEq (.cv x) (syn_cuni (.cv p)))) syntaxFormula0138) p0672
        p0674
    have p0676 :=
      @g_syl5bi (.classMem (syn_cuni (.cv p)) (syn_cvv))
        (syn_wex x (.classEq (.cv x) (syn_cuni (.cv p))))
        (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0138 p0630 p0675
    have p0677 := @g_elex (syn_cuni (.cv p)) (syn_cvv)
    have p0678 :=
      @g_a1ii (.imp (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0140) syntaxFormula0141
        p0676 p0677
    have p0679 :=
      @g_biid (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
    have p0680 :=
      @g_a1i
        (syn_wb (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
          (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classEq (.cv y) (syn_cuni (.cv q))) p0679
    have p0681 :=
      @g_eleq1 (.cv y) (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
    have p0682 :=
      @g_anbi12d (.classEq (.cv y) (syn_cuni (.cv q)))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv y) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) p0680
        p0681
    have p0683 :=
      @g_breq2 (.cv y) (syn_cuni (.cv q)) (syn_cuni (.cv p))
        (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))
    have p0684 :=
      @g_breq2 (.cv y) (syn_cuni (.cv q)) (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y))
    have p0685 :=
      @g_imbi12d (.classEq (.cv y) (syn_cuni (.cv q)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv y))
        syntaxFormula0127 (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (.cv y))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q))) p0683
        p0684
    have p0686 :=
      @g_imbi12d (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0136 syntaxFormula0125
        syntaxFormula0137 syntaxFormula0142 p0682 p0685
    have p0687 :=
      @g_imbi2d (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0138 syntaxFormula0143
        (.classMem (syn_cuni (.cv p)) (syn_cvv)) p0686
    have p0688 :=
      @g_syl5ibcom (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0140
        (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0144 p0678 p0687
    have p0689 :=
      @g_alrimiv (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0145 y dv_cache_0057 p0688
    have p0690 := @g_nfcv y (syn_cuni (.cv p)) dv_cache_0058
    exact
      continuation p0364 p0370 p0374 p0395 p0400 p0403 p0406 p0415 p0417 p0419 p0420 p0421
        p0424 p0425 p0430 p0431 p0440 p0442 p0444 p0451 p0453 p0455 p0458 p0462 p0466
        p0469 p0478 p0480 p0481 p0489 p0494 p0503 p0534 p0541 p0548 p0553 p0555 p0557
        p0558 p0560 p0562 p0565 p0570 p0580 p0585 p0586 p0590 p0605 p0609 p0621 p0624
        p0626 p0628 p0630 p0639 p0641 p0653 p0657 p0660 p0668 p0677 p0679 p0684 p0689
        p0690

end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `ReplaySupport.CodeCover3`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_cfbhnqinjcodecoverddndv_stage3 (u : Var) (P : Class) (k : Var)
    (Y : Class) (p0001 : _) (p0006 : _) (p0011 : _) (p0023 : _) (p0082 : _) (p0370 : _)
    (p0395 : _) (p0419 : _) (p0421 : _) (p0424 : _) (p0425 : _) (p0430 : _) (p0431 : _)
    (p0440 : _) (p0444 : _) (p0458 : _) (p0469 : _) (p0481 : _) (p0494 : _) (p0555 : _)
    (p0557 : _) (p0565 : _) (p0585 : _) (p0590 : _) (p0605 : _) (p0609 : _) (p0626 : _)
    (p0628 : _) (p0677 : _) (p0689 : _) (p0690 : _) {Result : Type}
    (continuation : _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ →
        _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ →
        _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → Result) :=
  show Result from
    by
    let proofSupport : Finset Var :=
      ({ u } : Finset Var) ∪ P.fv ∪ ({ k } : Finset Var) ∪ Y.fv
    let y : Var := freshVar proofSupport 1
    let x : Var := freshVar proofSupport 2
    let a : Var := freshVar proofSupport 4
    let z : Var := freshVar proofSupport 5
    let p : Var := freshVar proofSupport 6
    let q : Var := freshVar proofSupport 7
    let h : Var := freshVar proofSupport 8
    let b : Var := freshVar proofSupport 9
    let t : Var := freshVar proofSupport 10
    have fresh_y : y ∉ proofSupport :=
      by
      change freshVar proofSupport 1 ∉ proofSupport
      exact freshVar_not_mem proofSupport 1
    have fresh_y_ne_u : y ≠ u := by
      intro h
      exact
        fresh_y
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_y_not_P : y ∉ P.fv := by
      intro h
      exact
        fresh_y
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_y_not_Y : y ∉ Y.fv := by
      intro h
      exact fresh_y (Finset.mem_union_right _ (h))
    have fresh_x : x ∉ proofSupport :=
      by
      change freshVar proofSupport 2 ∉ proofSupport
      exact freshVar_not_mem proofSupport 2
    have fresh_x_ne_u : x ≠ u := by
      intro h
      exact
        fresh_x
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_x_not_P : x ∉ P.fv := by
      intro h
      exact
        fresh_x
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_x_ne_k : x ≠ k := by
      intro h
      exact
        fresh_x
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_x_not_Y : x ∉ Y.fv := by
      intro h
      exact fresh_x (Finset.mem_union_right _ (h))
    have fresh_a : a ∉ proofSupport :=
      by
      change freshVar proofSupport 4 ∉ proofSupport
      exact freshVar_not_mem proofSupport 4
    have fresh_a_ne_u : a ≠ u := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_z : z ∉ proofSupport :=
      by
      change freshVar proofSupport 5 ∉ proofSupport
      exact freshVar_not_mem proofSupport 5
    have fresh_z_ne_u : z ≠ u := by
      intro h
      exact
        fresh_z
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_z_not_P : z ∉ P.fv := by
      intro h
      exact
        fresh_z
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_z_not_Y : z ∉ Y.fv := by
      intro h
      exact fresh_z (Finset.mem_union_right _ (h))
    have fresh_p : p ∉ proofSupport :=
      by
      change freshVar proofSupport 6 ∉ proofSupport
      exact freshVar_not_mem proofSupport 6
    have fresh_p_ne_u : p ≠ u := by
      intro h
      exact
        fresh_p
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_p_not_P : p ∉ P.fv := by
      intro h
      exact
        fresh_p
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_q : q ∉ proofSupport :=
      by
      change freshVar proofSupport 7 ∉ proofSupport
      exact freshVar_not_mem proofSupport 7
    have fresh_q_ne_u : q ≠ u := by
      intro h
      exact
        fresh_q
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_q_not_P : q ∉ P.fv := by
      intro h
      exact
        fresh_q
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_b : b ∉ proofSupport :=
      by
      change freshVar proofSupport 9 ∉ proofSupport
      exact freshVar_not_mem proofSupport 9
    have fresh_b_ne_u : b ≠ u := by
      intro h
      exact
        fresh_b
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_b_ne_k : b ≠ k := by
      intro h
      exact
        fresh_b
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_b_not_Y : b ∉ Y.fv := by
      intro h
      exact fresh_b (Finset.mem_union_right _ (h))
    have fresh_t : t ∉ proofSupport :=
      by
      change freshVar proofSupport 10 ∉ proofSupport
      exact freshVar_not_mem proofSupport 10
    have fresh_t_ne_u : t ≠ u := by
      intro h
      exact
        fresh_t
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_y_ne_x : y ≠ x :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 2
      exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
    have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
    have fresh_y_ne_a : y ≠ a :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
    have fresh_y_ne_z : y ≠ z :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
    have fresh_y_ne_p : y ≠ p :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
    have fresh_p_ne_y : p ≠ y := Ne.symm fresh_y_ne_p
    have fresh_y_ne_q : y ≠ q :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
    have fresh_q_ne_y : q ≠ y := Ne.symm fresh_y_ne_q
    have fresh_y_ne_t : y ≠ t :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 1) (j := 10) (by decide)
    have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
    have fresh_x_ne_a : x ≠ a :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
    have fresh_x_ne_z : x ≠ z :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
    have fresh_x_ne_b : x ≠ b :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 2) (j := 9) (by decide)
    have fresh_b_ne_x : b ≠ x := Ne.symm fresh_x_ne_b
    have fresh_x_ne_t : x ≠ t :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 2) (j := 10) (by decide)
    have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
    have fresh_a_ne_b : a ≠ b :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 4) (j := 9) (by decide)
    have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
    have fresh_a_ne_t : a ≠ t :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 4) (j := 10) (by decide)
    have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
    have fresh_z_ne_p : z ≠ p :=
      by
      change freshVar proofSupport 5 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
    have fresh_p_ne_z : p ≠ z := Ne.symm fresh_z_ne_p
    have fresh_z_ne_q : z ≠ q :=
      by
      change freshVar proofSupport 5 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
    have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
    have dv_cache_0007 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
    have dv_cache_0055 : x ∉ ((Wff.classMem (.cv u) (syn_chwcn P))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_P, or_false,
            not_false_eq_true])
    have dv_cache_0057 : y ∉ ((Wff.classMem (.cv u) (syn_chwcn P))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_u, fresh_y_not_P, or_false,
            not_false_eq_true])
    have dv_cache_0059 : y ∉ ((syn_cvv)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0060 :
      y ∉
        ((Wff.imp (syn_wa
              (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
              (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))) (.imp
              (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))
                (syn_cuni (.cv q))) (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y))
                (syn_cuni (.cv q)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_u, fresh_y_ne_q, fresh_y_not_P,
            fresh_y_not_Y, compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0061 : q ∉ ((Wff.classMem (.cv u) (syn_chwcn P))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_u, fresh_q_not_P, or_false,
            not_false_eq_true])
    have dv_cache_0062 : q ∉ ((Wff.classEq (.cv y) (.cv z))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_y, fresh_q_ne_z, or_false,
            not_false_eq_true])
    have dv_cache_0063 : p ∉ ((Wff.classMem (.cv u) (syn_chwcn P))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
            Finset.mem_singleton, fresh_p_ne_u, fresh_p_not_P, or_false,
            not_false_eq_true])
    have dv_cache_0064 : p ∉ ((Wff.classEq (.cv y) (.cv z))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_p_ne_y, fresh_p_ne_z, or_false,
            not_false_eq_true])
    have dv_cache_0065 : z ∉ ((Wff.classMem (.cv u) (syn_chwcn P))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_P, or_false,
            not_false_eq_true])
    have dv_cache_0066 :
      x ∉
        ((syn_ccom (syn_chnqmap1 (syn_cun P Y))
            (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_x_not_P, fresh_x_not_Y, fresh_x_ne_u,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0067 :
      y ∉
        ((syn_ccom (syn_chnqmap1 (syn_cun P Y))
            (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_y_not_P, fresh_y_not_Y, fresh_y_ne_u,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0068 :
      z ∉
        ((syn_ccom (syn_chnqmap1 (syn_cun P Y))
            (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_z_not_P, fresh_z_not_Y, fresh_z_ne_u,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0069 : x ≠ z := by exact (show x ≠ z from (by exact fresh_x_ne_z))
    have dv_cache_0070 : y ≠ z := by exact (show y ≠ z from (by exact fresh_y_ne_z))
    have dv_cache_0071 : a ∉ ((Class.cv u)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_u, not_false_eq_true])
    have dv_cache_0072 :
      x ∉ ((syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_ne_a, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0073 :
      x ∉
        ((syn_cop (syn_csn (.cv a)) (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))
              (syn_csn (.cv a))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_u, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0074 :
      x ∉
        ((syn_csymdif (syn_cins2 (syn_csset)) (syn_cins3 (syn_ccom (syn_csset)
                (syn_ccnv (syn_csi (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0075 : b ∉ ((syn_csn (.cv x))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_x,
            not_false_eq_true])
    have dv_cache_0076 : b ∉ ((syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_u, fresh_b_not_Y, fresh_b_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0077 :
      b ∉
        ((syn_wb (.classMem (syn_cop (syn_csn (.cv x)) (syn_cop (syn_csn (.cv a))
                  (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))))
              (syn_cins3 (syn_ccom (syn_csset)
                  (syn_ccnv (syn_csi (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))))))
            (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (.cv a))) (syn_ccom (syn_csset)
                (syn_ccnv (syn_csi (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a, fresh_b_ne_u,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0078 : y ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_y_ne_x, not_false_eq_true])
    have dv_cache_0079 : y ∉ ((Class.cv t)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_y_ne_t, not_false_eq_true])
    have dv_cache_0080 : y ∉ ((syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0081 : y ∉ ((syn_wbr (.cv t) (syn_csset) (syn_csn (.cv a)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_a, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0082 : t ∉ ((syn_csn (.cv y))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
            not_false_eq_true])
    have dv_cache_0083 :
      t ∉
        ((syn_wa (.classMem (.cv y) (syn_csn (.cv a)))
            (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_a, fresh_t_ne_x, fresh_t_ne_u,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0084 : t ∉ ((syn_csn (.cv x))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
            not_false_eq_true])
    have dv_cache_0085 : t ∉ ((syn_csn (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_a,
            not_false_eq_true])
    have dv_cache_0086 : t ∉ ((syn_csset)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0087 :
      t ∉ ((syn_ccnv (syn_csi (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_t_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0088 : y ∉ ((syn_csn (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_a,
            not_false_eq_true])
    have dv_cache_0089 : x ∉ ((syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_not_Y, fresh_x_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0090 :
      y ∉ ((syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_u, fresh_y_ne_x, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0091 : x ∉ ((syn_cvv)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0092 :
      x ∉ ((syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0093 :
      y ∉ ((syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    let syntaxClass0090 : Class :=
      (syn_ccom (syn_chnqmap1 (syn_cun P Y))
        (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0092 : Wff :=
      (syn_wbr (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0093 : Wff := (syn_wbr (.cv x) syntaxClass0090 (.cv y))
    let syntaxFormula0094 : Wff := (syn_wbr (.cv x) syntaxClass0090 (.cv z))
    let syntaxFormula0095 : Wff := (syn_wa syntaxFormula0093 syntaxFormula0094)
    let syntaxFormula0096 : Wff :=
      (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) (.cv p))
    let syntaxFormula0097 : Wff :=
      (syn_wa syntaxFormula0096 (syn_wbr (.cv p) (syn_chnqmap1 (syn_cun P Y)) (.cv y)))
    let syntaxFormula0098 : Wff := (syn_wex p syntaxFormula0097)
    let syntaxFormula0099 : Wff :=
      (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) (.cv q))
    let syntaxFormula0100 : Wff :=
      (syn_wa syntaxFormula0099 (syn_wbr (.cv q) (syn_chnqmap1 (syn_cun P Y)) (.cv z)))
    let syntaxFormula0101 : Wff := (syn_wex q syntaxFormula0100)
    let syntaxFormula0102 : Wff := (syn_wa syntaxFormula0095 syntaxFormula0097)
    let syntaxFormula0103 : Wff := (syn_wa syntaxFormula0102 syntaxFormula0100)
    let syntaxFormula0106 : Wff :=
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))))
    let syntaxFormula0114 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0117 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv p))
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (.cv q)))
    let syntaxFormula0121 : Wff := (syn_wa syntaxFormula0106 syntaxFormula0117)
    let syntaxFormula0125 : Wff :=
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0127 : Wff :=
      (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_cuni (.cv q)))
    let syntaxFormula0141 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv)))
    let syntaxFormula0142 : Wff :=
      (.imp syntaxFormula0127
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q))))
    let syntaxFormula0143 : Wff := (.imp syntaxFormula0125 syntaxFormula0142)
    let syntaxFormula0144 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0143)
    let syntaxFormula0145 : Wff :=
      (.imp (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0144)
    let syntaxFormula0146 : Wff :=
      (.imp (.classMem (syn_cuni (.cv q)) (syn_cvv)) syntaxFormula0144)
    let syntaxFormula0147 : Wff :=
      (.imp (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0146)
    let syntaxFormula0148 : Wff :=
      (.imp (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classMem (syn_cuni (.cv q)) (syn_cvv)))
    let syntaxFormula0149 : Wff :=
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_cvv)) (.classMem (syn_cuni (.cv q)) (syn_cvv)))
    let syntaxFormula0150 : Wff :=
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cun P Y)))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cun P Y))))
    let syntaxFormula0151 : Wff :=
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0152 : Wff :=
      (syn_wb syntaxFormula0151
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q))))
    let syntaxFormula0153 : Wff :=
      (syn_wb (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q)))
        syntaxFormula0151)
    let syntaxFormula0154 : Wff :=
      (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q)))
        syntaxFormula0151)
    let syntaxFormula0155 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0156 : Wff := (syn_wb syntaxFormula0114 syntaxFormula0155)
    let syntaxFormula0157 : Wff := (.imp syntaxFormula0114 syntaxFormula0155)
    let syntaxFormula0158 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (syn_csn (syn_cuni (.cv q))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0159 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))
        (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (syn_csn (syn_cuni (.cv q)))))
    let syntaxFormula0160 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0161 : Wff := (syn_wb syntaxFormula0159 syntaxFormula0160)
    let syntaxFormula0162 : Wff := (.imp syntaxFormula0159 syntaxFormula0160)
    let syntaxFormula0163 : Wff :=
      (.classEq (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cun P Y)))
        (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q)))
    let syntaxFormula0164 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p))
        (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q)))
    let syntaxFormula0165 : Wff := (syn_wb syntaxFormula0155 syntaxFormula0164)
    let syntaxFormula0166 : Wff := (.imp syntaxFormula0155 syntaxFormula0164)
    let syntaxFormula0167 : Wff := (.imp syntaxFormula0117 syntaxFormula0164)
    let syntaxFormula0168 : Wff :=
      (syn_wb (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p)))
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))))
    let syntaxFormula0169 : Wff :=
      (.imp (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p)))
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))))
    let syntaxFormula0170 : Wff := (.imp syntaxFormula0100 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0171 : Wff := (.all q syntaxFormula0102)
    let syntaxFormula0172 : Wff := (.all q syntaxFormula0170)
    let syntaxFormula0173 : Wff :=
      (.imp syntaxFormula0101 (syn_wex q (.classEq (.cv y) (.cv z))))
    let syntaxFormula0174 : Wff := (.imp syntaxFormula0097 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0175 : Wff := (.all p syntaxFormula0095)
    let syntaxFormula0176 : Wff := (.all p syntaxFormula0174)
    let syntaxFormula0177 : Wff :=
      (.imp syntaxFormula0098 (syn_wex p (.classEq (.cv y) (.cv z))))
    let syntaxFormula0178 : Wff := (.imp syntaxFormula0095 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0179 : Wff := (.all z syntaxFormula0178)
    let syntaxFormula0180 : Wff := (.all y syntaxFormula0179)
    let syntaxFormula0181 : Wff := (.all x syntaxFormula0180)
    let syntaxFormula0182 : Wff :=
      (syn_wss (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cpw1 (syn_chwcn (syn_cun P Y))))
    let syntaxFormula0183 : Wff :=
      (syn_wss (syn_crn (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cdm (syn_chnqmap1 (syn_cun P Y))))
    let syntaxClass0184 : Class := (syn_cdm syntaxClass0090)
    let syntaxFormula0185 : Wff :=
      (.classEq syntaxClass0184
        (syn_cdm (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))))
    let syntaxFormula0186 : Wff :=
      (.classEq (syn_cdm (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y)))
        (syn_chnord (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0187 : Wff :=
      (syn_wfn (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))
        (syn_chnord (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0188 : Wff :=
      (.classMem (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_chnord (syn_cfv (syn_c2nd) (.cv u))))
    let syntaxFormula0189 : Wff := (syn_wa syntaxFormula0187 syntaxFormula0188)
    let syntaxClass0190 : Class :=
      (syn_cfv (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))
        (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0191 : Wff :=
      (.classEq syntaxClass0190 (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0192 : Wff := (syn_wb syntaxFormula0191 syntaxFormula0092)
    let syntaxFormula0193 : Wff :=
      (.classEq (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
        syntaxClass0190)
    let syntaxClass0194 : Class :=
      (syn_cres (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0195 : Wff :=
      (.classMem (syn_csn (.cv a)) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxClass0196 : Class :=
      (syn_cfv (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_csn (.cv a)))
    let syntaxClass0197 : Class :=
      (syn_cop (syn_csn (.cv a))
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
    let syntaxClass0198 : Class :=
      (syn_ccom (syn_csset) (syn_ccnv (syn_csi (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))))
    let syntaxClass0199 : Class := (syn_cins3 syntaxClass0198)
    let syntaxClass0200 : Class := (syn_csymdif (syn_cins2 (syn_csset)) syntaxClass0199)
    let syntaxClass0201 : Class := (syn_cop (syn_csn (.cv x)) syntaxClass0197)
    let syntaxFormula0202 : Wff :=
      (syn_wbr (syn_csn (.cv x)) (syn_csset)
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
    let syntaxFormula0203 : Wff :=
      (.classMem (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))
        (syn_cvv))
    let syntaxFormula0204 : Wff :=
      (.classMem (.cv x)
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
    let syntaxFormula0205 : Wff := (.classMem syntaxClass0201 (syn_cins2 (syn_csset)))
    let syntaxClass0206 : Class :=
      (syn_cop (.cv b) (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
    let syntaxFormula0207 : Wff := (.classMem syntaxClass0206 (syn_cvv))
    let syntaxFormula0208 : Wff :=
      (.classMem (syn_cop (.cv b) (syn_csn (.cv a))) syntaxClass0198)
    let syntaxClass0209 : Class := (syn_cop (.cv b) syntaxClass0197)
    let syntaxFormula0210 : Wff := (.classMem syntaxClass0209 syntaxClass0199)
    let syntaxFormula0211 : Wff := (syn_wa syntaxFormula0208 syntaxFormula0207)
    let syntaxFormula0212 : Wff := (.classMem syntaxClass0201 syntaxClass0199)
    let syntaxFormula0213 : Wff :=
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (.cv a))) syntaxClass0198)
    let syntaxFormula0214 : Wff := (syn_wb syntaxFormula0212 syntaxFormula0213)
    let syntaxFormula0215 : Wff :=
      (.imp (.classEq (.cv b) (syn_csn (.cv x))) syntaxFormula0214)
    let syntaxFormula0216 : Wff := (.classMem syntaxClass0197 (syn_cvv))
    let syntaxFormula0217 : Wff :=
      (syn_wbr (syn_csn (.cv x))
        (syn_ccnv (syn_csi (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))) (.cv t))
    let syntaxFormula0218 : Wff :=
      (syn_wa (.classEq (.cv t) (syn_csn (.cv y)))
        (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x)))
    let syntaxFormula0219 : Wff := (syn_wex y syntaxFormula0218)
    let syntaxFormula0220 : Wff :=
      (syn_wa syntaxFormula0217 (syn_wbr (.cv t) (syn_csset) (syn_csn (.cv a))))
    let syntaxFormula0221 : Wff :=
      (syn_wa syntaxFormula0218 (syn_wbr (.cv t) (syn_csset) (syn_csn (.cv a))))
    let syntaxFormula0222 : Wff := (syn_wex y syntaxFormula0221)
    let syntaxFormula0223 : Wff :=
      (syn_wa (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x))
        (syn_wbr (.cv t) (syn_csset) (syn_csn (.cv a))))
    let syntaxFormula0224 : Wff :=
      (syn_wa (.classEq (.cv t) (syn_csn (.cv y))) syntaxFormula0223)
    let syntaxFormula0225 : Wff :=
      (syn_wa (.classMem (.cv y) (syn_csn (.cv a)))
        (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x)))
    let syntaxFormula0226 : Wff := (syn_wex t syntaxFormula0221)
    let syntaxFormula0227 : Wff := (syn_wex t syntaxFormula0220)
    let syntaxFormula0228 : Wff := (syn_wb syntaxFormula0205 syntaxFormula0212)
    let syntaxFormula0229 : Wff := (syn_wb syntaxFormula0204 syntaxFormula0204)
    let syntaxFormula0230 : Wff := (.classMem syntaxClass0201 syntaxClass0200)
    let syntaxFormula0231 : Wff := (.neg syntaxFormula0229)
    let syntaxFormula0232 : Wff := (syn_wex x syntaxFormula0230)
    let syntaxFormula0233 : Wff := (.all x syntaxFormula0229)
    let syntaxFormula0234 : Wff := (.neg syntaxFormula0233)
    let syntaxClass0235 : Class := (syn_cima syntaxClass0200 (syn_c1c))
    let syntaxFormula0236 : Wff := (.classMem syntaxClass0197 syntaxClass0235)
    let syntaxClass0237 : Class := (syn_ccompl syntaxClass0235)
    let syntaxFormula0238 : Wff :=
      (syn_wbr (syn_csn (.cv a)) syntaxClass0237
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
    let syntaxFormula0239 : Wff := (.classMem syntaxClass0197 syntaxClass0237)
    let syntaxFormula0240 : Wff := (.neg syntaxFormula0236)
    let syntaxFormula0241 : Wff :=
      (syn_wbr (syn_csn (.cv a)) (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
    let syntaxFormula0242 : Wff :=
      (syn_wbr (.cv x) (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (.cv y))
    let syntaxFormula0243 : Wff := (syn_weu y syntaxFormula0242)
    let syntaxFormula0244 : Wff :=
      (syn_wa (syn_wfn (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv))
        (.classMem (syn_csn (.cv a)) (syn_cvv)))
    have p0691 := @g_nfel1 y (syn_cuni (.cv p)) (syn_cvv) dv_cache_0059 p0690
    have p0692 := @g_nfv syntaxFormula0143 y dv_cache_0060
    have p0693 :=
      @g_nfim (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0143 y p0691 p0692
    have p0694 :=
      @g_n_19_23 (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0144 y p0693
    have p0695 :=
      @g_sylib (.classMem (.cv u) (syn_chwcn P)) (.all y syntaxFormula0145)
        (.imp (syn_wex y (.classEq (.cv y) (syn_cuni (.cv q)))) syntaxFormula0144) p0689
        p0694
    have p0696 :=
      @g_syl5bi (.classMem (syn_cuni (.cv q)) (syn_cvv))
        (syn_wex y (.classEq (.cv y) (syn_cuni (.cv q))))
        (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0144 p0628 p0695
    have p0697 := @g_elex (syn_cuni (.cv q)) (syn_cvv)
    have p0698 := @g_a1ii syntaxFormula0147 syntaxFormula0148 p0696 p0697
    have p0700 := @g_a1ii syntaxFormula0147 syntaxFormula0141 p0698 p0677
    have p0701 :=
      @g_com23 (.classMem (.cv u) (syn_chwcn P)) (.classMem (syn_cuni (.cv q)) (syn_cvv))
        (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0143 p0700
    have p0702 :=
      @g_imp3a (.classMem (.cv u) (syn_chwcn P)) (.classMem (syn_cuni (.cv p)) (syn_cvv))
        (.classMem (syn_cuni (.cv q)) (syn_cvv)) syntaxFormula0143 p0701
    have p0703 :=
      @g_syl5 syntaxFormula0125 syntaxFormula0149 (.classMem (.cv u) (syn_chwcn P))
        syntaxFormula0143 p0626 p0702
    have p0704 :=
      @g_pm2_43d (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0125 syntaxFormula0142
        p0703
    have p0705 :=
      @g_syl5 syntaxFormula0121 syntaxFormula0125 (.classMem (.cv u) (syn_chwcn P))
        syntaxFormula0142 p0605 p0704
    have p0706 :=
      @g_mpdi (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0127
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q))) p0609
        p0705
    have p0711 :=
      @g_sseld (.classMem (.cv u) (syn_chwcn P)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
        (syn_chwcn (syn_cun P Y)) (syn_cuni (.cv q)) p0555
    have p0712 :=
      @g_syl5 syntaxFormula0106
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (.classMem (.cv u) (syn_chwcn P))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cun P Y))) p0590 p0711
    have p0713 :=
      @g_jcad (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cun P Y)))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cun P Y))) p0557 p0712
    have p0714 :=
      @g_adantrd (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106 syntaxFormula0150
        syntaxFormula0117 p0713
    have p0715 :=
      @g_hwnisoclasseqbcl (syn_cun P Y) (syn_cuni (.cv p)) (syn_cuni (.cv q)) p0001
    have p0716 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0150
        syntaxFormula0152 p0714 p0715
    have p0717 :=
      @g_bicom syntaxFormula0151
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q)))
    have p0718 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0152
        syntaxFormula0153 p0716 p0717
    have p0719 :=
      @g_bi1 (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q)))
        syntaxFormula0151
    have p0720 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0153
        syntaxFormula0154 p0718 p0719
    have p0721 :=
      @g_id (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q)))
    have p0722 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P)) (.imp syntaxFormula0121 syntaxFormula0154))
        (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q)))
          (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q))))
        p0720 p0721
    have p0723 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q)))
        syntaxFormula0151 p0706 p0722
    have p0724 :=
      @g_eqeq2 (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cun P Y)))
        (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p))
    have p0725 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0151
        syntaxFormula0156 p0723 p0724
    have p0726 := @g_bi1 syntaxFormula0114 syntaxFormula0155
    have p0727 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0156
        syntaxFormula0157 p0725 p0726
    have p0728 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0114
        syntaxFormula0155 p0565 p0727
    have p0733 :=
      @g_fveq2d syntaxFormula0106 (.cv q) (syn_csn (syn_cuni (.cv q)))
        (syn_chnqmap1 (syn_cun P Y)) p0585
    have p0734 := @g_hnqmap1valcl (syn_cun P Y) (syn_cuni (.cv q)) p0001
    have p0735 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cun P Y))) syntaxFormula0158 p0712
        p0734
    have p0736 :=
      @g_eqeq2 (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (syn_csn (syn_cuni (.cv q))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cun P Y)))
        (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))
    have p0737 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106 syntaxFormula0158
        syntaxFormula0161 p0735 p0736
    have p0738 := @g_bi1 syntaxFormula0159 syntaxFormula0160
    have p0739 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106 syntaxFormula0161
        syntaxFormula0162 p0737 p0738
    have p0740 :=
      @g_mpdi (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106 syntaxFormula0159
        syntaxFormula0160 p0733 p0739
    have p0741 :=
      @g_adantrd (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106 syntaxFormula0160
        syntaxFormula0117 p0740
    have p0742 :=
      @g_eqcom (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cun P Y)))
    have p0743 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0160
        syntaxFormula0163 p0741 p0742
    have p0744 :=
      @g_eqeq2 (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_cun P Y)))
        (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))
        (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p))
    have p0745 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0163
        syntaxFormula0165 p0743 p0744
    have p0746 := @g_bi1 syntaxFormula0155 syntaxFormula0164
    have p0747 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0165
        syntaxFormula0166 p0745 p0746
    have p0748 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0121 syntaxFormula0155
        syntaxFormula0164 p0728 p0747
    have p0749 :=
      @g_exp3a (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0106 syntaxFormula0117
        syntaxFormula0164 p0748
    have p0750 :=
      @g_syl5 syntaxFormula0103 syntaxFormula0106 (.classMem (.cv u) (syn_chwcn P))
        syntaxFormula0167 p0494 p0749
    have p0751 :=
      @g_mpdi (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0103 syntaxFormula0117
        syntaxFormula0164 p0469 p0750
    have p0752 :=
      @g_eqeq2 (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p))
        (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q)) (.cv y)
    have p0753 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0103 syntaxFormula0164
        syntaxFormula0168 p0751 p0752
    have p0754 :=
      @g_bi1 (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p)))
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q)))
    have p0755 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0103 syntaxFormula0168
        syntaxFormula0169 p0753 p0754
    have p0756 :=
      @g_mpdi (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0103
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p)))
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))) p0444 p0755
    have p0758 :=
      @g_simpr syntaxFormula0099 (syn_wbr (.cv q) (syn_chnqmap1 (syn_cun P Y)) (.cv z))
    have p0759 :=
      @g_syl syntaxFormula0103 syntaxFormula0100
        (syn_wbr (.cv q) (syn_chnqmap1 (syn_cun P Y)) (.cv z)) p0458 p0758
    have p0763 := @g_funbrfv (.cv q) (.cv z) (syn_chnqmap1 (syn_cun P Y))
    have p0764 := Nominal.mp p0440 p0763
    have p0765 :=
      @g_syl syntaxFormula0103 (syn_wbr (.cv q) (syn_chnqmap1 (syn_cun P Y)) (.cv z))
        (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q)) (.cv z)) p0759 p0764
    have p0766 :=
      @g_eqeq2d syntaxFormula0103 (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q)) (.cv z)
        (.cv y) p0765
    have p0767 :=
      @g_mpbidi syntaxFormula0103
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q)))
        (.classEq (.cv y) (.cv z)) (.classMem (.cv u) (syn_chwcn P)) p0756 p0766
    have p0768 :=
      @g_exp3a (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0102 syntaxFormula0100
        (.classEq (.cv y) (.cv z)) p0767
    have p0769 :=
      @g_alimdv (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0102 syntaxFormula0170 q
        dv_cache_0061 p0768
    have p0770 :=
      @g_syl5 syntaxFormula0102 syntaxFormula0171 (.classMem (.cv u) (syn_chwcn P))
        syntaxFormula0172 p0431 p0769
    have p0771 := @g_exim syntaxFormula0100 (.classEq (.cv y) (.cv z)) q
    have p0772 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0102 syntaxFormula0172
        syntaxFormula0173 p0770 p0771
    have p0773 := @g_ax17e (.classEq (.cv y) (.cv z)) q dv_cache_0062
    have p0774 :=
      @g_syl8 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0102 syntaxFormula0101
        (syn_wex q (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z)) p0772 p0773
    have p0775 :=
      @g_mpdi (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0102 syntaxFormula0101
        (.classEq (.cv y) (.cv z)) p0430 p0774
    have p0776 :=
      @g_exp3a (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0095 syntaxFormula0097
        (.classEq (.cv y) (.cv z)) p0775
    have p0777 :=
      @g_alimdv (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0095 syntaxFormula0174 p
        dv_cache_0063 p0776
    have p0778 :=
      @g_syl5 syntaxFormula0095 syntaxFormula0175 (.classMem (.cv u) (syn_chwcn P))
        syntaxFormula0176 p0425 p0777
    have p0779 := @g_exim syntaxFormula0097 (.classEq (.cv y) (.cv z)) p
    have p0780 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0095 syntaxFormula0176
        syntaxFormula0177 p0778 p0779
    have p0781 := @g_ax17e (.classEq (.cv y) (.cv z)) p dv_cache_0064
    have p0782 :=
      @g_syl8 (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0095 syntaxFormula0098
        (syn_wex p (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z)) p0780 p0781
    have p0783 :=
      @g_mpdi (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0095 syntaxFormula0098
        (.classEq (.cv y) (.cv z)) p0424 p0782
    have p0784 :=
      @g_alrimiv (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0178 z dv_cache_0065 p0783
    have p0785 :=
      @g_alrimiv (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0179 y dv_cache_0057 p0784
    have p0786 :=
      @g_alrimiv (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0180 x dv_cache_0055 p0785
    have p0787 :=
      @g_dffun2 x y z syntaxClass0090 dv_cache_0066 dv_cache_0067 dv_cache_0068
        dv_cache_0007 dv_cache_0069 dv_cache_0070
    have p0788_e01_recanon :
      Nominal.NPrf (syn_wb (syn_wfun syntaxClass0090) syntaxFormula0181) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_wb, syn_wfun, syn_wss, syn_cin, syn_ccompl, syn_cnin, syn_wnan,
            syn_wa, syn_ccom, syn_copab, syn_wex, syn_ccnv, syn_cid]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq]
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0787
    have p0788 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0181
        (syn_wfun syntaxClass0090) p0786 p0788_e01_recanon
    have p0790 :=
      @g_funeq (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y)) syntaxClass0090
    have p0791 := Nominal.mp p0419 p0790
    have p0792 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P)) (syn_wfun syntaxClass0090)
        (syn_wfun (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))) p0788 p0791
    have p0794 :=
      @g_dmeqi (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y)) syntaxClass0090
        p0419
    have p0795 :=
      @g_pw1ss (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcn (syn_cun P Y))
    have p0796 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P))
        (syn_wss (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))) (syn_chwcn (syn_cun P Y)))
        syntaxFormula0182 p0555 p0795
    have p0797 :=
      (Nominal.classEqRefl (syn_cdm (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))))
    have p0798 :=
      @g_eqcomi (syn_cdm (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))
        (syn_crn (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))) p0797
    have p0802 :=
      @g_eqtri (syn_crn (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cdm (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) p0798 p0481
    have p0804 :=
      @g_fndm (syn_cpw1 (syn_chwcn (syn_cun P Y))) (syn_chnqmap1 (syn_cun P Y))
    have p0805 := Nominal.mp p0370 p0804
    have p0806 :=
      @g_n_3sstr4g (.classMem (.cv u) (syn_chwcn P))
        (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cpw1 (syn_chwcn (syn_cun P Y)))
        (syn_crn (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_cdm (syn_chnqmap1 (syn_cun P Y))) p0796 p0802 p0805
    have p0807 :=
      @g_dmcosseq (syn_chnqmap1 (syn_cun P Y))
        (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))
    have p0808 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0183 syntaxFormula0185 p0806
        p0807
    have p0809 := @g_dfrn4 (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
    have p0810 :=
      @g_syl6eqr (.classMem (.cv u) (syn_chwcn P)) syntaxClass0184
        (syn_cdm (syn_ccnv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))))
        (syn_crn (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))) p0808 p0809
    have p0811 := @g_hnqmap1rn (syn_cfv (syn_c2nd) (.cv u)) p0023
    have p0812 :=
      @g_syl6eq (.classMem (.cv u) (syn_chwcn P)) syntaxClass0184
        (syn_crn (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))
        (syn_chnord (syn_cfv (syn_c2nd) (.cv u))) p0810 p0811
    have p0813 :=
      @g_syl5eq (.classMem (.cv u) (syn_chwcn P))
        (syn_cdm (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))) syntaxClass0184
        (syn_chnord (syn_cfv (syn_c2nd) (.cv u))) p0794 p0812
    have p0814 :=
      @g_jca (.classMem (.cv u) (syn_chwcn P))
        (syn_wfun (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y)))
        syntaxFormula0186 p0792 p0813
    have p0815 := (Nominal.biimpRefl syntaxFormula0187)
    have p0816 :=
      @g_sylibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wa (syn_wfun (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y)))
          syntaxFormula0186)
        syntaxFormula0187 p0814 p0815
    have p0817 := @g_hwnisoclasselhnordcl (syn_cfv (syn_c2nd) (.cv u)) (.cv u) p0023
    have p0818 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P))
        (.classMem (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) syntaxFormula0188
        p0011 p0817
    have p0819 :=
      @g_jca (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0187 syntaxFormula0188 p0816
        p0818
    have p0820 :=
      @g_fnbrfvb (syn_chnord (syn_cfv (syn_c2nd) (.cv u)))
        (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y)))
        (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))
    have p0821 :=
      @g_syl (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0189 syntaxFormula0192 p0819
        p0820
    have p0822 :=
      @g_mpbird (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0191 syntaxFormula0092
        p0421 p0821
    have p0823 :=
      @g_eqtr4d (.classMem (.cv u) (syn_chwcn P))
        (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
        (syn_cec (.cv u) (syn_chwniso (syn_cun P Y))) syntaxClass0190 p0395 p0822
    have p0824 :=
      @g_a1d (.classMem (.cv u) (syn_chwcn P)) syntaxFormula0193
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) p0823
    have p0825 := @g_elex (.cv u) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
    have p0826 := @g_nfcv a (.cv u) dv_cache_0071
    have p0827 := @g_issetf a (.cv u) p0826
    have p0828 := (Nominal.classEqRefl (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))))
    have p0829 :=
      @g_fveq1i (syn_csn (.cv a)) (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u)))
        syntaxClass0194 p0828
    have p0830 := @g_snelpw1 (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))
    have p0831 :=
      @g_biimpri syntaxFormula0195
        (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u)))) p0830
    have p0832 :=
      @g_fvres (syn_csn (.cv a)) (syn_cpw1 (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
    have p0833 :=
      @g_syl (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        syntaxFormula0195
        (.classEq (syn_cfv syntaxClass0194 (syn_csn (.cv a))) syntaxClass0196) p0831 p0832
    have p0834 :=
      @g_syl5eq (.classMem (.cv a) (syn_chwcn (syn_cfv (syn_c2nd) (.cv u))))
        (syn_cfv (syn_chnqmap1 (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))
        (syn_cfv syntaxClass0194 (syn_csn (.cv a))) syntaxClass0196 p0829 p0833
    have p0835 :=
      @g_eqid (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))
    have p0836 :=
      @g_dfcleq x (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))
        dv_cache_0072 dv_cache_0072
    have p0837 := @g_elima1c x syntaxClass0197 syntaxClass0200 dv_cache_0073 dv_cache_0074
    have p0838 := @g_elsymdif syntaxClass0201 (syn_cins2 (syn_csset)) syntaxClass0199
    have p0839 := @g_snex (.cv a)
    have p0840 :=
      @g_otelins2 (syn_csn (.cv x)) (syn_csn (.cv a))
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))
        (syn_csset) p0839
    have p0841 := (Nominal.biimpRefl syntaxFormula0202)
    have p0842 := @g_snex (.cv x)
    have p0843 := @g_f1odm (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)) (.cv k)
    have p0844 :=
      @g_syl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wf1o (.cv k) (syn_cfv (syn_c2nd) (.cv u)) (syn_crn (.cv k)))
        (.classEq (syn_cdm (.cv k)) (syn_cfv (syn_c2nd) (.cv u))) p0006 p0843
    have p0845 := @g_dmex (.cv k) p0082
    have p0846 :=
      @g_syl6eqelr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_cfv (syn_c2nd) (.cv u)) (syn_cdm (.cv k)) (syn_cvv) p0844 p0845
    have p0847 := @g_hwnisoexg (syn_cfv (syn_c2nd) (.cv u))
    have p0848 :=
      @g_syl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cfv (syn_c2nd) (.cv u)) (syn_cvv))
        (.classMem (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_cvv)) p0846 p0847
    have p0849 :=
      @g_imaexg (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)) (syn_cvv)
        (syn_cvv)
    have p0850 :=
      @g_sylancl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_cvv))
        (.classMem (syn_csn (.cv a)) (syn_cvv)) syntaxFormula0203 p0848 p0839 p0849
    have p0851 :=
      @g_brssetg (syn_csn (.cv x))
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))) (syn_cvv)
        (syn_cvv)
    have p0852 :=
      @g_sylancr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_csn (.cv x)) (syn_cvv)) syntaxFormula0203
        (syn_wb syntaxFormula0202 (syn_wss (syn_csn (.cv x))
            (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))))
        p0842 p0850 p0851
    have p0853 := @g_vex x
    have p0854 :=
      @g_snss (.cv x)
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))) p0853
    have p0855 :=
      @g_syl6bbr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0202
        (syn_wss (syn_csn (.cv x))
          (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
        syntaxFormula0204 p0852 p0854
    have p0856 :=
      @g_syl5bbr
        (.classMem (syn_cop (syn_csn (.cv x))
            (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
          (syn_csset))
        syntaxFormula0202 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        syntaxFormula0204 p0841 p0855
    have p0857 :=
      @g_syl5bb syntaxFormula0205
        (.classMem (syn_cop (syn_csn (.cv x))
            (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
          (syn_csset))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0204 p0840 p0856
    have p0858 := @g_nfcv b (syn_csn (.cv x)) dv_cache_0075
    have p0859 := @g_issetf b (syn_csn (.cv x)) p0858
    have p0860 := @g_vex b
    have p0861 :=
      @g_opexg (.cv b)
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))) (syn_cvv)
        (syn_cvv)
    have p0862 :=
      @g_sylancr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv b) (syn_cvv)) syntaxFormula0203 syntaxFormula0207 p0860 p0850
        p0861
    have p0863 :=
      @g_biantrud (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0207
        syntaxFormula0208 p0862
    have p0864 := (Nominal.classEqRefl syntaxClass0199)
    have p0865 :=
      @g_eleq2i syntaxClass0199 (syn_ctxp syntaxClass0198 (syn_cvv)) syntaxClass0209 p0864
    have p0866 :=
      @g_oteltxp (.cv b) (syn_csn (.cv a))
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))
        syntaxClass0198 (syn_cvv)
    have p0867 :=
      @g_bitri syntaxFormula0210
        (.classMem syntaxClass0209 (syn_ctxp syntaxClass0198 (syn_cvv))) syntaxFormula0211
        p0865 p0866
    have p0868 :=
      @g_syl6rbbr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0208
        syntaxFormula0211 syntaxFormula0210 p0863 p0867
    have p0869 := @g_opeq1 (.cv b) (syn_csn (.cv x)) syntaxClass0197
    have p0870 :=
      @g_eleq1d (.classEq (.cv b) (syn_csn (.cv x))) syntaxClass0209 syntaxClass0201
        syntaxClass0199 p0869
    have p0871 := @g_opeq1 (.cv b) (syn_csn (.cv x)) (syn_csn (.cv a))
    have p0872 :=
      @g_eleq1d (.classEq (.cv b) (syn_csn (.cv x))) (syn_cop (.cv b) (syn_csn (.cv a)))
        (syn_cop (syn_csn (.cv x)) (syn_csn (.cv a))) syntaxClass0198 p0871
    have p0873 :=
      @g_bibi12d (.classEq (.cv b) (syn_csn (.cv x))) syntaxFormula0210 syntaxFormula0212
        syntaxFormula0208 syntaxFormula0213 p0870 p0872
    have p0874 :=
      @g_syl5ibcom (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wb syntaxFormula0210 syntaxFormula0208) (.classEq (.cv b) (syn_csn (.cv x)))
        syntaxFormula0214 p0868 p0873
    have p0875 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0215 b
        dv_cache_0076 p0874
    have p0876 := @g_nfv syntaxFormula0214 b dv_cache_0077
    have p0877 :=
      @g_n_19_23 (.classEq (.cv b) (syn_csn (.cv x))) syntaxFormula0214 b p0876
    have p0878 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.all b syntaxFormula0215)
        (.imp (syn_wex b (.classEq (.cv b) (syn_csn (.cv x)))) syntaxFormula0214) p0875
        p0877
    have p0879 :=
      @g_syl5bi (.classMem (syn_csn (.cv x)) (syn_cvv))
        (syn_wex b (.classEq (.cv b) (syn_csn (.cv x))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0214 p0859 p0878
    have p0880 := @g_elex (syn_csn (.cv x)) (syn_cvv)
    have p0881 :=
      @g_a1ii
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
          (.imp (.classMem (syn_csn (.cv x)) (syn_cvv)) syntaxFormula0214))
        (.imp (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem (syn_csn (.cv x)) (syn_cvv)))
        p0879 p0880
    have p0882 := @g_elex syntaxClass0201 syntaxClass0199
    have p0883 := @g_opexb (syn_csn (.cv x)) syntaxClass0197
    have p0884 :=
      @g_simplbi (.classMem syntaxClass0201 (syn_cvv))
        (.classMem (syn_csn (.cv x)) (syn_cvv)) syntaxFormula0216 p0883
    have p0885 :=
      @g_syl syntaxFormula0212 (.classMem syntaxClass0201 (syn_cvv))
        (.classMem (syn_csn (.cv x)) (syn_cvv)) p0882 p0884
    have p0886 := @g_elex (syn_cop (syn_csn (.cv x)) (syn_csn (.cv a))) syntaxClass0198
    have p0887 := @g_opexb (syn_csn (.cv x)) (syn_csn (.cv a))
    have p0888 :=
      @g_simplbi (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (.cv a))) (syn_cvv))
        (.classMem (syn_csn (.cv x)) (syn_cvv)) (.classMem (syn_csn (.cv a)) (syn_cvv))
        p0887
    have p0889 :=
      @g_syl syntaxFormula0213
        (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (.cv a))) (syn_cvv))
        (.classMem (syn_csn (.cv x)) (syn_cvv)) p0886 p0888
    have p0890 :=
      @g_pm5_21ni syntaxFormula0212 (.classMem (syn_csn (.cv x)) (syn_cvv))
        syntaxFormula0213 p0885 p0889
    have p0891 :=
      @g_pm2_61d1 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_csn (.cv x)) (syn_cvv)) syntaxFormula0214 p0881 p0890
    have p0892 :=
      @g_brcnv (syn_csn (.cv x)) (.cv t)
        (syn_csi (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
    have p0893 :=
      @g_brsnsi2 y (.cv x) (.cv t) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))
        dv_cache_0078 dv_cache_0079 dv_cache_0080 p0853
    have p0894 :=
      @g_bitri syntaxFormula0217
        (syn_wbr (.cv t) (syn_csi (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_csn (.cv x)))
        syntaxFormula0219 p0892 p0893
    have p0895 :=
      @g_anbi1i syntaxFormula0217 syntaxFormula0219
        (syn_wbr (.cv t) (syn_csset) (syn_csn (.cv a))) p0894
    have p0896 :=
      @g_n_19_41v syntaxFormula0218 (syn_wbr (.cv t) (syn_csset) (syn_csn (.cv a))) y
        dv_cache_0081
    have p0897 :=
      @g_bitr4i syntaxFormula0220
        (syn_wa syntaxFormula0219 (syn_wbr (.cv t) (syn_csset) (syn_csn (.cv a))))
        syntaxFormula0222 p0895 p0896
    have p0898 := @g_exbii syntaxFormula0220 syntaxFormula0222 t p0897
    have p0899 := @g_excom syntaxFormula0221 t y
    have p0900 :=
      @g_anass (.classEq (.cv t) (syn_csn (.cv y)))
        (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x))
        (syn_wbr (.cv t) (syn_csset) (syn_csn (.cv a)))
    have p0901 := @g_exbii syntaxFormula0221 syntaxFormula0224 t p0900
    have p0902 := @g_snex (.cv y)
    have p0903 := @g_breq1 (.cv t) (syn_csn (.cv y)) (syn_csn (.cv a)) (syn_csset)
    have p0904 :=
      @g_anbi2d (.classEq (.cv t) (syn_csn (.cv y)))
        (syn_wbr (.cv t) (syn_csset) (syn_csn (.cv a)))
        (syn_wbr (syn_csn (.cv y)) (syn_csset) (syn_csn (.cv a)))
        (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x)) p0903
    have p0905 :=
      @g_ancom (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x))
        (syn_wbr (syn_csn (.cv y)) (syn_csset) (syn_csn (.cv a)))
    have p0906 := @g_vex y
    have p0907 := @g_brssetsn (.cv y) (syn_csn (.cv a)) p0906 p0839
    have p0908 :=
      @g_anbi1i (syn_wbr (syn_csn (.cv y)) (syn_csset) (syn_csn (.cv a)))
        (.classMem (.cv y) (syn_csn (.cv a)))
        (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x)) p0907
    have p0909 :=
      @g_bitri
        (syn_wa (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x))
          (syn_wbr (syn_csn (.cv y)) (syn_csset) (syn_csn (.cv a))))
        (syn_wa (syn_wbr (syn_csn (.cv y)) (syn_csset) (syn_csn (.cv a)))
          (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x)))
        syntaxFormula0225 p0905 p0908
    have p0910 :=
      @g_syl6bb (.classEq (.cv t) (syn_csn (.cv y))) syntaxFormula0223
        (syn_wa (syn_wbr (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x))
          (syn_wbr (syn_csn (.cv y)) (syn_csset) (syn_csn (.cv a))))
        syntaxFormula0225 p0904 p0909
    have p0911 :=
      @g_ceqsexv syntaxFormula0223 syntaxFormula0225 t (syn_csn (.cv y)) dv_cache_0082
        dv_cache_0083 p0902 p0910
    have p0912 :=
      @g_bitri syntaxFormula0226 (syn_wex t syntaxFormula0224) syntaxFormula0225 p0901
        p0911
    have p0913 := @g_exbii syntaxFormula0226 syntaxFormula0225 y p0912
    have p0914 :=
      @g_n_3bitri syntaxFormula0227 (syn_wex t syntaxFormula0222)
        (syn_wex y syntaxFormula0226) (syn_wex y syntaxFormula0225) p0898 p0899 p0913
    have p0915 :=
      @g_opelco t (syn_csn (.cv x)) (syn_csn (.cv a)) (syn_csset)
        (syn_ccnv (syn_csi (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))) dv_cache_0084
        dv_cache_0085 dv_cache_0086 dv_cache_0087
    have p0916 :=
      @g_elima2 y (.cv x) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))
        dv_cache_0078 dv_cache_0080 dv_cache_0088
    have p0917 :=
      @g_n_3bitr4i syntaxFormula0227 (syn_wex y syntaxFormula0225) syntaxFormula0213
        syntaxFormula0204 p0914 p0915 p0916
    have p0918 :=
      @g_syl6bb (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0212
        syntaxFormula0213 syntaxFormula0204 p0891 p0917
    have p0919 :=
      @g_bibi12d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0205
        syntaxFormula0204 syntaxFormula0212 syntaxFormula0204 p0857 p0918
    have p0920 :=
      @g_notbid (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0228
        syntaxFormula0229 p0919
    have p0921 :=
      @g_syl5bb syntaxFormula0230 (.neg syntaxFormula0228)
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0231 p0838 p0920
    have p0922 :=
      @g_exbidv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0230
        syntaxFormula0231 x dv_cache_0089 p0921
    have p0923 := @g_exnal syntaxFormula0229 x
    have p0924 :=
      @g_syl6bb (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0232
        (syn_wex x syntaxFormula0231) syntaxFormula0234 p0922 p0923
    have p0925 :=
      @g_syl5bb syntaxFormula0236 syntaxFormula0232
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0234 p0837 p0924
    have p0926 :=
      @g_con2bid (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0236
        syntaxFormula0233 p0925
    have p0927 :=
      (Nominal.classEqRefl (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))
    have p0928 :=
      @g_breqi (syn_csn (.cv a))
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))
        (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) syntaxClass0237 p0927
    have p0929 := (Nominal.biimpRefl syntaxFormula0238)
    have p0930 :=
      @g_opexg (syn_csn (.cv a))
        (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))) (syn_cvv)
        (syn_cvv)
    have p0931 :=
      @g_sylancr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_csn (.cv a)) (syn_cvv)) syntaxFormula0203 syntaxFormula0216 p0839
        p0850 p0930
    have p0932 := @g_elcomplg syntaxClass0197 syntaxClass0235 (syn_cvv)
    have p0933 :=
      @g_syl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0216
        (syn_wb syntaxFormula0239 syntaxFormula0240) p0931 p0932
    have p0934 :=
      @g_syl5bb syntaxFormula0238 syntaxFormula0239
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0240 p0929 p0933
    have p0935 :=
      @g_syl5bb syntaxFormula0241 syntaxFormula0238
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0240 p0928 p0934
    have p0936 :=
      @g_bitr4d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0233
        syntaxFormula0240 syntaxFormula0241 p0926 p0935
    have p0937 :=
      @g_syl5rbb
        (.classEq (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))
          (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
        syntaxFormula0233 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        syntaxFormula0241 p0836 p0936
    have p0938 :=
      @g_mpbiri (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0241
        (.classEq (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a)))
          (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_csn (.cv a))))
        p0835 p0937
    have p0939 := @g_tru
    have p0941 :=
      @g_imaexg (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x) (syn_cvv) (syn_cvv)
    have p0942 :=
      @g_sylancl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (syn_cvv))
        (.classMem (.cv x) (syn_cvv))
        (.classMem (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x)) (syn_cvv))
        p0848 p0853 p0941
    have p0943 :=
      @g_eueq y (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x))
        dv_cache_0090
    have p0944 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x)) (syn_cvv))
        (syn_weu y (.classEq (.cv y)
            (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x))))
        p0942 p0943
    have p0947 :=
      @g_brimage (.cv x) (.cv y) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) p0853 p0906
    have p0948 :=
      @g_eubii syntaxFormula0242
        (.classEq (.cv y) (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x))) y
        p0947
    have p0949 :=
      @g_sylibr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_weu y (.classEq (.cv y)
            (syn_cima (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))) (.cv x))))
        syntaxFormula0243 p0944 p0948
    have p0950 :=
      @g_ralrimivw (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0243 x
        (syn_cvv) dv_cache_0089 p0949
    have p0951 :=
      @g_fnres x y (syn_cvv) (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
        dv_cache_0091 dv_cache_0059 dv_cache_0092 dv_cache_0093 dv_cache_0007
    have p0952 :=
      @g_sylibr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wral x (syn_cvv) syntaxFormula0243)
        (syn_wfn (syn_cres (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv))
          (syn_cvv))
        p0950 p0951
    have p0953 := @g_resid (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u))))
    have p0954 :=
      @g_fneq1i (syn_cvv)
        (syn_cres (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv))
        (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) p0953
    have p0955 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wfn (syn_cres (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv))
          (syn_cvv))
        (syn_wfn (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv)) p0952
        p0954
    have p0956 :=
      @g_a1d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wfn (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv))
        syn_wtru p0955
    have p0957 := @g_a1i (.classMem (syn_csn (.cv a)) (syn_cvv)) syn_wtru p0839
    have p0958 :=
      @g_pm3_2 (syn_wfn (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv))
        (.classMem (syn_csn (.cv a)) (syn_cvv))
    have p0959 :=
      @g_syl5 syn_wtru (.classMem (syn_csn (.cv a)) (syn_cvv))
        (syn_wfn (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv))
        syntaxFormula0244 p0957 p0958
    have p0960 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syn_wtru
        (syn_wfn (syn_cimage (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))) (syn_cvv))
        (.imp syn_wtru syntaxFormula0244) p0956 p0959
    have p0961 :=
      @g_pm2_43d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syn_wtru
        syntaxFormula0244 p0960
    exact
      continuation p0691 p0697 p0705 p0715 p0717 p0719 p0721 p0722 p0724 p0726 p0734 p0736
        p0738 p0742 p0744 p0746 p0747 p0752 p0754 p0764 p0766 p0771 p0773 p0779 p0781
        p0791 p0794 p0796 p0798 p0805 p0807 p0809 p0815 p0820 p0824 p0825 p0827 p0828
        p0831 p0834 p0839 p0842 p0846 p0848 p0853 p0859 p0860 p0871 p0880 p0888 p0902
        p0903 p0906 p0907 p0938 p0939 p0955 p0957 p0961

end NFChoice.DirectNominalPrf.WPPReplay

end
