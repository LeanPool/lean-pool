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

/-- Checked nominal proof certificate identified upstream as `g_cfbhnqinjcodecoverddndv_stage1`. -/
@[expose]
noncomputable def gCfbhnqinjcodecoverddndvStage1 (u : Var) (P : Class) (k : Var)
    (Y : Class) (dv_P_u : u ∉ P.fv)
    (hyp_cfbhnqinjcodecoverddndv_1 : Nominal.NPrf (.classMem P (synCvv)))
    (hyp_cfbhnqinjcodecoverddndv_2 : Nominal.NPrf (.classMem Y (synCvv))) {Result : Type}
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
      f ∉ ((synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))).fv := by
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
        ((Wff.imp (synWa
              (synWf1o (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv x)
                (.cv y)) (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
              (synCpwpull (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv r))
              (synCwe) (.cv x)))).fv :=
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
      x ∉ ((synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))).fv := by
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
        ((Wff.imp (synWa (synWf1o (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
                (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv y))
              (synWbr (.cv r) (synCwe) (.cv y))) (synWbr
              (synCpwpull (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv r))
              (synCwe) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))))).fv :=
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
      y ∉ ((synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))).fv := by
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
        ((Wff.imp (synWa (synWf1o (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
                (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
                (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
              (synWbr (.cv r) (synCwe)
                (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synCpwpull (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv r))
              (synCwe) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))))).fv :=
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
    have dv_cache_0014 : r ∉ ((synCfv (synC1st) (.cv u))).fv := by
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
        ((Wff.imp (synWa (synWf1o (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
                (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
                (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
              (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
                (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))) (synWbr
              (synCpwpull (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
                (synCfv (synC1st) (.cv u)))
              (synCwe) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))))).fv :=
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
        ((Wff.imp (synWfo (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv x)
              (.cv y)) (synWss
              (synCpwpull (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv r))
              (synCxp (.cv x) (.cv x))))).fv :=
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
        ((Wff.imp (synWfo (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv y)) (synWss
              (synCpwpull (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv r))
              (synCxp (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
                (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))))).fv :=
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
        ((Wff.imp (synWfo (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
              (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))) (synWss
              (synCpwpull (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv r))
              (synCxp (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
                (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))))).fv :=
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
        ((Wff.imp (synWfo (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
              (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
              (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))) (synWss
              (synCpwpull (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
                (synCfv (synC1st) (.cv u)))
              (synCxp (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
                (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))))).fv :=
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
      Disjoint ((synCrn (.cv k))).fv ((synCfv (synC1st) (.cv a))).fv := by
      exact
        (show Disjoint ((synCrn (.cv k))).fv ((synCfv (synC1st) (.cv a))).fv from (by
            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
            exact
              (show Disjoint (((Class.cv k)).fv) ((((Class.cv a)).fv) ∪ (((synC1st)).fv))
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
                    (show Disjoint (((Class.cv k)).fv) (((synC1st)).fv) from
                      (by
                        rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                        exact
                          (show Disjoint (({ k } : Finset Var)) (((synC1st)).fv) from
                            (by
                              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                              exact
                                (show Disjoint (({ k } : Finset Var)) ((∅ : Finset Var))
                                  from (by simp))))))⟩))))
    have dv_cache_0021 : Disjoint (Y).fv ((synCfv (synC1st) (.cv a))).fv := by
      exact
        (show Disjoint (Y).fv ((synCfv (synC1st) (.cv a))).fv from (by
            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
            exact
              (show Disjoint ((Y).fv) ((((Class.cv a)).fv) ∪ (((synC1st)).fv)) from
                (Finset.disjoint_union_right.mpr
                  ⟨(show Disjoint ((Y).fv) (((Class.cv a)).fv) from
                      (by
                        rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                        exact
                          (show Disjoint ((Y).fv) (({ a } : Finset Var)) from
                            (Finset.disjoint_singleton_right.mpr
                              (show a ∉ (Y).fv from (by exact fresh_a_not_Y)))))),
                    (show Disjoint ((Y).fv) (((synC1st)).fv) from
                      (by
                        rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                        exact
                          (show Disjoint ((Y).fv) ((∅ : Finset Var)) from
                            (by simp))))⟩))))
    have dv_cache_0022 : a ∉ ((synChwcn (synCrn (.cv k)))).fv := by
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
    have dv_cache_0023 : a ∉ ((synChwcn Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            fresh_a_not_Y, not_false_eq_true])
    have dv_cache_0024 : a ∉ ((synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)).fv := by
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
      (synWss (synCfv (synC1st) (.cv u))
        (synCxp (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0001 : Wff :=
      (synWa (.classMem (.cv u) (synChwcodes (synCfv (synC2nd) (.cv u)))) syntaxFormula0000)
    let syntaxFormula0002 : Wff :=
      (synWa (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0003 : Wff :=
      (synWa (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)))
        (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0004 : Wff :=
      (synWf1o (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
        (synCfv (synC2nd) (.cv u)) (synCima (.cv k) (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0005 : Wff :=
      (.classEq (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCfv (synC2nd) (.cv u)))
    let syntaxFormula0006 : Wff :=
      (.classEq (synCfv (synC2nd) (.cv u))
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0007 : Wff :=
      (.classEq (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCima (.cv k) (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0008 : Wff :=
      (.classEq (synCima (.cv k) (synCfv (synC2nd) (.cv u)))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0009 : Wff :=
      (synWf1o (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0010 : Wff := (synWb syntaxFormula0004 syntaxFormula0009)
    let syntaxFormula0011 : Wff :=
      (synWf1o (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0012 : Wff :=
      (synWbr (synCfv (synC1st) (.cv u)) (synCwe)
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0013 : Wff :=
      (synWb syntaxFormula0012
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0014 : Wff :=
      (synWb (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        syntaxFormula0012)
    let syntaxFormula0015 : Wff :=
      (.imp (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        syntaxFormula0012)
    let syntaxFormula0016 : Wff :=
      (synWbr (.cv r) (synCwe) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxClass0017 : Class :=
      (synCcom (synCcnv (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))) (.cv r))
    let syntaxClass0018 : Class :=
      (synCcom (synCcnv (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synCfv (synC1st) (.cv u)))
    let syntaxClass0019 : Class :=
      (synCpwpull (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv r))
    let syntaxClass0020 : Class :=
      (synCcom syntaxClass0017 (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxClass0021 : Class :=
      (synCpwpull (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCfv (synC1st) (.cv u)))
    let syntaxClass0022 : Class :=
      (synCcom syntaxClass0018 (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0023 : Wff := (synWa syntaxFormula0011 syntaxFormula0016)
    let syntaxFormula0024 : Wff := (synWa syntaxFormula0011 syntaxFormula0012)
    let syntaxFormula0025 : Wff :=
      (synWbr syntaxClass0019 (synCwe)
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0026 : Wff :=
      (synWbr syntaxClass0021 (synCwe)
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0027 : Wff :=
      (synWf1o (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv y))
    let syntaxFormula0028 : Wff :=
      (synWa syntaxFormula0027 (synWbr (.cv r) (synCwe) (.cv y)))
    let syntaxFormula0029 : Wff :=
      (synWf1o (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
    let syntaxFormula0030 : Wff :=
      (synWa syntaxFormula0029 (synWbr (.cv r) (synCwe) (.cv y)))
    let syntaxFormula0031 : Wff := (synWbr syntaxClass0019 (synCwe) (.cv x))
    let syntaxFormula0032 : Wff := (.imp syntaxFormula0030 syntaxFormula0031)
    let syntaxFormula0033 : Wff := (.imp syntaxFormula0028 syntaxFormula0025)
    let syntaxFormula0034 : Wff := (.imp syntaxFormula0023 syntaxFormula0025)
    let syntaxClass0035 : Class :=
      (synCcom (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
    let syntaxClass0036 : Class :=
      (synCcom syntaxClass0035 (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0037 : Wff :=
      (synWbr syntaxClass0036 (synCwe)
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0038 : Wff :=
      (synWss (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (synCrn (.cv k)))
    let syntaxFormula0039 : Wff :=
      (synWb syntaxFormula0038
        (synWss (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k))))
    let syntaxFormula0040 : Wff :=
      (synWb (synWss (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k)))
        syntaxFormula0038)
    let syntaxFormula0041 : Wff :=
      (.imp (synWss (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k)))
        syntaxFormula0038)
    let syntaxClass0042 : Class :=
      (synCop syntaxClass0036 (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0043 : Wff :=
      (.classMem syntaxClass0042 (synChwcodes (synCrn (.cv k))))
    let syntaxFormula0044 : Wff :=
      (synWfo (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxClass0045 : Class :=
      (synCxp (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0046 : Wff := (synWss syntaxClass0019 syntaxClass0045)
    let syntaxFormula0047 : Wff := (synWss syntaxClass0021 syntaxClass0045)
    let syntaxFormula0048 : Wff :=
      (synWfo (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv y))
    let syntaxFormula0049 : Wff :=
      (synWfo (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv x) (.cv y))
    let syntaxFormula0050 : Wff := (synWss syntaxClass0019 (synCxp (.cv x) (.cv x)))
    let syntaxFormula0051 : Wff := (.imp syntaxFormula0049 syntaxFormula0050)
    let syntaxFormula0052 : Wff := (.imp syntaxFormula0048 syntaxFormula0046)
    let syntaxFormula0053 : Wff := (.imp syntaxFormula0044 syntaxFormula0046)
    let syntaxFormula0054 : Wff := (synWss syntaxClass0036 syntaxClass0045)
    let syntaxClass0055 : Class := (synCfv (synC2nd) syntaxClass0042)
    let syntaxClass0056 : Class := (synCfv (synC1st) syntaxClass0042)
    let syntaxClass0057 : Class := (synCxp syntaxClass0055 syntaxClass0055)
    let syntaxFormula0058 : Wff := (synWss syntaxClass0056 syntaxClass0057)
    let syntaxFormula0059 : Wff :=
      (.classMem syntaxClass0042 (synChwcn (synCrn (.cv k))))
    let syntaxFormula0060 : Wff :=
      (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCrn (.cv k))))
    let syntaxFormula0061 : Wff :=
      (.classMem (synCop (synCfv (synC1st) (.cv a)) (synCfv (synC2nd) (.cv a)))
        (synChwcodes (synCrn (.cv k))))
    let syntaxFormula0062 : Wff :=
      (synWa (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCrn (.cv k))))
    let syntaxFormula0063 : Wff :=
      (synWa (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) Y))
    let syntaxFormula0064 : Wff :=
      (.classMem (synCop (synCfv (synC1st) (.cv a)) (synCfv (synC2nd) (.cv a)))
        (synChwcodes Y))
    let syntaxFormula0065 : Wff :=
      (synWss (synCfv (synC1st) (.cv a))
        (synCxp (synCfv (synC2nd) (.cv a)) (synCfv (synC2nd) (.cv a))))
    let syntaxFormula0066 : Wff :=
      (synWa (.classMem (.cv a) (synChwcodes Y)) syntaxFormula0065)
    let syntaxFormula0067 : Wff :=
      (.classMem (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        (synChnord Y))
    let syntaxFormula0068 : Wff :=
      (synWa (synWfn (synChnqinc Y (synCun P Y)) (synChnord Y)) syntaxFormula0067)
    let syntaxClass0069 : Class :=
      (synCfv (synChnqinc Y (synCun P Y))
        (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y)))
    let syntaxFormula0070 : Wff :=
      (.classMem syntaxClass0069 (synCrn (synChnqinc Y (synCun P Y))))
    let syntaxFormula0071 : Wff :=
      (synWbr (synCec (.cv u) (synChwniso P)) (synCcnv (synChnqmap1 P)) (synCsn (.cv u)))
    have p0000 := @gSsun2 Y P
    have p0001 := @gUnex P Y hyp_cfbhnqinjcodecoverddndv_1 hyp_cfbhnqinjcodecoverddndv_2
    have p0002 := @gHnqincfn (synCun P Y) Y p0000 hyp_cfbhnqinjcodecoverddndv_2 p0001
    have p0003 :=
      @gA1i (synWfn (synChnqinc Y (synCun P Y)) (synChnord Y))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0002
    have p0004 := @gF1f1orn (synCfv (synC2nd) (.cv u)) Y (.cv k)
    have p0005 := @gId (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
    have p0006 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (synWf1o (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k))))
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y))
        p0004 p0005
    have p0007 := @gF1of1 (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)) (.cv k)
    have p0008 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWf1o (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k))) p0006 p0007
    have p0009 := @gHwcnselfbasendv u P dv_cache_0001
    have p0010 := @gId (.classMem (.cv u) (synChwcn P))
    have p0011 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.imp (.classMem (.cv u) (synChwcn P)) (.classMem (.cv u) (synChwcn P))) p0009
        p0010
    have p0012 := @gHwcnpair u (synCfv (synC2nd) (.cv u))
    have p0013 :=
      @gSyl (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv u) (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
        p0011 p0012
    have p0014 := @gVex u
    have p0015 := @gElhwcncl (synCfv (synC2nd) (.cv u)) (.cv u)
    have p0016 := Nominal.mp p0014 p0015
    have p0017 :=
      @gBiimpi (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0001 p0016
    have p0018 :=
      @gSyl (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0001
        p0011 p0017
    have p0019 :=
      @gSimpl (.classMem (.cv u) (synChwcodes (synCfv (synC2nd) (.cv u))))
        syntaxFormula0000
    have p0020 :=
      @gSyl (.classMem (.cv u) (synChwcn P)) syntaxFormula0001
        (.classMem (.cv u) (synChwcodes (synCfv (synC2nd) (.cv u)))) p0018 p0019
    have p0021 :=
      @gEqeltrrd (.classMem (.cv u) (synChwcn P)) (.cv u)
        (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synChwcodes (synCfv (synC2nd) (.cv u))) p0013 p0020
    have p0022 := @gFvex (.cv u) (synC1st)
    have p0023 := @gFvex (.cv u) (synC2nd)
    have p0024 :=
      @gElhwcodesclndv (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))
        (synCfv (synC2nd) (.cv u)) p0022 p0023
    have p0025 :=
      @gSylib (.classMem (.cv u) (synChwcn P))
        (.classMem (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u)))
          (synChwcodes (synCfv (synC2nd) (.cv u))))
        syntaxFormula0002 p0021 p0024
    have p0026 :=
      @gSimpr
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
    have p0027 :=
      @gSyl (.classMem (.cv u) (synChwcn P)) syntaxFormula0002
        (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u))) p0025 p0026
    have p0028 :=
      @gA1d (.classMem (.cv u) (synChwcn P))
        (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0027
    have p0029 :=
      @g_pm3_2 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)))
        (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
    have p0030 :=
      @gSyl9 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k))) syntaxFormula0003
        p0028 p0029
    have p0031 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)))
        (.classMem (.cv u) (synChwcn P))
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0003) p0008
        p0030
    have p0032 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0003 p0031
    have p0033 :=
      @gF1ores (synCfv (synC2nd) (.cv u)) (synCrn (.cv k))
        (synCfv (synC2nd) (.cv u)) (.cv k)
    have p0034 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0003
        syntaxFormula0004 p0032 p0033
    have p0035 :=
      @gF1odm (synCfv (synC2nd) (.cv u))
        (synCima (.cv k) (synCfv (synC2nd) (.cv u)))
        (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
    have p0036 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0004
        syntaxFormula0005 p0034 p0035
    have p0037 :=
      @gEqcom (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCfv (synC2nd) (.cv u))
    have p0038 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0005
        syntaxFormula0006 p0036 p0037
    have p0039 :=
      @gF1ofo (synCfv (synC2nd) (.cv u))
        (synCima (.cv k) (synCfv (synC2nd) (.cv u)))
        (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
    have p0040 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0004
        (synWfo (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
          (synCfv (synC2nd) (.cv u)) (synCima (.cv k) (synCfv (synC2nd) (.cv u))))
        p0034 p0039
    have p0041 :=
      @gForn (synCfv (synC2nd) (.cv u)) (synCima (.cv k) (synCfv (synC2nd) (.cv u)))
        (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
    have p0042 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfo (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
          (synCfv (synC2nd) (.cv u)) (synCima (.cv k) (synCfv (synC2nd) (.cv u))))
        syntaxFormula0007 p0040 p0041
    have p0043 :=
      @gEqcom (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCima (.cv k) (synCfv (synC2nd) (.cv u)))
    have p0044 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0007
        syntaxFormula0008 p0042 p0043
    have p0045 :=
      @gJcad (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0006
        syntaxFormula0008 p0038 p0044
    have p0046 :=
      @gF1oeq23 (synCfv (synC2nd) (.cv u))
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCima (.cv k) (synCfv (synC2nd) (.cv u)))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
    have p0047 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa syntaxFormula0006 syntaxFormula0008) syntaxFormula0010 p0045 p0046
    have p0048 := @gBi1 syntaxFormula0004 syntaxFormula0009
    have p0049 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0010
        (.imp syntaxFormula0004 syntaxFormula0009) p0047 p0048
    have p0050 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0004
        syntaxFormula0009 p0034 p0049
    have p0051 :=
      @gF1ocnv (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
    have p0052 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0009
        syntaxFormula0011 p0050 p0051
    have p0053 :=
      @gSimpl
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv u)))
    have p0054 :=
      @gSyl (.classMem (.cv u) (synChwcn P)) syntaxFormula0002
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        p0025 p0053
    have p0055 :=
      @gA1d (.classMem (.cv u) (synChwcn P))
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0054
    have p0056 :=
      @gBreq2 (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u)) (synCwe)
    have p0057 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0005
        syntaxFormula0013 p0036 p0056
    have p0058 :=
      @gBicom syntaxFormula0012
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
    have p0059 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0013
        syntaxFormula0014 p0057 p0058
    have p0060 :=
      @gBi1 (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        syntaxFormula0012
    have p0061 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0014
        syntaxFormula0015 p0059 p0060
    have p0062 :=
      @gId (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
    have p0063 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0015))
        (.imp (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
          (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u))))
        p0061 p0062
    have p0064 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWbr (synCfv (synC1st) (.cv u)) (synCwe) (synCfv (synC2nd) (.cv u)))
        syntaxFormula0012 p0055 p0063
    have p0065 :=
      @gJcad (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0011
        syntaxFormula0012 p0052 p0064
    have p0067 := @gBiid syntaxFormula0011
    have p0068 :=
      @gA1i (synWb syntaxFormula0011 syntaxFormula0011)
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))) p0067
    have p0069 := @gId (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
    have p0070 :=
      @gBreq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) (.cv r)
        (synCfv (synC1st) (.cv u))
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (synCwe) p0069
    have p0071 :=
      @gAnbi12d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) syntaxFormula0011
        syntaxFormula0011 syntaxFormula0016 syntaxFormula0012 p0068 p0070
    have p0073 :=
      @gCoeq2d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) (.cv r)
        (synCfv (synC1st) (.cv u))
        (synCcnv (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))) p0069
    have p0074 :=
      @gCoeq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) syntaxClass0017
        syntaxClass0018 (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) p0073
    have p0075 := (Nominal.classEqRefl syntaxClass0019)
    have p0076 := @gEqcomi syntaxClass0019 syntaxClass0020 p0075
    have p0077 := (Nominal.classEqRefl syntaxClass0021)
    have p0078 := @gEqcomi syntaxClass0021 syntaxClass0022 p0077
    have p0079 :=
      @gN3eqtr3g (.classEq (.cv r) (synCfv (synC1st) (.cv u))) syntaxClass0020
        syntaxClass0022 syntaxClass0019 syntaxClass0021 p0074 p0076 p0078
    have p0080 :=
      @gBreq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) syntaxClass0019
        syntaxClass0021 (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCwe) p0079
    have p0081 :=
      @gImbi12d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) syntaxFormula0023
        syntaxFormula0024 syntaxFormula0025 syntaxFormula0026 p0071 p0080
    have p0082 := @gVex k
    have p0084 := @gResex (.cv k) (synCfv (synC2nd) (.cv u)) p0082 p0023
    have p0085 := @gDmex (synCres (.cv k) (synCfv (synC2nd) (.cv u))) p0084
    have p0086 :=
      @gF1oeq3 (.cv y) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
    have p0087 :=
      @gId (.classEq (.cv y) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    have p0088 :=
      @gBreq2d
        (.classEq (.cv y) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (.cv y) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv r)
        (synCwe) p0087
    have p0089 :=
      @gAnbi12d
        (.classEq (.cv y) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0027 syntaxFormula0011 (synWbr (.cv r) (synCwe) (.cv y))
        syntaxFormula0016 p0086 p0088
    have p0090 := @gBiid syntaxFormula0025
    have p0091 :=
      @gA1i (synWb syntaxFormula0025 syntaxFormula0025)
        (.classEq (.cv y) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))) p0090
    have p0092 :=
      @gImbi12d
        (.classEq (.cv y) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0028 syntaxFormula0023 syntaxFormula0025 syntaxFormula0025 p0089
        p0091
    have p0095 := @gRnex (synCres (.cv k) (synCfv (synC2nd) (.cv u))) p0084
    have p0096 :=
      @gF1oeq2 (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv y)
        (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
    have p0097 := @gBiid (synWbr (.cv r) (synCwe) (.cv y))
    have p0098 :=
      @gA1i
        (synWb (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classEq (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))) p0097
    have p0099 :=
      @gAnbi12d
        (.classEq (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0029 syntaxFormula0027 (synWbr (.cv r) (synCwe) (.cv y))
        (synWbr (.cv r) (synCwe) (.cv y)) p0096 p0098
    have p0100 :=
      @gId (.classEq (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    have p0101 :=
      @gBreq2d
        (.classEq (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) syntaxClass0019
        (synCwe) p0100
    have p0102 :=
      @gImbi12d
        (.classEq (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0030 syntaxFormula0028 syntaxFormula0031 syntaxFormula0025 p0099
        p0101
    have p0105 := @gCnvex (synCres (.cv k) (synCfv (synC2nd) (.cv u))) p0084
    have p0106 :=
      @gF1oeq1 (.cv x) (.cv y) (.cv f)
        (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
    have p0108 :=
      @gA1i
        (synWb (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        p0097
    have p0109 :=
      @gAnbi12d
        (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synWf1o (.cv f) (.cv x) (.cv y)) syntaxFormula0029
        (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)) p0106
        p0108
    have p0110 :=
      @gId (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    have p0111 :=
      @gCnveqd
        (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) p0110
    have p0112 :=
      @gCoeq1d
        (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synCcnv (.cv f))
        (synCcnv (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))) (.cv r)
        p0111
    have p0114 :=
      @gCoeq12d
        (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synCcom (synCcnv (.cv f)) (.cv r)) syntaxClass0017 (.cv f)
        (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) p0112 p0110
    have p0115 := (Nominal.classEqRefl (synCpwpull (.cv f) (.cv r)))
    have p0116 :=
      @gEqcomi (synCpwpull (.cv f) (.cv r))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0115
    have p0119 :=
      @gN3eqtr3g
        (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) syntaxClass0020
        (synCpwpull (.cv f) (.cv r)) syntaxClass0019 p0114 p0116 p0076
    have p0120 :=
      @gBreq1d
        (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synCpwpull (.cv f) (.cv r)) syntaxClass0019 (.cv x) (synCwe) p0119
    have p0121 :=
      @gImbi12d
        (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0030 (synWbr (synCpwpull (.cv f) (.cv r)) (synCwe) (.cv x))
        syntaxFormula0031 p0109 p0120
    have p0122 :=
      @gPwpullwesetimpndv x y f r dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
        dv_cache_0006 dv_cache_0007
    have p0123 :=
      @gVtocl
        (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
          (synWbr (synCpwpull (.cv f) (.cv r)) (synCwe) (.cv x)))
        syntaxFormula0032 f (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        dv_cache_0008 dv_cache_0009 p0105 p0121 p0122
    have p0124 :=
      @gVtocl syntaxFormula0032 syntaxFormula0033 x
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) dv_cache_0010
        dv_cache_0011 p0095 p0102 p0123
    have p0125 :=
      @gVtocl syntaxFormula0033 syntaxFormula0034 y
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) dv_cache_0012
        dv_cache_0013 p0085 p0092 p0124
    have p0126 :=
      @gVtocl syntaxFormula0034 (.imp syntaxFormula0024 syntaxFormula0026) r
        (synCfv (synC1st) (.cv u)) dv_cache_0014 dv_cache_0015 p0022 p0081 p0125
    have p0127 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0024
        syntaxFormula0026 p0065 p0126
    have p0129 := @gCnvcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
    have p0130 :=
      @gCoeq1i (synCcnv (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)) p0129
    have p0131 :=
      @gCoeq1i syntaxClass0018 syntaxClass0035
        (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) p0130
    have p0132 := @gEqtri syntaxClass0021 syntaxClass0022 syntaxClass0036 p0077 p0131
    have p0133 := @gEqid (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
    have p0134 :=
      @gBreq12i syntaxClass0021 syntaxClass0036
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (synCwe) p0132 p0133
    have p0135 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0026
        syntaxFormula0037 p0127 p0134
    have p0136 := @gImassrn (.cv k) (synCfv (synC2nd) (.cv u))
    have p0137 := @gF1ofo (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)) (.cv k)
    have p0138 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWf1o (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)))
        (synWfo (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k))) p0006 p0137
    have p0139 := @gForn (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)) (.cv k)
    have p0140 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfo (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)))
        (.classEq (synCrn (.cv k)) (synCrn (.cv k))) p0138 p0139
    have p0141 :=
      @gSyl5sseq (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (synCrn (.cv k))
        (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k)) p0136 p0140
    have p0142 :=
      @gSseq1 (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k))
    have p0143 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0007
        syntaxFormula0039 p0042 p0142
    have p0144 :=
      @gBicom syntaxFormula0038
        (synWss (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k)))
    have p0145 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0039
        syntaxFormula0040 p0143 p0144
    have p0146 :=
      @gBi1 (synWss (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k)))
        syntaxFormula0038
    have p0147 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0040
        syntaxFormula0041 p0145 p0146
    have p0148 :=
      @gId (synWss (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k)))
    have p0149 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0041))
        (.imp (synWss (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k)))
          (synWss (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k))))
        p0147 p0148
    have p0150 :=
      @gMpdi (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWss (synCima (.cv k) (synCfv (synC2nd) (.cv u))) (synCrn (.cv k)))
        syntaxFormula0038 p0141 p0149
    have p0151 :=
      @gJcad (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0037
        syntaxFormula0038 p0135 p0150
    have p0155 :=
      @gCoex (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u))
        p0084 p0022
    have p0159 :=
      @gCoex syntaxClass0035 (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        p0155 p0105
    have p0163 :=
      @gElhwcodesclndv syntaxClass0036
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (synCrn (.cv k)) p0159
        p0095
    have p0164 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa syntaxFormula0037 syntaxFormula0038) syntaxFormula0043 p0151 p0163
    have p0165 :=
      @gF1ofo (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
    have p0166 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0011
        syntaxFormula0044 p0052 p0165
    have p0168 := @gBiid syntaxFormula0044
    have p0169 :=
      @gA1i (synWb syntaxFormula0044 syntaxFormula0044)
        (.classEq (.cv r) (synCfv (synC1st) (.cv u))) p0168
    have p0178 :=
      @gSseq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) syntaxClass0019
        syntaxClass0021 syntaxClass0045 p0079
    have p0179 :=
      @gImbi12d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) syntaxFormula0044
        syntaxFormula0044 syntaxFormula0046 syntaxFormula0047 p0169 p0178
    have p0183 :=
      @gFoeq3 (.cv y) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
    have p0184 := @gBiid syntaxFormula0046
    have p0185 :=
      @gA1i (synWb syntaxFormula0046 syntaxFormula0046)
        (.classEq (.cv y) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))) p0184
    have p0186 :=
      @gImbi12d
        (.classEq (.cv y) (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0048 syntaxFormula0044 syntaxFormula0046 syntaxFormula0046 p0183
        p0185
    have p0190 :=
      @gFoeq2 (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv y)
        (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
    have p0193 :=
      @gXpeq12d
        (.classEq (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv x)
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) p0100 p0100
    have p0194 :=
      @gSseq2d
        (.classEq (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synCxp (.cv x) (.cv x)) syntaxClass0045 syntaxClass0019 p0193
    have p0195 :=
      @gImbi12d
        (.classEq (.cv x) (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0049 syntaxFormula0048 syntaxFormula0050 syntaxFormula0046 p0190
        p0194
    have p0199 :=
      @gFoeq1 (.cv x) (.cv y) (.cv f)
        (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
    have p0210 :=
      @gSseq1d
        (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synCpwpull (.cv f) (.cv r)) syntaxClass0019 (synCxp (.cv x) (.cv x)) p0119
    have p0211 :=
      @gImbi12d
        (.classEq (.cv f) (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
        (synWfo (.cv f) (.cv x) (.cv y)) syntaxFormula0049
        (synWss (synCpwpull (.cv f) (.cv r)) (synCxp (.cv x) (.cv x)))
        syntaxFormula0050 p0199 p0210
    have p0212 :=
      @gPwpullssxpsetimpndv x y f r dv_cache_0002 dv_cache_0003 dv_cache_0004
        dv_cache_0005 dv_cache_0006 dv_cache_0007
    have p0213 :=
      @gVtocl
        (.imp (synWfo (.cv f) (.cv x) (.cv y))
          (synWss (synCpwpull (.cv f) (.cv r)) (synCxp (.cv x) (.cv x))))
        syntaxFormula0051 f (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        dv_cache_0008 dv_cache_0016 p0105 p0211 p0212
    have p0214 :=
      @gVtocl syntaxFormula0051 syntaxFormula0052 x
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) dv_cache_0010
        dv_cache_0017 p0095 p0195 p0213
    have p0215 :=
      @gVtocl syntaxFormula0052 syntaxFormula0053 y
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) dv_cache_0012
        dv_cache_0018 p0085 p0186 p0214
    have p0216 :=
      @gVtocl syntaxFormula0053 (.imp syntaxFormula0044 syntaxFormula0047) r
        (synCfv (synC1st) (.cv u)) dv_cache_0014 dv_cache_0019 p0022 p0179 p0215
    have p0217 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0044
        syntaxFormula0047 p0166 p0216
    have p0223 := @gEqcomi syntaxClass0021 syntaxClass0036 p0132
    have p0224 := @gSseq1i syntaxClass0036 syntaxClass0021 syntaxClass0045 p0223
    have p0225 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0047
        syntaxFormula0054 p0217 p0224
    have p0237 :=
      @gOpfv1st syntaxClass0036 (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        p0159 p0095
    have p0249 :=
      @gOpfv2nd syntaxClass0036 (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        p0159 p0095
    have p0262 :=
      @gXpeq12i syntaxClass0055 (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        syntaxClass0055 (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) p0249
        p0249
    have p0263 :=
      @gSseq12i syntaxClass0056 syntaxClass0036 syntaxClass0057 syntaxClass0045 p0237
        p0262
    have p0264 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0054
        syntaxFormula0058 p0225 p0263
    have p0265 :=
      @gJcad (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0043
        syntaxFormula0058 p0164 p0264
    have p0277 :=
      @gOpex syntaxClass0036 (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        p0159 p0095
    have p0278 := @gElhwcncl (synCrn (.cv k)) syntaxClass0042
    have p0279 := Nominal.mp p0277 p0278
    have p0280 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa syntaxFormula0043 syntaxFormula0058) syntaxFormula0059 p0265 p0279
    have p0282 := @gHncodetrnfnvalndv u (.cv k) p0082 p0014
    have p0283 :=
      @gA1i (.classEq (synCfv (synChncodetrnfn (.cv k)) (.cv u)) syntaxClass0042)
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0282
    have p0284 :=
      @gEleq1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synCfv (synChncodetrnfn (.cv k)) (.cv u)) syntaxClass0042
        (synChwcn (synCrn (.cv k))) p0283
    have p0285 :=
      @gBiimprd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0060
        syntaxFormula0059 p0284
    have p0286 :=
      @gSylcom (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0059
        syntaxFormula0060 p0280 p0285
    have p0287 := @gHwcnraw a (synCrn (.cv k))
    have p0288 := @gHwcnpair a (synCrn (.cv k))
    have p0289 :=
      @gEleq1d (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) (.cv a)
        (synCop (synCfv (synC1st) (.cv a)) (synCfv (synC2nd) (.cv a)))
        (synChwcodes (synCrn (.cv k))) p0288
    have p0290 :=
      @gMpbid (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv a) (synChwcodes (synCrn (.cv k)))) syntaxFormula0061 p0287 p0289
    have p0291 := @gFvex (.cv a) (synC1st)
    have p0292 := @gFvex (.cv a) (synC2nd)
    have p0293 :=
      @gElhwcodes (synCrn (.cv k)) (synCfv (synC2nd) (.cv a))
        (synCfv (synC1st) (.cv a)) dv_cache_0020 p0291 p0292
    have p0294 := @gBiimpi syntaxFormula0061 syntaxFormula0062 p0293
    have p0295 :=
      @gSyl (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0061
        syntaxFormula0062 p0290 p0294
    have p0296 :=
      @gSimpld (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCrn (.cv k))) p0295
    have p0306 :=
      @gSimprd (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCrn (.cv k))) p0295
    have p0307 := @gF1f (synCfv (synC2nd) (.cv u)) Y (.cv k)
    have p0308 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (synWf (.cv k) (synCfv (synC2nd) (.cv u)) Y))
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y))
        p0307 p0005
    have p0309 := @gFrn (synCfv (synC2nd) (.cv u)) Y (.cv k)
    have p0310 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWf (.cv k) (synCfv (synC2nd) (.cv u)) Y) (synWss (synCrn (.cv k)) Y)
        p0308 p0309
    have p0311 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWss (synCrn (.cv k)) Y) (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        p0310
    have p0312 := @gSstr (synCfv (synC2nd) (.cv a)) (synCrn (.cv k)) Y
    have p0313 :=
      @gEx (synWss (synCfv (synC2nd) (.cv a)) (synCrn (.cv k)))
        (synWss (synCrn (.cv k)) Y) (synWss (synCfv (synC2nd) (.cv a)) Y) p0312
    have p0314 :=
      @gSyl9 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) (synWss (synCrn (.cv k)) Y)
        (synWss (synCfv (synC2nd) (.cv a)) (synCrn (.cv k)))
        (synWss (synCfv (synC2nd) (.cv a)) Y) p0311 p0313
    have p0315 :=
      @gSyl5 (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWss (synCfv (synC2nd) (.cv a)) (synCrn (.cv k)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
          (synWss (synCfv (synC2nd) (.cv a)) Y))
        p0306 p0314
    have p0316 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWss (synCfv (synC2nd) (.cv a)) Y) p0315
    have p0317 :=
      @g_pm3_2
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) Y)
    have p0318 :=
      @gSyl9 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWss (synCfv (synC2nd) (.cv a)) Y)
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        syntaxFormula0063 p0316 p0317
    have p0319 :=
      @gSyl5 (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0063) p0296
        p0318
    have p0320 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0063 p0319
    have p0323 :=
      @gElhwcodes Y (synCfv (synC2nd) (.cv a)) (synCfv (synC1st) (.cv a))
        dv_cache_0021 p0291 p0292
    have p0324 := @gBiimpri syntaxFormula0064 syntaxFormula0063 p0323
    have p0325 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0063
        syntaxFormula0064 p0320 p0324
    have p0327 :=
      @gEleq1d (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) (.cv a)
        (synCop (synCfv (synC1st) (.cv a)) (synCfv (synC2nd) (.cv a)))
        (synChwcodes Y) p0288
    have p0328 :=
      @gBiimprd (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv a) (synChwcodes Y)) syntaxFormula0064 p0327
    have p0329 :=
      @gSylcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0064
        (.classMem (.cv a) (synChwcodes Y)) p0325 p0328
    have p0330 := @gHwcnsupp a (synCrn (.cv k))
    have p0331 := @g_pm3_2 (.classMem (.cv a) (synChwcodes Y)) syntaxFormula0065
    have p0332 :=
      @gSyl5 (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0065
        (.classMem (.cv a) (synChwcodes Y)) syntaxFormula0066 p0330 p0331
    have p0333 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv a) (synChwcodes Y))
        (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0066) p0329
        p0332
    have p0334 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0066 p0333
    have p0335 := @gElhwcn a Y
    have p0336 := @gBiimpri (.classMem (.cv a) (synChwcn Y)) syntaxFormula0066 p0335
    have p0337 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0066
        (.classMem (.cv a) (synChwcn Y)) p0334 p0336
    have p0338 :=
      @gSsrdv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) a
        (synChwcn (synCrn (.cv k))) (synChwcn Y) dv_cache_0022 dv_cache_0023
        dv_cache_0024 p0337
    have p0339 :=
      @gSseld (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synChwcn (synCrn (.cv k))) (synChwcn Y)
        (synCfv (synChncodetrnfn (.cv k)) (.cv u)) p0338
    have p0340 :=
      @gSylcom (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0060
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn Y)) p0286 p0339
    have p0341 :=
      @gHwnisoclasselhnordcl Y (synCfv (synChncodetrnfn (.cv k)) (.cv u))
        hyp_cfbhnqinjcodecoverddndv_2
    have p0342 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn Y))
        syntaxFormula0067 p0340 p0341
    have p0343 :=
      @g_pm3_2 (synWfn (synChnqinc Y (synCun P Y)) (synChnord Y)) syntaxFormula0067
    have p0344 :=
      @gSyl9 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0067
        (synWfn (synChnqinc Y (synCun P Y)) (synChnord Y)) syntaxFormula0068 p0342
        p0343
    have p0345 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfn (synChnqinc Y (synCun P Y)) (synChnord Y))
        (.classMem (.cv u) (synChwcn P))
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0068) p0003
        p0344
    have p0346 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0068 p0345
    have p0347 :=
      @gFnfvelrn (synChnord Y)
        (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        (synChnqinc Y (synCun P Y))
    have p0348 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0068
        syntaxFormula0070 p0346 p0347
    have p0349 := @gHnqmap1valcl P (.cv u) hyp_cfbhnqinjcodecoverddndv_1
    have p0350 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.classEq (synCfv (synChnqmap1 P) (synCsn (.cv u)))
            (synCec (.cv u) (synChwniso P))))
        (.imp (.classMem (.cv u) (synChwcn P)) (.classMem (.cv u) (synChwcn P))) p0349
        p0010
    have p0351 := @gSnelpw1 (.cv u) (synChwcn P)
    have p0352 :=
      @gSylibr (.classMem (.cv u) (synChwcn P)) (.classMem (.cv u) (synChwcn P))
        (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn P))) p0010 p0351
    have p0353 := @gHnqmap1fn P hyp_cfbhnqinjcodecoverddndv_1
    have p0354 :=
      @gJctil (.classMem (.cv u) (synChwcn P))
        (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn P)))
        (synWfn (synChnqmap1 P) (synCpw1 (synChwcn P))) p0352 p0353
    have p0355 :=
      @gFnbrfvb (synCpw1 (synChwcn P)) (synCsn (.cv u))
        (synCec (.cv u) (synChwniso P)) (synChnqmap1 P)
    have p0356 :=
      @gSyl (.classMem (.cv u) (synChwcn P))
        (synWa (synWfn (synChnqmap1 P) (synCpw1 (synChwcn P)))
          (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn P))))
        (synWb (.classEq (synCfv (synChnqmap1 P) (synCsn (.cv u)))
            (synCec (.cv u) (synChwniso P)))
          (synWbr (synCsn (.cv u)) (synChnqmap1 P) (synCec (.cv u) (synChwniso P))))
        p0354 p0355
    have p0357 :=
      @gMpbid (.classMem (.cv u) (synChwcn P))
        (.classEq (synCfv (synChnqmap1 P) (synCsn (.cv u)))
          (synCec (.cv u) (synChwniso P)))
        (synWbr (synCsn (.cv u)) (synChnqmap1 P) (synCec (.cv u) (synChwniso P)))
        p0350 p0356
    have p0358 :=
      @gBrcnv (synCec (.cv u) (synChwniso P)) (synCsn (.cv u)) (synChnqmap1 P)
    have p0359 :=
      @gSylibr (.classMem (.cv u) (synChwcn P))
        (synWbr (synCsn (.cv u)) (synChnqmap1 P) (synCec (.cv u) (synChwniso P)))
        syntaxFormula0071 p0357 p0358
    have p0360 := @gSsun1 P Y
    have p0361 := @gHwcnssbase (synCun P Y) P p0360
    have p0362 := @gSsel (synChwcn P) (synChwcn (synCun P Y)) (.cv u)
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

/-- Checked nominal proof certificate identified upstream as `g_cfbhnqinjcodecoverddndv_stage2`. -/
@[expose]
noncomputable def gCfbhnqinjcodecoverddndvStage2 (u : Var) (P : Class) (k : Var)
    (Y : Class) (dv_P_u : u ∉ P.fv)
    (hyp_cfbhnqinjcodecoverddndv_1 : Nominal.NPrf (.classMem P (synCvv))) (p0001 : _)
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
    have dv_cache_0025 : x ∉ ((synCsn (.cv u))).fv := by
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
        ((synWa (synWbr (synCec (.cv u) (synChwniso P)) (synCcnv (synChnqmap1 P))
              (synCsn (.cv u))) (synWbr (synCsn (.cv u)) (synChnqmap1 (synCun P Y))
              (synCec (.cv u) (synChwniso (synCun P Y)))))).fv :=
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
    have dv_cache_0027 : x ∉ ((synCec (.cv u) (synChwniso P))).fv := by
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
    have dv_cache_0028 : x ∉ ((synCec (.cv u) (synChwniso (synCun P Y)))).fv := by
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
    have dv_cache_0029 : x ∉ ((synChnqmap1 (synCun P Y))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            fresh_x_not_P, fresh_x_not_Y, or_false, not_false_eq_true])
    have dv_cache_0030 : x ∉ ((synCcnv (synChnqmap1 P))).fv := by
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
        ((synWa (synWbr (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
              (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) (synCsn (.cv u)))
            (synWbr (synCsn (.cv u)) (synChnqmap1 (synCun P Y))
              (synCec (.cv u) (synChwniso (synCun P Y)))))).fv :=
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
      x ∉ ((synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))).fv := by
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
      x ∉ ((synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))).fv := by
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
    have dv_cache_0036 : p ∉ ((synChnqmap1 (synCun P Y))).fv := by
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
      p ∉ ((synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))).fv := by
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
        ((synWa (synWbr (.cv x) (synCcom (synChnqmap1 (synCun P Y))
                (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))) (.cv y))
            (synWbr (.cv x) (synCcom (synChnqmap1 (synCun P Y))
                (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))) (.cv z)))).fv :=
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
    have dv_cache_0041 : q ∉ ((synChnqmap1 (synCun P Y))).fv := by
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
      q ∉ ((synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))).fv := by
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
        ((synWa (synWa (synWbr (.cv x) (synCcom (synChnqmap1 (synCun P Y))
                  (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))) (.cv y))
              (synWbr (.cv x) (synCcom (synChnqmap1 (synCun P Y))
                  (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))) (.cv z))) (synWa
              (synWbr (.cv x) (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) (.cv p))
              (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y))))).fv :=
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
      Disjoint ((synCfv (synC2nd) (.cv u))).fv ((synCfv (synC1st) (.cv a))).fv := by
      exact
        (show Disjoint ((synCfv (synC2nd) (.cv u))).fv ((synCfv (synC1st) (.cv a))).fv from
          (by
            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv ((synC2nd))
                ((Class.cv u)),
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv ((synC1st))
                ((Class.cv a))];
            exact
              (show
                Disjoint ((((Class.cv u)).fv) ∪ (((synC2nd)).fv))
                  ((((Class.cv a)).fv) ∪ (((synC1st)).fv))
                from
                (Finset.disjoint_union_left.mpr
                  ⟨(show
                      Disjoint (((Class.cv u)).fv)
                        ((((Class.cv a)).fv) ∪ (((synC1st)).fv))
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
                          (show Disjoint (((Class.cv u)).fv) (((synC1st)).fv) from
                            (by
                              rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                              exact
                                (show Disjoint (({ u } : Finset Var)) (((synC1st)).fv)
                                  from
                                  (by
                                    rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                                    exact
                                      (show
                                        Disjoint (({ u } : Finset Var)) ((∅ : Finset Var))
                                        from (by simp))))))⟩)),
                    (show
                      Disjoint (((synC2nd)).fv) ((((Class.cv a)).fv) ∪ (((synC1st)).fv))
                      from
                      (Finset.disjoint_union_right.mpr
                        ⟨(show Disjoint (((synC2nd)).fv) (((Class.cv a)).fv) from
                            (by
                              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd];
                              exact
                                (show Disjoint ((∅ : Finset Var)) (((Class.cv a)).fv) from
                                  (by simp)))),
                          (show Disjoint (((synC2nd)).fv) (((synC1st)).fv) from
                            (by
                              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd];
                              exact
                                (show Disjoint ((∅ : Finset Var)) (((synC1st)).fv) from
                                  (by simp))))⟩))⟩))))
    have dv_cache_0045 : Disjoint ((synCun P Y)).fv ((synCfv (synC1st) (.cv a))).fv :=
      by
      exact
        (show Disjoint ((synCun P Y)).fv ((synCfv (synC1st) (.cv a))).fv from (by
            rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
              NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv];
            exact
              (show
                Disjoint (((P).fv) ∪ ((Y).fv)) ((((Class.cv a)).fv) ∪ (((synC1st)).fv))
                from
                (Finset.disjoint_union_left.mpr
                  ⟨(show Disjoint ((P).fv) ((((Class.cv a)).fv) ∪ (((synC1st)).fv)) from
                      (Finset.disjoint_union_right.mpr
                        ⟨(show Disjoint ((P).fv) (((Class.cv a)).fv) from
                            (by
                              rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                              exact
                                (show Disjoint ((P).fv) (({ a } : Finset Var)) from
                                  (Finset.disjoint_singleton_right.mpr
                                    (show a ∉ (P).fv from (by exact fresh_a_not_P)))))),
                          (show Disjoint ((P).fv) (((synC1st)).fv) from
                            (by
                              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                              exact
                                (show Disjoint ((P).fv) ((∅ : Finset Var)) from
                                  (by simp))))⟩)),
                    (show Disjoint ((Y).fv) ((((Class.cv a)).fv) ∪ (((synC1st)).fv)) from
                      (Finset.disjoint_union_right.mpr
                        ⟨(show Disjoint ((Y).fv) (((Class.cv a)).fv) from
                            (by
                              rw [NFChoice.Compiler.CoreFVSimp.fv_class_cv];
                              exact
                                (show Disjoint ((Y).fv) (({ a } : Finset Var)) from
                                  (Finset.disjoint_singleton_right.mpr
                                    (show a ∉ (Y).fv from (by exact fresh_a_not_Y)))))),
                          (show Disjoint ((Y).fv) (((synC1st)).fv) from
                            (by
                              rw [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st];
                              exact
                                (show Disjoint ((Y).fv) ((∅ : Finset Var)) from
                                  (by simp))))⟩))⟩))))
    have dv_cache_0046 : a ∉ ((synChwcn (synCfv (synC2nd) (.cv u)))).fv := by
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
    have dv_cache_0047 : a ∉ ((synChwcn (synCun P Y))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            fresh_a_not_P, fresh_a_not_Y, or_false, not_false_eq_true])
    have dv_cache_0048 : a ∉ ((Wff.classMem (.cv u) (synChwcn P))).fv := by
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
    have dv_cache_0049 : y ∉ ((synCuni (.cv q))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_q,
            not_false_eq_true])
    have dv_cache_0050 : x ∉ ((synCuni (.cv p))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_p,
            not_false_eq_true])
    have dv_cache_0051 : h ∉ ((synCfv (synC2nd) (.cv u))).fv := by
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
    have dv_cache_0054 : h ∉ ((synCun P Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
            Finset.mem_union, fresh_h_not_P, fresh_h_not_Y, or_false, not_false_eq_true])
    have dv_cache_0055 : x ∉ ((Wff.classMem (.cv u) (synChwcn P))).fv := by
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
        ((Wff.imp (synWa
              (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
              (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u))))) (.imp
              (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
              (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (.cv y))))).fv :=
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
    have dv_cache_0057 : y ∉ ((Wff.classMem (.cv u) (synChwcn P))).fv := by
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
    have dv_cache_0058 : y ∉ ((synCuni (.cv p))).fv := by
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
      (synWss (synCfv (synC1st) (.cv a))
        (synCxp (synCfv (synC2nd) (.cv a)) (synCfv (synC2nd) (.cv a))))
    let syntaxFormula0071 : Wff :=
      (synWbr (synCec (.cv u) (synChwniso P)) (synCcnv (synChnqmap1 P)) (synCsn (.cv u)))
    let syntaxFormula0072 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (synCsn (.cv u)))
        (synCec (.cv u) (synChwniso (synCun P Y))))
    let syntaxFormula0073 : Wff :=
      (synWbr (synCsn (.cv u)) (synChnqmap1 (synCun P Y))
        (synCec (.cv u) (synChwniso (synCun P Y))))
    let syntaxFormula0074 : Wff :=
      (synWbr (.cv x) (synChnqmap1 (synCun P Y))
        (synCec (.cv u) (synChwniso (synCun P Y))))
    let syntaxFormula0075 : Wff :=
      (synWa (synWbr (synCec (.cv u) (synChwniso P)) (synCcnv (synChnqmap1 P)) (.cv x))
        syntaxFormula0074)
    let syntaxFormula0076 : Wff := (synWa syntaxFormula0071 syntaxFormula0073)
    let syntaxFormula0077 : Wff := (synWex x syntaxFormula0075)
    let syntaxFormula0078 : Wff :=
      (synWbr (synCec (.cv u) (synChwniso P)) (synChnqinc P (synCun P Y))
        (synCec (.cv u) (synChwniso (synCun P Y))))
    let syntaxFormula0079 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv u)))
        (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0080 : Wff :=
      (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0081 : Wff :=
      (synWfn (synChnqmap1 (synCfv (synC2nd) (.cv u)))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0082 : Wff := (synWa syntaxFormula0081 syntaxFormula0080)
    let syntaxFormula0083 : Wff :=
      (synWbr (synCsn (.cv u)) (synChnqmap1 (synCfv (synC2nd) (.cv u)))
        (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0084 : Wff := (synWb syntaxFormula0079 syntaxFormula0083)
    let syntaxFormula0085 : Wff :=
      (synWbr (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) (synCsn (.cv u)))
    let syntaxFormula0086 : Wff :=
      (synWbr (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) (.cv x))
    let syntaxFormula0087 : Wff := (synWa syntaxFormula0086 syntaxFormula0074)
    let syntaxFormula0088 : Wff := (synWa syntaxFormula0085 syntaxFormula0073)
    let syntaxFormula0089 : Wff := (synWex x syntaxFormula0087)
    let syntaxClass0090 : Class :=
      (synCcom (synChnqmap1 (synCun P Y))
        (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0091 : Wff :=
      (synWbr (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        syntaxClass0090 (synCec (.cv u) (synChwniso (synCun P Y))))
    let syntaxFormula0092 : Wff :=
      (synWbr (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y))
        (synCec (.cv u) (synChwniso (synCun P Y))))
    let syntaxFormula0093 : Wff := (synWbr (.cv x) syntaxClass0090 (.cv y))
    let syntaxFormula0094 : Wff := (synWbr (.cv x) syntaxClass0090 (.cv z))
    let syntaxFormula0095 : Wff := (synWa syntaxFormula0093 syntaxFormula0094)
    let syntaxFormula0096 : Wff :=
      (synWbr (.cv x) (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) (.cv p))
    let syntaxFormula0097 : Wff :=
      (synWa syntaxFormula0096 (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y)))
    let syntaxFormula0098 : Wff := (synWex p syntaxFormula0097)
    let syntaxFormula0099 : Wff :=
      (synWbr (.cv x) (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) (.cv q))
    let syntaxFormula0100 : Wff :=
      (synWa syntaxFormula0099 (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z)))
    let syntaxFormula0101 : Wff := (synWex q syntaxFormula0100)
    let syntaxFormula0102 : Wff := (synWa syntaxFormula0095 syntaxFormula0097)
    let syntaxFormula0103 : Wff := (synWa syntaxFormula0102 syntaxFormula0100)
    let syntaxFormula0104 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p)) (.cv x))
    let syntaxFormula0105 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)) (.cv x))
    let syntaxFormula0106 : Wff :=
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))))
    let syntaxFormula0107 : Wff :=
      (.classMem (synCop (synCfv (synC1st) (.cv a)) (synCfv (synC2nd) (.cv a)))
        (synChwcodes (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0108 : Wff :=
      (synWa (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0109 : Wff :=
      (synWa (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y)))
    let syntaxFormula0110 : Wff :=
      (.classMem (synCop (synCfv (synC1st) (.cv a)) (synCfv (synC2nd) (.cv a)))
        (synChwcodes (synCun P Y)))
    let syntaxFormula0111 : Wff :=
      (synWa (.classMem (.cv a) (synChwcodes (synCun P Y))) syntaxFormula0065)
    let syntaxFormula0112 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (synCsn (synCuni (.cv p))))
        (synCec (synCuni (.cv p)) (synChwniso (synCun P Y))))
    let syntaxFormula0113 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
        (synCfv (synChnqmap1 (synCun P Y)) (synCsn (synCuni (.cv p)))))
    let syntaxFormula0114 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
        (synCec (synCuni (.cv p)) (synChwniso (synCun P Y))))
    let syntaxFormula0115 : Wff := (synWb syntaxFormula0113 syntaxFormula0114)
    let syntaxFormula0116 : Wff := (.imp syntaxFormula0113 syntaxFormula0114)
    let syntaxFormula0117 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)))
    let syntaxClass0118 : Class :=
      (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (synCuni (.cv p))))
    let syntaxFormula0119 : Wff :=
      (.classEq syntaxClass0118
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0120 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p))
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0121 : Wff := (synWa syntaxFormula0106 syntaxFormula0117)
    let syntaxClass0122 : Class :=
      (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (synCuni (.cv q))))
    let syntaxFormula0123 : Wff :=
      (.classEq syntaxClass0122
        (synCec (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0124 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
        (synCec (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0125 : Wff :=
      (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0126 : Wff :=
      (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0127 : Wff :=
      (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))) (synCuni (.cv q)))
    let syntaxFormula0128 : Wff := (synWb syntaxFormula0126 syntaxFormula0127)
    let syntaxFormula0129 : Wff :=
      (synWa (.classMem (.cv x) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0130 : Wff :=
      (synWa (.classMem (.cv x) (synChwcn (synCun P Y)))
        (.classMem (.cv y) (synChwcn (synCun P Y))))
    let syntaxFormula0131 : Wff :=
      (synWa (.classMem (.cv x) (synChwcodes (synCun P Y)))
        (.classMem (.cv y) (synChwcodes (synCun P Y))))
    let syntaxFormula0132 : Wff :=
      (synWa syntaxFormula0129
        (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y)))
    let syntaxFormula0133 : Wff :=
      (synWiso (.cv h) (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
        (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y)))
    let syntaxFormula0134 : Wff := (synWex h syntaxFormula0133)
    let syntaxFormula0135 : Wff := (synWa syntaxFormula0131 syntaxFormula0134)
    let syntaxFormula0136 : Wff :=
      (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0137 : Wff :=
      (.imp (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (.cv y)))
    let syntaxFormula0138 : Wff := (.imp syntaxFormula0136 syntaxFormula0137)
    let syntaxFormula0139 : Wff :=
      (.imp (.classEq (.cv x) (synCuni (.cv p))) syntaxFormula0138)
    let syntaxFormula0140 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0138)
    let syntaxFormula0141 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) (.classMem (synCuni (.cv p)) (synCvv)))
    let syntaxFormula0142 : Wff :=
      (.imp syntaxFormula0127
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))))
    let syntaxFormula0143 : Wff := (.imp syntaxFormula0125 syntaxFormula0142)
    let syntaxFormula0144 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0143)
    let syntaxFormula0145 : Wff :=
      (.imp (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0144)
    have p0364 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P)) (.classMem (.cv u) (synChwcn (synCun P Y))))
        (.imp (.classMem (.cv u) (synChwcn P)) (.classMem (.cv u) (synChwcn P))) p0363
        p0010
    have p0366 := @gHnqmap1valcl (synCun P Y) (.cv u) p0001
    have p0367 :=
      @gSyl (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv u) (synChwcn (synCun P Y))) syntaxFormula0072 p0364 p0366
    have p0368 := @gSnelpw1 (.cv u) (synChwcn (synCun P Y))
    have p0369 :=
      @gSylibr (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv u) (synChwcn (synCun P Y)))
        (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn (synCun P Y)))) p0364 p0368
    have p0370 := @gHnqmap1fn (synCun P Y) p0001
    have p0371 :=
      @gJctil (.classMem (.cv u) (synChwcn P))
        (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn (synCun P Y))))
        (synWfn (synChnqmap1 (synCun P Y)) (synCpw1 (synChwcn (synCun P Y)))) p0369
        p0370
    have p0372 :=
      @gFnbrfvb (synCpw1 (synChwcn (synCun P Y))) (synCsn (.cv u))
        (synCec (.cv u) (synChwniso (synCun P Y))) (synChnqmap1 (synCun P Y))
    have p0373 :=
      @gSyl (.classMem (.cv u) (synChwcn P))
        (synWa (synWfn (synChnqmap1 (synCun P Y)) (synCpw1 (synChwcn (synCun P Y))))
          (.classMem (synCsn (.cv u)) (synCpw1 (synChwcn (synCun P Y)))))
        (synWb syntaxFormula0072 syntaxFormula0073) p0371 p0372
    have p0374 :=
      @gMpbid (.classMem (.cv u) (synChwcn P)) syntaxFormula0072 syntaxFormula0073 p0367
        p0373
    have p0375 :=
      @gJca (.classMem (.cv u) (synChwcn P)) syntaxFormula0071 syntaxFormula0073 p0359
        p0374
    have p0376 := @gSnex (.cv u)
    have p0377 := @gId (.classEq (.cv x) (synCsn (.cv u)))
    have p0378 :=
      @gBreq2d (.classEq (.cv x) (synCsn (.cv u))) (.cv x) (synCsn (.cv u))
        (synCec (.cv u) (synChwniso P)) (synCcnv (synChnqmap1 P)) p0377
    have p0380 :=
      @gBreq1d (.classEq (.cv x) (synCsn (.cv u))) (.cv x) (synCsn (.cv u))
        (synCec (.cv u) (synChwniso (synCun P Y))) (synChnqmap1 (synCun P Y)) p0377
    have p0381 :=
      @gAnbi12d (.classEq (.cv x) (synCsn (.cv u)))
        (synWbr (synCec (.cv u) (synChwniso P)) (synCcnv (synChnqmap1 P)) (.cv x))
        syntaxFormula0071 syntaxFormula0074 syntaxFormula0073 p0378 p0380
    have p0382 :=
      @gSpcev syntaxFormula0075 syntaxFormula0076 x (synCsn (.cv u)) dv_cache_0025
        dv_cache_0026 p0376 p0381
    have p0383 :=
      @gSyl (.classMem (.cv u) (synChwcn P)) syntaxFormula0076 syntaxFormula0077 p0375
        p0382
    have p0384 :=
      @gBrco x (synCec (.cv u) (synChwniso P))
        (synCec (.cv u) (synChwniso (synCun P Y))) (synChnqmap1 (synCun P Y))
        (synCcnv (synChnqmap1 P)) dv_cache_0027 dv_cache_0028 dv_cache_0029
        dv_cache_0030
    have p0385 :=
      @gSylibr (.classMem (.cv u) (synChwcn P)) syntaxFormula0077
        (synWbr (synCec (.cv u) (synChwniso P))
          (synCcom (synChnqmap1 (synCun P Y)) (synCcnv (synChnqmap1 P)))
          (synCec (.cv u) (synChwniso (synCun P Y))))
        p0383 p0384
    have p0386 := (Nominal.classEqRefl (synChnqinc P (synCun P Y)))
    have p0387 :=
      @gBreqi (synCec (.cv u) (synChwniso P))
        (synCec (.cv u) (synChwniso (synCun P Y))) (synChnqinc P (synCun P Y))
        (synCcom (synChnqmap1 (synCun P Y)) (synCcnv (synChnqmap1 P))) p0386
    have p0388 :=
      @gSylibr (.classMem (.cv u) (synChwcn P))
        (synWbr (synCec (.cv u) (synChwniso P))
          (synCcom (synChnqmap1 (synCun P Y)) (synCcnv (synChnqmap1 P)))
          (synCec (.cv u) (synChwniso (synCun P Y))))
        syntaxFormula0078 p0385 p0387
    have p0389 := @gHwnisoclasselhnordcl P (.cv u) hyp_cfbhnqinjcodecoverddndv_1
    have p0390 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.classMem (synCec (.cv u) (synChwniso P)) (synChnord P)))
        (.imp (.classMem (.cv u) (synChwcn P)) (.classMem (.cv u) (synChwcn P))) p0389
        p0010
    have p0391 := @gHnqincfn (synCun P Y) P p0360 hyp_cfbhnqinjcodecoverddndv_1 p0001
    have p0392 :=
      @gJctil (.classMem (.cv u) (synChwcn P))
        (.classMem (synCec (.cv u) (synChwniso P)) (synChnord P))
        (synWfn (synChnqinc P (synCun P Y)) (synChnord P)) p0390 p0391
    have p0393 :=
      @gFnbrfvb (synChnord P) (synCec (.cv u) (synChwniso P))
        (synCec (.cv u) (synChwniso (synCun P Y))) (synChnqinc P (synCun P Y))
    have p0394 :=
      @gSyl (.classMem (.cv u) (synChwcn P))
        (synWa (synWfn (synChnqinc P (synCun P Y)) (synChnord P))
          (.classMem (synCec (.cv u) (synChwniso P)) (synChnord P)))
        (synWb (.classEq
            (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
            (synCec (.cv u) (synChwniso (synCun P Y)))) syntaxFormula0078)
        p0392 p0393
    have p0395 :=
      @gMpbird (.classMem (.cv u) (synChwcn P))
        (.classEq (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
          (synCec (.cv u) (synChwniso (synCun P Y))))
        syntaxFormula0078 p0388 p0394
    have p0397 := @gHnqmap1valcl (synCfv (synC2nd) (.cv u)) (.cv u) p0023
    have p0398 :=
      @gSyl (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0079
        p0011 p0397
    have p0399 := @gSnelpw1 (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p0400 :=
      @gSylibr (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0080
        p0011 p0399
    have p0401 := @gHnqmap1fn (synCfv (synC2nd) (.cv u)) p0023
    have p0402 :=
      @gJctil (.classMem (.cv u) (synChwcn P)) syntaxFormula0080 syntaxFormula0081 p0400
        p0401
    have p0403 :=
      @gFnbrfvb (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) (synCsn (.cv u))
        (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0404 :=
      @gSyl (.classMem (.cv u) (synChwcn P)) syntaxFormula0082 syntaxFormula0084 p0402
        p0403
    have p0405 :=
      @gMpbid (.classMem (.cv u) (synChwcn P)) syntaxFormula0079 syntaxFormula0083 p0398
        p0404
    have p0406 :=
      @gBrcnv (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCsn (.cv u)) (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0407 :=
      @gSylibr (.classMem (.cv u) (synChwcn P)) syntaxFormula0083 syntaxFormula0085
        p0405 p0406
    have p0408 :=
      @gJca (.classMem (.cv u) (synChwcn P)) syntaxFormula0085 syntaxFormula0073 p0407
        p0374
    have p0411 :=
      @gBreq2d (.classEq (.cv x) (synCsn (.cv u))) (.cv x) (synCsn (.cv u))
        (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) p0377
    have p0414 :=
      @gAnbi12d (.classEq (.cv x) (synCsn (.cv u))) syntaxFormula0086 syntaxFormula0085
        syntaxFormula0074 syntaxFormula0073 p0411 p0380
    have p0415 :=
      @gSpcev syntaxFormula0087 syntaxFormula0088 x (synCsn (.cv u)) dv_cache_0025
        dv_cache_0031 p0376 p0414
    have p0416 :=
      @gSyl (.classMem (.cv u) (synChwcn P)) syntaxFormula0088 syntaxFormula0089 p0408
        p0415
    have p0417 :=
      @gBrco x (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (.cv u) (synChwniso (synCun P Y))) (synChnqmap1 (synCun P Y))
        (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) dv_cache_0032 dv_cache_0028
        dv_cache_0029 dv_cache_0033
    have p0418 :=
      @gSylibr (.classMem (.cv u) (synChwcn P)) syntaxFormula0089 syntaxFormula0091
        p0416 p0417
    have p0419 :=
      (Nominal.classEqRefl (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)))
    have p0420 :=
      @gBreqi (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (.cv u) (synChwniso (synCun P Y)))
        (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)) syntaxClass0090 p0419
    have p0421 :=
      @gSylibr (.classMem (.cv u) (synChwcn P)) syntaxFormula0091 syntaxFormula0092
        p0418 p0420
    have p0422 := @gSimpl syntaxFormula0093 syntaxFormula0094
    have p0423 :=
      @gBrco p (.cv x) (.cv y) (synChnqmap1 (synCun P Y))
        (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) dv_cache_0034 dv_cache_0035
        dv_cache_0036 dv_cache_0037
    have p0424 :=
      @gSylib syntaxFormula0095 syntaxFormula0093 syntaxFormula0098 p0422 p0423
    have p0425 := Nominal.ax17 syntaxFormula0095 p dv_cache_0038
    have p0426 := @gSimpl syntaxFormula0095 syntaxFormula0097
    have p0427 := @gSimpr syntaxFormula0093 syntaxFormula0094
    have p0428 :=
      @gBrco q (.cv x) (.cv z) (synChnqmap1 (synCun P Y))
        (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) dv_cache_0039 dv_cache_0040
        dv_cache_0041 dv_cache_0042
    have p0429 :=
      @gSylib syntaxFormula0095 syntaxFormula0094 syntaxFormula0101 p0427 p0428
    have p0430 := @gSyl syntaxFormula0102 syntaxFormula0095 syntaxFormula0101 p0426 p0429
    have p0431 := Nominal.ax17 syntaxFormula0102 q dv_cache_0043
    have p0432 := @gSimpl syntaxFormula0102 syntaxFormula0100
    have p0433 := @gSimpr syntaxFormula0095 syntaxFormula0097
    have p0434 := @gSyl syntaxFormula0103 syntaxFormula0102 syntaxFormula0097 p0432 p0433
    have p0435 :=
      @gSimpr syntaxFormula0096 (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y))
    have p0436 :=
      @gSyl syntaxFormula0103 syntaxFormula0097
        (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y)) p0434 p0435
    have p0439 :=
      @gFnfun (synCpw1 (synChwcn (synCun P Y))) (synChnqmap1 (synCun P Y))
    have p0440 := Nominal.mp p0370 p0439
    have p0441 := @gFunbrfv (.cv p) (.cv y) (synChnqmap1 (synCun P Y))
    have p0442 := Nominal.mp p0440 p0441
    have p0443 :=
      @gSyl syntaxFormula0103 (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y))
        (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p)) (.cv y)) p0436 p0442
    have p0444 :=
      @gEqcomd syntaxFormula0103 (synCfv (synChnqmap1 (synCun P Y)) (.cv p)) (.cv y)
        p0443
    have p0448 :=
      @gSimpl syntaxFormula0096 (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y))
    have p0449 := @gSyl syntaxFormula0103 syntaxFormula0097 syntaxFormula0096 p0434 p0448
    have p0450 := @gBrcnv (.cv x) (.cv p) (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0451 :=
      @gSylib syntaxFormula0103 syntaxFormula0096
        (synWbr (.cv p) (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv x)) p0449 p0450
    have p0453 :=
      @gFnfun (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0454 := Nominal.mp p0401 p0453
    have p0455 := @gFunbrfv (.cv p) (.cv x) (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0456 := Nominal.mp p0454 p0455
    have p0457 :=
      @gSyl syntaxFormula0103
        (synWbr (.cv p) (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv x))
        syntaxFormula0104 p0451 p0456
    have p0458 := @gSimpr syntaxFormula0102 syntaxFormula0100
    have p0459 :=
      @gSimpl syntaxFormula0099 (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z))
    have p0460 := @gSyl syntaxFormula0103 syntaxFormula0100 syntaxFormula0099 p0458 p0459
    have p0461 := @gBrcnv (.cv x) (.cv q) (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0462 :=
      @gSylib syntaxFormula0103 syntaxFormula0099
        (synWbr (.cv q) (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv x)) p0460 p0461
    have p0466 := @gFunbrfv (.cv q) (.cv x) (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0467 := Nominal.mp p0454 p0466
    have p0468 :=
      @gSyl syntaxFormula0103
        (synWbr (.cv q) (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv x))
        syntaxFormula0105 p0462 p0467
    have p0469 :=
      @gEqtr4d syntaxFormula0103
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p)) (.cv x)
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)) p0457 p0468
    have p0477 := @gBreldm (.cv p) (.cv x) (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0478 :=
      @gSyl syntaxFormula0103
        (synWbr (.cv p) (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv x))
        (.classMem (.cv p) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u))))) p0451
        p0477
    have p0480 :=
      @gFndm (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0481 := Nominal.mp p0401 p0480
    have p0482 :=
      @gSyl6eleq syntaxFormula0103 (.cv p)
        (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) p0478 p0481
    have p0488 := @gBreldm (.cv q) (.cv x) (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0489 :=
      @gSyl syntaxFormula0103
        (synWbr (.cv q) (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv x))
        (.classMem (.cv q) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u))))) p0462
        p0488
    have p0493 :=
      @gSyl6eleq syntaxFormula0103 (.cv q)
        (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) p0489 p0481
    have p0494 :=
      @gJca syntaxFormula0103
        (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))) p0482
        p0493
    have p0495 :=
      @gSimpl (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    have p0496 := @gHnwpw1argcl (synChwcn (synCfv (synC2nd) (.cv u))) p
    have p0497 :=
      @gSimprd (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0496
    have p0498 :=
      @gSyl syntaxFormula0106
        (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0495 p0497
    have p0499 :=
      @gFveq2d syntaxFormula0106 (.cv p) (synCsn (synCuni (.cv p)))
        (synChnqmap1 (synCun P Y)) p0498
    have p0502 :=
      @gSimpld (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p0496
    have p0503 :=
      @gSyl syntaxFormula0106
        (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u)))) p0495
        p0502
    have p0504 := @gHwcnraw a (synCfv (synC2nd) (.cv u))
    have p0505 := @gHwcnpair a (synCfv (synC2nd) (.cv u))
    have p0506 :=
      @gEleq1d (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) (.cv a)
        (synCop (synCfv (synC1st) (.cv a)) (synCfv (synC2nd) (.cv a)))
        (synChwcodes (synCfv (synC2nd) (.cv u))) p0505
    have p0507 :=
      @gMpbid (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv a) (synChwcodes (synCfv (synC2nd) (.cv u)))) syntaxFormula0107
        p0504 p0506
    have p0510 :=
      @gElhwcodes (synCfv (synC2nd) (.cv u)) (synCfv (synC2nd) (.cv a))
        (synCfv (synC1st) (.cv a)) dv_cache_0044 p0291 p0292
    have p0511 := @gBiimpi syntaxFormula0107 syntaxFormula0108 p0510
    have p0512 :=
      @gSyl (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0107 syntaxFormula0108 p0507 p0511
    have p0513 :=
      @gSimpld (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCfv (synC2nd) (.cv u))) p0512
    have p0523 :=
      @gSimprd (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCfv (synC2nd) (.cv u))) p0512
    have p0524 := @gHwcnbase u P dv_cache_0001
    have p0525 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P)) (synWss (synCfv (synC2nd) (.cv u)) P))
        (.imp (.classMem (.cv u) (synChwcn P)) (.classMem (.cv u) (synChwcn P))) p0524
        p0010
    have p0527 :=
      @gSyl6ss (.classMem (.cv u) (synChwcn P)) (synCfv (synC2nd) (.cv u)) P
        (synCun P Y) p0525 p0360
    have p0528 :=
      @gA1d (.classMem (.cv u) (synChwcn P))
        (synWss (synCfv (synC2nd) (.cv u)) (synCun P Y))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) p0527
    have p0529 :=
      @gSstr (synCfv (synC2nd) (.cv a)) (synCfv (synC2nd) (.cv u)) (synCun P Y)
    have p0530 :=
      @gEx (synWss (synCfv (synC2nd) (.cv a)) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv u)) (synCun P Y))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y)) p0529
    have p0531 :=
      @gSyl9 (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWss (synCfv (synC2nd) (.cv u)) (synCun P Y))
        (synWss (synCfv (synC2nd) (.cv a)) (synCfv (synC2nd) (.cv u)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y)) p0528 p0530
    have p0532 :=
      @gSyl5 (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWss (synCfv (synC2nd) (.cv a)) (synCfv (synC2nd) (.cv u)))
        (.classMem (.cv u) (synChwcn P))
        (.imp (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
          (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y)))
        p0523 p0531
    have p0533 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y)) p0532
    have p0534 :=
      @g_pm3_2
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y))
    have p0535 :=
      @gSyl9 (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y))
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        syntaxFormula0109 p0533 p0534
    have p0536 :=
      @gSyl5 (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (.classMem (.cv u) (synChwcn P))
        (.imp (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0109)
        p0513 p0535
    have p0537 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0109
        p0536
    have p0540 :=
      @gElhwcodes (synCun P Y) (synCfv (synC2nd) (.cv a)) (synCfv (synC1st) (.cv a))
        dv_cache_0045 p0291 p0292
    have p0541 := @gBiimpri syntaxFormula0110 syntaxFormula0109 p0540
    have p0542 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0109
        syntaxFormula0110 p0537 p0541
    have p0544 :=
      @gEleq1d (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) (.cv a)
        (synCop (synCfv (synC1st) (.cv a)) (synCfv (synC2nd) (.cv a)))
        (synChwcodes (synCun P Y)) p0505
    have p0545 :=
      @gBiimprd (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv a) (synChwcodes (synCun P Y))) syntaxFormula0110 p0544
    have p0546 :=
      @gSylcom (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0110
        (.classMem (.cv a) (synChwcodes (synCun P Y))) p0542 p0545
    have p0547 := @gHwcnsupp a (synCfv (synC2nd) (.cv u))
    have p0548 :=
      @g_pm3_2 (.classMem (.cv a) (synChwcodes (synCun P Y))) syntaxFormula0065
    have p0549 :=
      @gSyl5 (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0065 (.classMem (.cv a) (synChwcodes (synCun P Y)))
        syntaxFormula0111 p0547 p0548
    have p0550 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv a) (synChwcodes (synCun P Y)))
        (.imp (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0111)
        p0546 p0549
    have p0551 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0111
        p0550
    have p0552 := @gElhwcn a (synCun P Y)
    have p0553 :=
      @gBiimpri (.classMem (.cv a) (synChwcn (synCun P Y))) syntaxFormula0111 p0552
    have p0554 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0111
        (.classMem (.cv a) (synChwcn (synCun P Y))) p0551 p0553
    have p0555 :=
      @gSsrdv (.classMem (.cv u) (synChwcn P)) a
        (synChwcn (synCfv (synC2nd) (.cv u))) (synChwcn (synCun P Y)) dv_cache_0046
        dv_cache_0047 dv_cache_0048 p0554
    have p0556 :=
      @gSseld (.classMem (.cv u) (synChwcn P)) (synChwcn (synCfv (synC2nd) (.cv u)))
        (synChwcn (synCun P Y)) (synCuni (.cv p)) p0555
    have p0557 :=
      @gSyl5 syntaxFormula0106
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv u) (synChwcn P))
        (.classMem (synCuni (.cv p)) (synChwcn (synCun P Y))) p0503 p0556
    have p0558 := @gHnqmap1valcl (synCun P Y) (synCuni (.cv p)) p0001
    have p0559 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0106
        (.classMem (synCuni (.cv p)) (synChwcn (synCun P Y))) syntaxFormula0112 p0557
        p0558
    have p0560 :=
      @gEqeq2 (synCfv (synChnqmap1 (synCun P Y)) (synCsn (synCuni (.cv p))))
        (synCec (synCuni (.cv p)) (synChwniso (synCun P Y)))
        (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
    have p0561 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0106 syntaxFormula0112
        syntaxFormula0115 p0559 p0560
    have p0562 := @gBi1 syntaxFormula0113 syntaxFormula0114
    have p0563 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0106 syntaxFormula0115
        syntaxFormula0116 p0561 p0562
    have p0564 :=
      @gMpdi (.classMem (.cv u) (synChwcn P)) syntaxFormula0106 syntaxFormula0113
        syntaxFormula0114 p0499 p0563
    have p0565 :=
      @gAdantrd (.classMem (.cv u) (synChwcn P)) syntaxFormula0106 syntaxFormula0114
        syntaxFormula0117 p0564
    have p0570 :=
      @gFveq2d syntaxFormula0106 (.cv p) (synCsn (synCuni (.cv p)))
        (synChnqmap1 (synCfv (synC2nd) (.cv u))) p0498
    have p0575 := @gHnqmap1valcl (synCfv (synC2nd) (.cv u)) (synCuni (.cv p)) p0023
    have p0576 :=
      @gSyl syntaxFormula0106
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0119 p0503 p0575
    have p0577 :=
      @gEqtrd syntaxFormula0106
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p)) syntaxClass0118
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))) p0570
        p0576
    have p0578 := @gAdantr syntaxFormula0106 syntaxFormula0120 syntaxFormula0117 p0577
    have p0579 :=
      @gEqcomd syntaxFormula0121
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p))
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))) p0578
    have p0580 := @gSimpr syntaxFormula0106 syntaxFormula0117
    have p0581 :=
      @gEqtrd syntaxFormula0121
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)) p0579 p0580
    have p0582 :=
      @gSimpr (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    have p0583 := @gHnwpw1argcl (synChwcn (synCfv (synC2nd) (.cv u))) q
    have p0584 :=
      @gSimprd (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0583
    have p0585 :=
      @gSyl syntaxFormula0106
        (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0582 p0584
    have p0586 :=
      @gFveq2d syntaxFormula0106 (.cv q) (synCsn (synCuni (.cv q)))
        (synChnqmap1 (synCfv (synC2nd) (.cv u))) p0585
    have p0589 :=
      @gSimpld (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p0583
    have p0590 :=
      @gSyl syntaxFormula0106
        (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u)))) p0582
        p0589
    have p0591 := @gHnqmap1valcl (synCfv (synC2nd) (.cv u)) (synCuni (.cv q)) p0023
    have p0592 :=
      @gSyl syntaxFormula0106
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0123 p0590 p0591
    have p0593 :=
      @gEqtrd syntaxFormula0106
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)) syntaxClass0122
        (synCec (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u)))) p0586
        p0592
    have p0594 := @gAdantr syntaxFormula0106 syntaxFormula0124 syntaxFormula0117 p0593
    have p0595 :=
      @gEqtrd syntaxFormula0121
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
        (synCec (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u)))) p0581
        p0594
    have p0604 :=
      @gJca syntaxFormula0106
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u)))) p0503
        p0590
    have p0605 := @gAdantr syntaxFormula0106 syntaxFormula0125 syntaxFormula0117 p0604
    have p0606 :=
      @gHwnisoclasseqbcl (synCfv (synC2nd) (.cv u)) (synCuni (.cv p))
        (synCuni (.cv q)) p0023
    have p0607 := @gSyl syntaxFormula0121 syntaxFormula0125 syntaxFormula0128 p0605 p0606
    have p0608 := @gBiimpd syntaxFormula0121 syntaxFormula0126 syntaxFormula0127 p0607
    have p0609 := @gMpd syntaxFormula0121 syntaxFormula0126 syntaxFormula0127 p0595 p0608
    have p0620 :=
      @gSimpl (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
    have p0621 := @gElex (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p0622 :=
      @gSyl syntaxFormula0125
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv p)) (synCvv)) p0620 p0621
    have p0623 :=
      @gSimpr (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
    have p0624 := @gElex (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p0625 :=
      @gSyl syntaxFormula0125
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv q)) (synCvv)) p0623 p0624
    have p0626 :=
      @gJca syntaxFormula0125 (.classMem (synCuni (.cv p)) (synCvv))
        (.classMem (synCuni (.cv q)) (synCvv)) p0622 p0625
    have p0627 := @gNfcv y (synCuni (.cv q)) dv_cache_0049
    have p0628 := @gIssetf y (synCuni (.cv q)) p0627
    have p0629 := @gNfcv x (synCuni (.cv p)) dv_cache_0050
    have p0630 := @gIssetf x (synCuni (.cv p)) p0629
    have p0631 :=
      @gSimpl (.classMem (.cv x) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u))))
    have p0632 :=
      @gSseld (.classMem (.cv u) (synChwcn P)) (synChwcn (synCfv (synC2nd) (.cv u)))
        (synChwcn (synCun P Y)) (.cv x) p0555
    have p0633 :=
      @gSyl5 syntaxFormula0129
        (.classMem (.cv x) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv u) (synChwcn P)) (.classMem (.cv x) (synChwcn (synCun P Y)))
        p0631 p0632
    have p0634 :=
      @gSimpr (.classMem (.cv x) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u))))
    have p0635 :=
      @gSseld (.classMem (.cv u) (synChwcn P)) (synChwcn (synCfv (synC2nd) (.cv u)))
        (synChwcn (synCun P Y)) (.cv y) p0555
    have p0636 :=
      @gSyl5 syntaxFormula0129
        (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv u) (synChwcn P)) (.classMem (.cv y) (synChwcn (synCun P Y)))
        p0634 p0635
    have p0637 :=
      @gJcad (.classMem (.cv u) (synChwcn P)) syntaxFormula0129
        (.classMem (.cv x) (synChwcn (synCun P Y)))
        (.classMem (.cv y) (synChwcn (synCun P Y))) p0633 p0636
    have p0638 :=
      @gAdantrd (.classMem (.cv u) (synChwcn P)) syntaxFormula0129 syntaxFormula0130
        (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y)) p0637
    have p0639 := @gHwcnraw x (synCun P Y)
    have p0640 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0129
        (.classMem (.cv x) (synChwcn (synCun P Y)))
        (.classMem (.cv x) (synChwcodes (synCun P Y))) p0633 p0639
    have p0641 := @gHwcnraw y (synCun P Y)
    have p0642 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0129
        (.classMem (.cv y) (synChwcn (synCun P Y)))
        (.classMem (.cv y) (synChwcodes (synCun P Y))) p0636 p0641
    have p0643 :=
      @gJcad (.classMem (.cv u) (synChwcn P)) syntaxFormula0129
        (.classMem (.cv x) (synChwcodes (synCun P Y)))
        (.classMem (.cv y) (synChwcodes (synCun P Y))) p0640 p0642
    have p0644 :=
      @gAdantrd (.classMem (.cv u) (synChwcn P)) syntaxFormula0129 syntaxFormula0131
        (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y)) p0643
    have p0645 :=
      @gSimpr syntaxFormula0129
        (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
    have p0646 := @gHwnisohwisob y x (synCfv (synC2nd) (.cv u)) dv_cache_0007
    have p0647 :=
      @gBiimpi (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
        (synWa syntaxFormula0129
          (synWbr (.cv x) (synChwiso (synCfv (synC2nd) (.cv u))) (.cv y)))
        p0646
    have p0648 :=
      @gSimprd (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
        syntaxFormula0129
        (synWbr (.cv x) (synChwiso (synCfv (synC2nd) (.cv u))) (.cv y)) p0647
    have p0649 :=
      @gSyl syntaxFormula0132
        (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
        (synWbr (.cv x) (synChwiso (synCfv (synC2nd) (.cv u))) (.cv y)) p0645 p0648
    have p0650 :=
      @gBrhwisoany y x (synCfv (synC2nd) (.cv u)) h dv_cache_0051 dv_cache_0052
        dv_cache_0053
    have p0651 :=
      @gSylib syntaxFormula0132
        (synWbr (.cv x) (synChwiso (synCfv (synC2nd) (.cv u))) (.cv y))
        (synWa (synWa (.classMem (.cv x) (synChwcodes (synCfv (synC2nd) (.cv u))))
            (.classMem (.cv y) (synChwcodes (synCfv (synC2nd) (.cv u))))) syntaxFormula0134)
        p0649 p0650
    have p0652 :=
      @gSimprd syntaxFormula0132
        (synWa (.classMem (.cv x) (synChwcodes (synCfv (synC2nd) (.cv u))))
          (.classMem (.cv y) (synChwcodes (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0134 p0651
    have p0653 := @g_pm3_2 syntaxFormula0131 syntaxFormula0134
    have p0654 :=
      @gSyl5 syntaxFormula0132 syntaxFormula0134 syntaxFormula0131 syntaxFormula0135
        p0652 p0653
    have p0655 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0132 syntaxFormula0131
        (.imp syntaxFormula0132 syntaxFormula0135) p0644 p0654
    have p0656 :=
      @gPm243d (.classMem (.cv u) (synChwcn P)) syntaxFormula0132 syntaxFormula0135
        p0655
    have p0657 :=
      @gBrhwisoany y x (synCun P Y) h dv_cache_0054 dv_cache_0052 dv_cache_0053
    have p0658 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P)) syntaxFormula0132 syntaxFormula0135
        (synWbr (.cv x) (synChwiso (synCun P Y)) (.cv y)) p0656 p0657
    have p0659 :=
      @gJcad (.classMem (.cv u) (synChwcn P)) syntaxFormula0132 syntaxFormula0130
        (synWbr (.cv x) (synChwiso (synCun P Y)) (.cv y)) p0638 p0658
    have p0660 := @gHwnisohwisob y x (synCun P Y) dv_cache_0007
    have p0661 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P)) syntaxFormula0132
        (synWa syntaxFormula0130 (synWbr (.cv x) (synChwiso (synCun P Y)) (.cv y)))
        (synWbr (.cv x) (synChwniso (synCun P Y)) (.cv y)) p0659 p0660
    have p0662 :=
      @gExp3a (.classMem (.cv u) (synChwcn P)) syntaxFormula0129
        (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
        (synWbr (.cv x) (synChwniso (synCun P Y)) (.cv y)) p0661
    have p0663 :=
      @gEleq1 (.cv x) (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p0664 := @gBiid (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u))))
    have p0665 :=
      @gA1i
        (synWb (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u))))
          (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classEq (.cv x) (synCuni (.cv p))) p0664
    have p0666 :=
      @gAnbi12d (.classEq (.cv x) (synCuni (.cv p)))
        (.classMem (.cv x) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u)))) p0663 p0665
    have p0667 :=
      @gBreq1 (.cv x) (synCuni (.cv p)) (.cv y)
        (synChwniso (synCfv (synC2nd) (.cv u)))
    have p0668 := @gBreq1 (.cv x) (synCuni (.cv p)) (.cv y) (synChwniso (synCun P Y))
    have p0669 :=
      @gImbi12d (.classEq (.cv x) (synCuni (.cv p)))
        (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
        (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
        (synWbr (.cv x) (synChwniso (synCun P Y)) (.cv y))
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (.cv y)) p0667 p0668
    have p0670 :=
      @gImbi12d (.classEq (.cv x) (synCuni (.cv p))) syntaxFormula0129 syntaxFormula0136
        (.imp (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
          (synWbr (.cv x) (synChwniso (synCun P Y)) (.cv y)))
        syntaxFormula0137 p0666 p0669
    have p0671 :=
      @gSyl5ibcom (.classMem (.cv u) (synChwcn P))
        (.imp syntaxFormula0129
          (.imp (synWbr (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
            (synWbr (.cv x) (synChwniso (synCun P Y)) (.cv y))))
        (.classEq (.cv x) (synCuni (.cv p))) syntaxFormula0138 p0662 p0670
    have p0672 :=
      @gAlrimiv (.classMem (.cv u) (synChwcn P)) syntaxFormula0139 x dv_cache_0055 p0671
    have p0673 := @gNfv syntaxFormula0138 x dv_cache_0056
    have p0674 :=
      @gN1923 (.classEq (.cv x) (synCuni (.cv p))) syntaxFormula0138 x p0673
    have p0675 :=
      @gSylib (.classMem (.cv u) (synChwcn P)) (.all x syntaxFormula0139)
        (.imp (synWex x (.classEq (.cv x) (synCuni (.cv p)))) syntaxFormula0138) p0672
        p0674
    have p0676 :=
      @gSyl5bi (.classMem (synCuni (.cv p)) (synCvv))
        (synWex x (.classEq (.cv x) (synCuni (.cv p))))
        (.classMem (.cv u) (synChwcn P)) syntaxFormula0138 p0630 p0675
    have p0677 := @gElex (synCuni (.cv p)) (synCvv)
    have p0678 :=
      @gA1ii (.imp (.classMem (.cv u) (synChwcn P)) syntaxFormula0140) syntaxFormula0141
        p0676 p0677
    have p0679 :=
      @gBiid (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
    have p0680 :=
      @gA1i
        (synWb (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
          (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classEq (.cv y) (synCuni (.cv q))) p0679
    have p0681 :=
      @gEleq1 (.cv y) (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p0682 :=
      @gAnbi12d (.classEq (.cv y) (synCuni (.cv q)))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv y) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u)))) p0680
        p0681
    have p0683 :=
      @gBreq2 (.cv y) (synCuni (.cv q)) (synCuni (.cv p))
        (synChwniso (synCfv (synC2nd) (.cv u)))
    have p0684 :=
      @gBreq2 (.cv y) (synCuni (.cv q)) (synCuni (.cv p)) (synChwniso (synCun P Y))
    have p0685 :=
      @gImbi12d (.classEq (.cv y) (synCuni (.cv q)))
        (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv y))
        syntaxFormula0127 (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (.cv y))
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))) p0683
        p0684
    have p0686 :=
      @gImbi12d (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0136 syntaxFormula0125
        syntaxFormula0137 syntaxFormula0142 p0682 p0685
    have p0687 :=
      @gImbi2d (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0138 syntaxFormula0143
        (.classMem (synCuni (.cv p)) (synCvv)) p0686
    have p0688 :=
      @gSyl5ibcom (.classMem (.cv u) (synChwcn P)) syntaxFormula0140
        (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0144 p0678 p0687
    have p0689 :=
      @gAlrimiv (.classMem (.cv u) (synChwcn P)) syntaxFormula0145 y dv_cache_0057 p0688
    have p0690 := @gNfcv y (synCuni (.cv p)) dv_cache_0058
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

/-- Checked nominal proof certificate identified upstream as `g_cfbhnqinjcodecoverddndv_stage3`. -/
@[expose]
noncomputable def gCfbhnqinjcodecoverddndvStage3 (u : Var) (P : Class) (k : Var)
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
    have dv_cache_0055 : x ∉ ((Wff.classMem (.cv u) (synChwcn P))).fv := by
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
    have dv_cache_0057 : y ∉ ((Wff.classMem (.cv u) (synChwcn P))).fv := by
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
    have dv_cache_0059 : y ∉ ((synCvv)).fv := by
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
        ((Wff.imp (synWa
              (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
              (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))) (.imp
              (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))
                (synCuni (.cv q))) (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y))
                (synCuni (.cv q)))))).fv :=
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
    have dv_cache_0061 : q ∉ ((Wff.classMem (.cv u) (synChwcn P))).fv := by
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
    have dv_cache_0063 : p ∉ ((Wff.classMem (.cv u) (synChwcn P))).fv := by
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
    have dv_cache_0065 : z ∉ ((Wff.classMem (.cv u) (synChwcn P))).fv := by
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
        ((synCcom (synChnqmap1 (synCun P Y))
            (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))).fv :=
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
        ((synCcom (synChnqmap1 (synCun P Y))
            (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))).fv :=
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
        ((synCcom (synChnqmap1 (synCun P Y))
            (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))).fv :=
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
      x ∉ ((synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))).fv :=
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
        ((synCop (synCsn (.cv a)) (synCima (synChwniso (synCfv (synC2nd) (.cv u)))
              (synCsn (.cv a))))).fv :=
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
        ((synCsymdif (synCins2 (synCsset)) (synCins3 (synCcom (synCsset)
                (synCcnv (synCsi (synChwniso (synCfv (synC2nd) (.cv u))))))))).fv :=
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
    have dv_cache_0075 : b ∉ ((synCsn (.cv x))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_b_ne_x,
            not_false_eq_true])
    have dv_cache_0076 : b ∉ ((synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)).fv := by
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
        ((synWb (.classMem (synCop (synCsn (.cv x)) (synCop (synCsn (.cv a))
                  (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))))
              (synCins3 (synCcom (synCsset)
                  (synCcnv (synCsi (synChwniso (synCfv (synC2nd) (.cv u))))))))
            (.classMem (synCop (synCsn (.cv x)) (synCsn (.cv a))) (synCcom (synCsset)
                (synCcnv (synCsi (synChwniso (synCfv (synC2nd) (.cv u))))))))).fv :=
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
    have dv_cache_0080 : y ∉ ((synChwniso (synCfv (synC2nd) (.cv u)))).fv := by
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
    have dv_cache_0081 : y ∉ ((synWbr (.cv t) (synCsset) (synCsn (.cv a)))).fv := by
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
    have dv_cache_0082 : t ∉ ((synCsn (.cv y))).fv := by
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
        ((synWa (.classMem (.cv y) (synCsn (.cv a)))
            (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x)))).fv :=
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
    have dv_cache_0084 : t ∉ ((synCsn (.cv x))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
            not_false_eq_true])
    have dv_cache_0085 : t ∉ ((synCsn (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_a,
            not_false_eq_true])
    have dv_cache_0086 : t ∉ ((synCsset)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0087 :
      t ∉ ((synCcnv (synCsi (synChwniso (synCfv (synC2nd) (.cv u)))))).fv := by
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
    have dv_cache_0088 : y ∉ ((synCsn (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_a,
            not_false_eq_true])
    have dv_cache_0089 : x ∉ ((synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)).fv := by
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
      y ∉ ((synCima (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x))).fv := by
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
    have dv_cache_0091 : x ∉ ((synCvv)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0092 :
      x ∉ ((synCimage (synChwniso (synCfv (synC2nd) (.cv u))))).fv := by
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
      y ∉ ((synCimage (synChwniso (synCfv (synC2nd) (.cv u))))).fv := by
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
      (synCcom (synChnqmap1 (synCun P Y))
        (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0092 : Wff :=
      (synWbr (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y))
        (synCec (.cv u) (synChwniso (synCun P Y))))
    let syntaxFormula0093 : Wff := (synWbr (.cv x) syntaxClass0090 (.cv y))
    let syntaxFormula0094 : Wff := (synWbr (.cv x) syntaxClass0090 (.cv z))
    let syntaxFormula0095 : Wff := (synWa syntaxFormula0093 syntaxFormula0094)
    let syntaxFormula0096 : Wff :=
      (synWbr (.cv x) (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) (.cv p))
    let syntaxFormula0097 : Wff :=
      (synWa syntaxFormula0096 (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y)))
    let syntaxFormula0098 : Wff := (synWex p syntaxFormula0097)
    let syntaxFormula0099 : Wff :=
      (synWbr (.cv x) (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))) (.cv q))
    let syntaxFormula0100 : Wff :=
      (synWa syntaxFormula0099 (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z)))
    let syntaxFormula0101 : Wff := (synWex q syntaxFormula0100)
    let syntaxFormula0102 : Wff := (synWa syntaxFormula0095 syntaxFormula0097)
    let syntaxFormula0103 : Wff := (synWa syntaxFormula0102 syntaxFormula0100)
    let syntaxFormula0106 : Wff :=
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))))
    let syntaxFormula0114 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
        (synCec (synCuni (.cv p)) (synChwniso (synCun P Y))))
    let syntaxFormula0117 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)))
    let syntaxFormula0121 : Wff := (synWa syntaxFormula0106 syntaxFormula0117)
    let syntaxFormula0125 : Wff :=
      (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0127 : Wff :=
      (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))) (synCuni (.cv q)))
    let syntaxFormula0141 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) (.classMem (synCuni (.cv p)) (synCvv)))
    let syntaxFormula0142 : Wff :=
      (.imp syntaxFormula0127
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))))
    let syntaxFormula0143 : Wff := (.imp syntaxFormula0125 syntaxFormula0142)
    let syntaxFormula0144 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0143)
    let syntaxFormula0145 : Wff :=
      (.imp (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0144)
    let syntaxFormula0146 : Wff :=
      (.imp (.classMem (synCuni (.cv q)) (synCvv)) syntaxFormula0144)
    let syntaxFormula0147 : Wff :=
      (.imp (.classMem (.cv u) (synChwcn P)) syntaxFormula0146)
    let syntaxFormula0148 : Wff :=
      (.imp (.classMem (synCuni (.cv q)) (synCvv)) (.classMem (synCuni (.cv q)) (synCvv)))
    let syntaxFormula0149 : Wff :=
      (synWa (.classMem (synCuni (.cv p)) (synCvv)) (.classMem (synCuni (.cv q)) (synCvv)))
    let syntaxFormula0150 : Wff :=
      (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCun P Y)))
        (.classMem (synCuni (.cv q)) (synChwcn (synCun P Y))))
    let syntaxFormula0151 : Wff :=
      (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCun P Y)))
        (synCec (synCuni (.cv q)) (synChwniso (synCun P Y))))
    let syntaxFormula0152 : Wff :=
      (synWb syntaxFormula0151
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))))
    let syntaxFormula0153 : Wff :=
      (synWb (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q)))
        syntaxFormula0151)
    let syntaxFormula0154 : Wff :=
      (.imp (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q)))
        syntaxFormula0151)
    let syntaxFormula0155 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
        (synCec (synCuni (.cv q)) (synChwniso (synCun P Y))))
    let syntaxFormula0156 : Wff := (synWb syntaxFormula0114 syntaxFormula0155)
    let syntaxFormula0157 : Wff := (.imp syntaxFormula0114 syntaxFormula0155)
    let syntaxFormula0158 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (synCsn (synCuni (.cv q))))
        (synCec (synCuni (.cv q)) (synChwniso (synCun P Y))))
    let syntaxFormula0159 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv q))
        (synCfv (synChnqmap1 (synCun P Y)) (synCsn (synCuni (.cv q)))))
    let syntaxFormula0160 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv q))
        (synCec (synCuni (.cv q)) (synChwniso (synCun P Y))))
    let syntaxFormula0161 : Wff := (synWb syntaxFormula0159 syntaxFormula0160)
    let syntaxFormula0162 : Wff := (.imp syntaxFormula0159 syntaxFormula0160)
    let syntaxFormula0163 : Wff :=
      (.classEq (synCec (synCuni (.cv q)) (synChwniso (synCun P Y)))
        (synCfv (synChnqmap1 (synCun P Y)) (.cv q)))
    let syntaxFormula0164 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
        (synCfv (synChnqmap1 (synCun P Y)) (.cv q)))
    let syntaxFormula0165 : Wff := (synWb syntaxFormula0155 syntaxFormula0164)
    let syntaxFormula0166 : Wff := (.imp syntaxFormula0155 syntaxFormula0164)
    let syntaxFormula0167 : Wff := (.imp syntaxFormula0117 syntaxFormula0164)
    let syntaxFormula0168 : Wff :=
      (synWb (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv p)))
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q))))
    let syntaxFormula0169 : Wff :=
      (.imp (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv p)))
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q))))
    let syntaxFormula0170 : Wff := (.imp syntaxFormula0100 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0171 : Wff := (.all q syntaxFormula0102)
    let syntaxFormula0172 : Wff := (.all q syntaxFormula0170)
    let syntaxFormula0173 : Wff :=
      (.imp syntaxFormula0101 (synWex q (.classEq (.cv y) (.cv z))))
    let syntaxFormula0174 : Wff := (.imp syntaxFormula0097 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0175 : Wff := (.all p syntaxFormula0095)
    let syntaxFormula0176 : Wff := (.all p syntaxFormula0174)
    let syntaxFormula0177 : Wff :=
      (.imp syntaxFormula0098 (synWex p (.classEq (.cv y) (.cv z))))
    let syntaxFormula0178 : Wff := (.imp syntaxFormula0095 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0179 : Wff := (.all z syntaxFormula0178)
    let syntaxFormula0180 : Wff := (.all y syntaxFormula0179)
    let syntaxFormula0181 : Wff := (.all x syntaxFormula0180)
    let syntaxFormula0182 : Wff :=
      (synWss (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCun P Y))))
    let syntaxFormula0183 : Wff :=
      (synWss (synCrn (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (synCdm (synChnqmap1 (synCun P Y))))
    let syntaxClass0184 : Class := (synCdm syntaxClass0090)
    let syntaxFormula0185 : Wff :=
      (.classEq syntaxClass0184
        (synCdm (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))))
    let syntaxFormula0186 : Wff :=
      (.classEq (synCdm (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)))
        (synChnord (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0187 : Wff :=
      (synWfn (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y))
        (synChnord (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0188 : Wff :=
      (.classMem (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0189 : Wff := (synWa syntaxFormula0187 syntaxFormula0188)
    let syntaxClass0190 : Class :=
      (synCfv (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y))
        (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0191 : Wff :=
      (.classEq syntaxClass0190 (synCec (.cv u) (synChwniso (synCun P Y))))
    let syntaxFormula0192 : Wff := (synWb syntaxFormula0191 syntaxFormula0092)
    let syntaxFormula0193 : Wff :=
      (.classEq (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
        syntaxClass0190)
    let syntaxClass0194 : Class :=
      (synCres (synCimage (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0195 : Wff :=
      (.classMem (synCsn (.cv a)) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxClass0196 : Class :=
      (synCfv (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCsn (.cv a)))
    let syntaxClass0197 : Class :=
      (synCop (synCsn (.cv a))
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
    let syntaxClass0198 : Class :=
      (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCfv (synC2nd) (.cv u))))))
    let syntaxClass0199 : Class := (synCins3 syntaxClass0198)
    let syntaxClass0200 : Class := (synCsymdif (synCins2 (synCsset)) syntaxClass0199)
    let syntaxClass0201 : Class := (synCop (synCsn (.cv x)) syntaxClass0197)
    let syntaxFormula0202 : Wff :=
      (synWbr (synCsn (.cv x)) (synCsset)
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
    let syntaxFormula0203 : Wff :=
      (.classMem (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCvv))
    let syntaxFormula0204 : Wff :=
      (.classMem (.cv x)
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
    let syntaxFormula0205 : Wff := (.classMem syntaxClass0201 (synCins2 (synCsset)))
    let syntaxClass0206 : Class :=
      (synCop (.cv b) (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
    let syntaxFormula0207 : Wff := (.classMem syntaxClass0206 (synCvv))
    let syntaxFormula0208 : Wff :=
      (.classMem (synCop (.cv b) (synCsn (.cv a))) syntaxClass0198)
    let syntaxClass0209 : Class := (synCop (.cv b) syntaxClass0197)
    let syntaxFormula0210 : Wff := (.classMem syntaxClass0209 syntaxClass0199)
    let syntaxFormula0211 : Wff := (synWa syntaxFormula0208 syntaxFormula0207)
    let syntaxFormula0212 : Wff := (.classMem syntaxClass0201 syntaxClass0199)
    let syntaxFormula0213 : Wff :=
      (.classMem (synCop (synCsn (.cv x)) (synCsn (.cv a))) syntaxClass0198)
    let syntaxFormula0214 : Wff := (synWb syntaxFormula0212 syntaxFormula0213)
    let syntaxFormula0215 : Wff :=
      (.imp (.classEq (.cv b) (synCsn (.cv x))) syntaxFormula0214)
    let syntaxFormula0216 : Wff := (.classMem syntaxClass0197 (synCvv))
    let syntaxFormula0217 : Wff :=
      (synWbr (synCsn (.cv x))
        (synCcnv (synCsi (synChwniso (synCfv (synC2nd) (.cv u))))) (.cv t))
    let syntaxFormula0218 : Wff :=
      (synWa (.classEq (.cv t) (synCsn (.cv y)))
        (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x)))
    let syntaxFormula0219 : Wff := (synWex y syntaxFormula0218)
    let syntaxFormula0220 : Wff :=
      (synWa syntaxFormula0217 (synWbr (.cv t) (synCsset) (synCsn (.cv a))))
    let syntaxFormula0221 : Wff :=
      (synWa syntaxFormula0218 (synWbr (.cv t) (synCsset) (synCsn (.cv a))))
    let syntaxFormula0222 : Wff := (synWex y syntaxFormula0221)
    let syntaxFormula0223 : Wff :=
      (synWa (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x))
        (synWbr (.cv t) (synCsset) (synCsn (.cv a))))
    let syntaxFormula0224 : Wff :=
      (synWa (.classEq (.cv t) (synCsn (.cv y))) syntaxFormula0223)
    let syntaxFormula0225 : Wff :=
      (synWa (.classMem (.cv y) (synCsn (.cv a)))
        (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x)))
    let syntaxFormula0226 : Wff := (synWex t syntaxFormula0221)
    let syntaxFormula0227 : Wff := (synWex t syntaxFormula0220)
    let syntaxFormula0228 : Wff := (synWb syntaxFormula0205 syntaxFormula0212)
    let syntaxFormula0229 : Wff := (synWb syntaxFormula0204 syntaxFormula0204)
    let syntaxFormula0230 : Wff := (.classMem syntaxClass0201 syntaxClass0200)
    let syntaxFormula0231 : Wff := (.neg syntaxFormula0229)
    let syntaxFormula0232 : Wff := (synWex x syntaxFormula0230)
    let syntaxFormula0233 : Wff := (.all x syntaxFormula0229)
    let syntaxFormula0234 : Wff := (.neg syntaxFormula0233)
    let syntaxClass0235 : Class := (synCima syntaxClass0200 (synC1c))
    let syntaxFormula0236 : Wff := (.classMem syntaxClass0197 syntaxClass0235)
    let syntaxClass0237 : Class := (synCcompl syntaxClass0235)
    let syntaxFormula0238 : Wff :=
      (synWbr (synCsn (.cv a)) syntaxClass0237
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
    let syntaxFormula0239 : Wff := (.classMem syntaxClass0197 syntaxClass0237)
    let syntaxFormula0240 : Wff := (.neg syntaxFormula0236)
    let syntaxFormula0241 : Wff :=
      (synWbr (synCsn (.cv a)) (synCimage (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
    let syntaxFormula0242 : Wff :=
      (synWbr (.cv x) (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (.cv y))
    let syntaxFormula0243 : Wff := (synWeu y syntaxFormula0242)
    let syntaxFormula0244 : Wff :=
      (synWa (synWfn (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
        (.classMem (synCsn (.cv a)) (synCvv)))
    have p0691 := @gNfel1 y (synCuni (.cv p)) (synCvv) dv_cache_0059 p0690
    have p0692 := @gNfv syntaxFormula0143 y dv_cache_0060
    have p0693 :=
      @gNfim (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0143 y p0691 p0692
    have p0694 :=
      @gN1923 (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0144 y p0693
    have p0695 :=
      @gSylib (.classMem (.cv u) (synChwcn P)) (.all y syntaxFormula0145)
        (.imp (synWex y (.classEq (.cv y) (synCuni (.cv q)))) syntaxFormula0144) p0689
        p0694
    have p0696 :=
      @gSyl5bi (.classMem (synCuni (.cv q)) (synCvv))
        (synWex y (.classEq (.cv y) (synCuni (.cv q))))
        (.classMem (.cv u) (synChwcn P)) syntaxFormula0144 p0628 p0695
    have p0697 := @gElex (synCuni (.cv q)) (synCvv)
    have p0698 := @gA1ii syntaxFormula0147 syntaxFormula0148 p0696 p0697
    have p0700 := @gA1ii syntaxFormula0147 syntaxFormula0141 p0698 p0677
    have p0701 :=
      @gCom23 (.classMem (.cv u) (synChwcn P)) (.classMem (synCuni (.cv q)) (synCvv))
        (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0143 p0700
    have p0702 :=
      @gImp3a (.classMem (.cv u) (synChwcn P)) (.classMem (synCuni (.cv p)) (synCvv))
        (.classMem (synCuni (.cv q)) (synCvv)) syntaxFormula0143 p0701
    have p0703 :=
      @gSyl5 syntaxFormula0125 syntaxFormula0149 (.classMem (.cv u) (synChwcn P))
        syntaxFormula0143 p0626 p0702
    have p0704 :=
      @gPm243d (.classMem (.cv u) (synChwcn P)) syntaxFormula0125 syntaxFormula0142
        p0703
    have p0705 :=
      @gSyl5 syntaxFormula0121 syntaxFormula0125 (.classMem (.cv u) (synChwcn P))
        syntaxFormula0142 p0605 p0704
    have p0706 :=
      @gMpdi (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0127
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))) p0609
        p0705
    have p0711 :=
      @gSseld (.classMem (.cv u) (synChwcn P)) (synChwcn (synCfv (synC2nd) (.cv u)))
        (synChwcn (synCun P Y)) (synCuni (.cv q)) p0555
    have p0712 :=
      @gSyl5 syntaxFormula0106
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv u) (synChwcn P))
        (.classMem (synCuni (.cv q)) (synChwcn (synCun P Y))) p0590 p0711
    have p0713 :=
      @gJcad (.classMem (.cv u) (synChwcn P)) syntaxFormula0106
        (.classMem (synCuni (.cv p)) (synChwcn (synCun P Y)))
        (.classMem (synCuni (.cv q)) (synChwcn (synCun P Y))) p0557 p0712
    have p0714 :=
      @gAdantrd (.classMem (.cv u) (synChwcn P)) syntaxFormula0106 syntaxFormula0150
        syntaxFormula0117 p0713
    have p0715 :=
      @gHwnisoclasseqbcl (synCun P Y) (synCuni (.cv p)) (synCuni (.cv q)) p0001
    have p0716 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0150
        syntaxFormula0152 p0714 p0715
    have p0717 :=
      @gBicom syntaxFormula0151
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q)))
    have p0718 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0152
        syntaxFormula0153 p0716 p0717
    have p0719 :=
      @gBi1 (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q)))
        syntaxFormula0151
    have p0720 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0153
        syntaxFormula0154 p0718 p0719
    have p0721 :=
      @gId (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q)))
    have p0722 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P)) (.imp syntaxFormula0121 syntaxFormula0154))
        (.imp (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q)))
          (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))))
        p0720 p0721
    have p0723 :=
      @gMpdd (.classMem (.cv u) (synChwcn P)) syntaxFormula0121
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q)))
        syntaxFormula0151 p0706 p0722
    have p0724 :=
      @gEqeq2 (synCec (synCuni (.cv p)) (synChwniso (synCun P Y)))
        (synCec (synCuni (.cv q)) (synChwniso (synCun P Y)))
        (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
    have p0725 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0151
        syntaxFormula0156 p0723 p0724
    have p0726 := @gBi1 syntaxFormula0114 syntaxFormula0155
    have p0727 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0156
        syntaxFormula0157 p0725 p0726
    have p0728 :=
      @gMpdd (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0114
        syntaxFormula0155 p0565 p0727
    have p0733 :=
      @gFveq2d syntaxFormula0106 (.cv q) (synCsn (synCuni (.cv q)))
        (synChnqmap1 (synCun P Y)) p0585
    have p0734 := @gHnqmap1valcl (synCun P Y) (synCuni (.cv q)) p0001
    have p0735 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0106
        (.classMem (synCuni (.cv q)) (synChwcn (synCun P Y))) syntaxFormula0158 p0712
        p0734
    have p0736 :=
      @gEqeq2 (synCfv (synChnqmap1 (synCun P Y)) (synCsn (synCuni (.cv q))))
        (synCec (synCuni (.cv q)) (synChwniso (synCun P Y)))
        (synCfv (synChnqmap1 (synCun P Y)) (.cv q))
    have p0737 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0106 syntaxFormula0158
        syntaxFormula0161 p0735 p0736
    have p0738 := @gBi1 syntaxFormula0159 syntaxFormula0160
    have p0739 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0106 syntaxFormula0161
        syntaxFormula0162 p0737 p0738
    have p0740 :=
      @gMpdi (.classMem (.cv u) (synChwcn P)) syntaxFormula0106 syntaxFormula0159
        syntaxFormula0160 p0733 p0739
    have p0741 :=
      @gAdantrd (.classMem (.cv u) (synChwcn P)) syntaxFormula0106 syntaxFormula0160
        syntaxFormula0117 p0740
    have p0742 :=
      @gEqcom (synCfv (synChnqmap1 (synCun P Y)) (.cv q))
        (synCec (synCuni (.cv q)) (synChwniso (synCun P Y)))
    have p0743 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0160
        syntaxFormula0163 p0741 p0742
    have p0744 :=
      @gEqeq2 (synCec (synCuni (.cv q)) (synChwniso (synCun P Y)))
        (synCfv (synChnqmap1 (synCun P Y)) (.cv q))
        (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
    have p0745 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0163
        syntaxFormula0165 p0743 p0744
    have p0746 := @gBi1 syntaxFormula0155 syntaxFormula0164
    have p0747 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0165
        syntaxFormula0166 p0745 p0746
    have p0748 :=
      @gMpdd (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0155
        syntaxFormula0164 p0728 p0747
    have p0749 :=
      @gExp3a (.classMem (.cv u) (synChwcn P)) syntaxFormula0106 syntaxFormula0117
        syntaxFormula0164 p0748
    have p0750 :=
      @gSyl5 syntaxFormula0103 syntaxFormula0106 (.classMem (.cv u) (synChwcn P))
        syntaxFormula0167 p0494 p0749
    have p0751 :=
      @gMpdi (.classMem (.cv u) (synChwcn P)) syntaxFormula0103 syntaxFormula0117
        syntaxFormula0164 p0469 p0750
    have p0752 :=
      @gEqeq2 (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
        (synCfv (synChnqmap1 (synCun P Y)) (.cv q)) (.cv y)
    have p0753 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0103 syntaxFormula0164
        syntaxFormula0168 p0751 p0752
    have p0754 :=
      @gBi1 (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv p)))
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q)))
    have p0755 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0103 syntaxFormula0168
        syntaxFormula0169 p0753 p0754
    have p0756 :=
      @gMpdi (.classMem (.cv u) (synChwcn P)) syntaxFormula0103
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv p)))
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q))) p0444 p0755
    have p0758 :=
      @gSimpr syntaxFormula0099 (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z))
    have p0759 :=
      @gSyl syntaxFormula0103 syntaxFormula0100
        (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z)) p0458 p0758
    have p0763 := @gFunbrfv (.cv q) (.cv z) (synChnqmap1 (synCun P Y))
    have p0764 := Nominal.mp p0440 p0763
    have p0765 :=
      @gSyl syntaxFormula0103 (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z))
        (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv q)) (.cv z)) p0759 p0764
    have p0766 :=
      @gEqeq2d syntaxFormula0103 (synCfv (synChnqmap1 (synCun P Y)) (.cv q)) (.cv z)
        (.cv y) p0765
    have p0767 :=
      @gMpbidi syntaxFormula0103
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q)))
        (.classEq (.cv y) (.cv z)) (.classMem (.cv u) (synChwcn P)) p0756 p0766
    have p0768 :=
      @gExp3a (.classMem (.cv u) (synChwcn P)) syntaxFormula0102 syntaxFormula0100
        (.classEq (.cv y) (.cv z)) p0767
    have p0769 :=
      @gAlimdv (.classMem (.cv u) (synChwcn P)) syntaxFormula0102 syntaxFormula0170 q
        dv_cache_0061 p0768
    have p0770 :=
      @gSyl5 syntaxFormula0102 syntaxFormula0171 (.classMem (.cv u) (synChwcn P))
        syntaxFormula0172 p0431 p0769
    have p0771 := @gExim syntaxFormula0100 (.classEq (.cv y) (.cv z)) q
    have p0772 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0102 syntaxFormula0172
        syntaxFormula0173 p0770 p0771
    have p0773 := @gAx17e (.classEq (.cv y) (.cv z)) q dv_cache_0062
    have p0774 :=
      @gSyl8 (.classMem (.cv u) (synChwcn P)) syntaxFormula0102 syntaxFormula0101
        (synWex q (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z)) p0772 p0773
    have p0775 :=
      @gMpdi (.classMem (.cv u) (synChwcn P)) syntaxFormula0102 syntaxFormula0101
        (.classEq (.cv y) (.cv z)) p0430 p0774
    have p0776 :=
      @gExp3a (.classMem (.cv u) (synChwcn P)) syntaxFormula0095 syntaxFormula0097
        (.classEq (.cv y) (.cv z)) p0775
    have p0777 :=
      @gAlimdv (.classMem (.cv u) (synChwcn P)) syntaxFormula0095 syntaxFormula0174 p
        dv_cache_0063 p0776
    have p0778 :=
      @gSyl5 syntaxFormula0095 syntaxFormula0175 (.classMem (.cv u) (synChwcn P))
        syntaxFormula0176 p0425 p0777
    have p0779 := @gExim syntaxFormula0097 (.classEq (.cv y) (.cv z)) p
    have p0780 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P)) syntaxFormula0095 syntaxFormula0176
        syntaxFormula0177 p0778 p0779
    have p0781 := @gAx17e (.classEq (.cv y) (.cv z)) p dv_cache_0064
    have p0782 :=
      @gSyl8 (.classMem (.cv u) (synChwcn P)) syntaxFormula0095 syntaxFormula0098
        (synWex p (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z)) p0780 p0781
    have p0783 :=
      @gMpdi (.classMem (.cv u) (synChwcn P)) syntaxFormula0095 syntaxFormula0098
        (.classEq (.cv y) (.cv z)) p0424 p0782
    have p0784 :=
      @gAlrimiv (.classMem (.cv u) (synChwcn P)) syntaxFormula0178 z dv_cache_0065 p0783
    have p0785 :=
      @gAlrimiv (.classMem (.cv u) (synChwcn P)) syntaxFormula0179 y dv_cache_0057 p0784
    have p0786 :=
      @gAlrimiv (.classMem (.cv u) (synChwcn P)) syntaxFormula0180 x dv_cache_0055 p0785
    have p0787 :=
      @gDffun2 x y z syntaxClass0090 dv_cache_0066 dv_cache_0067 dv_cache_0068
        dv_cache_0007 dv_cache_0069 dv_cache_0070
    have p0788_e01_recanon :
      Nominal.NPrf (synWb (synWfun syntaxClass0090) syntaxFormula0181) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb, synWfun, synWss, synCin, synCcompl, synCnin, synWnan,
            synWa, synCcom, synCopab, synWex, synCcnv, synCid]
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
      @gSylibr (.classMem (.cv u) (synChwcn P)) syntaxFormula0181
        (synWfun syntaxClass0090) p0786 p0788_e01_recanon
    have p0790 :=
      @gFuneq (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)) syntaxClass0090
    have p0791 := Nominal.mp p0419 p0790
    have p0792 :=
      @gSylibr (.classMem (.cv u) (synChwcn P)) (synWfun syntaxClass0090)
        (synWfun (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y))) p0788 p0791
    have p0794 :=
      @gDmeqi (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)) syntaxClass0090
        p0419
    have p0795 :=
      @gPw1ss (synChwcn (synCfv (synC2nd) (.cv u))) (synChwcn (synCun P Y))
    have p0796 :=
      @gSyl (.classMem (.cv u) (synChwcn P))
        (synWss (synChwcn (synCfv (synC2nd) (.cv u))) (synChwcn (synCun P Y)))
        syntaxFormula0182 p0555 p0795
    have p0797 :=
      (Nominal.classEqRefl (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
    have p0798 :=
      @gEqcomi (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synCrn (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))) p0797
    have p0802 :=
      @gEqtri (synCrn (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) p0798 p0481
    have p0804 :=
      @gFndm (synCpw1 (synChwcn (synCun P Y))) (synChnqmap1 (synCun P Y))
    have p0805 := Nominal.mp p0370 p0804
    have p0806 :=
      @gN3sstr4g (.classMem (.cv u) (synChwcn P))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCun P Y)))
        (synCrn (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (synCdm (synChnqmap1 (synCun P Y))) p0796 p0802 p0805
    have p0807 :=
      @gDmcosseq (synChnqmap1 (synCun P Y))
        (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))
    have p0808 :=
      @gSyl (.classMem (.cv u) (synChwcn P)) syntaxFormula0183 syntaxFormula0185 p0806
        p0807
    have p0809 := @gDfrn4 (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p0810 :=
      @gSyl6eqr (.classMem (.cv u) (synChwcn P)) syntaxClass0184
        (synCdm (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (synCrn (synChnqmap1 (synCfv (synC2nd) (.cv u)))) p0808 p0809
    have p0811 := @gHnqmap1rn (synCfv (synC2nd) (.cv u)) p0023
    have p0812 :=
      @gSyl6eq (.classMem (.cv u) (synChwcn P)) syntaxClass0184
        (synCrn (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u))) p0810 p0811
    have p0813 :=
      @gSyl5eq (.classMem (.cv u) (synChwcn P))
        (synCdm (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y))) syntaxClass0184
        (synChnord (synCfv (synC2nd) (.cv u))) p0794 p0812
    have p0814 :=
      @gJca (.classMem (.cv u) (synChwcn P))
        (synWfun (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)))
        syntaxFormula0186 p0792 p0813
    have p0815 := (Nominal.biimpRefl syntaxFormula0187)
    have p0816 :=
      @gSylibr (.classMem (.cv u) (synChwcn P))
        (synWa (synWfun (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)))
          syntaxFormula0186)
        syntaxFormula0187 p0814 p0815
    have p0817 := @gHwnisoclasselhnordcl (synCfv (synC2nd) (.cv u)) (.cv u) p0023
    have p0818 :=
      @gSyl (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0188
        p0011 p0817
    have p0819 :=
      @gJca (.classMem (.cv u) (synChwcn P)) syntaxFormula0187 syntaxFormula0188 p0816
        p0818
    have p0820 :=
      @gFnbrfvb (synChnord (synCfv (synC2nd) (.cv u)))
        (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (.cv u) (synChwniso (synCun P Y)))
        (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y))
    have p0821 :=
      @gSyl (.classMem (.cv u) (synChwcn P)) syntaxFormula0189 syntaxFormula0192 p0819
        p0820
    have p0822 :=
      @gMpbird (.classMem (.cv u) (synChwcn P)) syntaxFormula0191 syntaxFormula0092
        p0421 p0821
    have p0823 :=
      @gEqtr4d (.classMem (.cv u) (synChwcn P))
        (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
        (synCec (.cv u) (synChwniso (synCun P Y))) syntaxClass0190 p0395 p0822
    have p0824 :=
      @gA1d (.classMem (.cv u) (synChwcn P)) syntaxFormula0193
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0823
    have p0825 := @gElex (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p0826 := @gNfcv a (.cv u) dv_cache_0071
    have p0827 := @gIssetf a (.cv u) p0826
    have p0828 := (Nominal.classEqRefl (synChnqmap1 (synCfv (synC2nd) (.cv u))))
    have p0829 :=
      @gFveq1i (synCsn (.cv a)) (synChnqmap1 (synCfv (synC2nd) (.cv u)))
        syntaxClass0194 p0828
    have p0830 := @gSnelpw1 (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p0831 :=
      @gBiimpri syntaxFormula0195
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) p0830
    have p0832 :=
      @gFvres (synCsn (.cv a)) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synCimage (synChwniso (synCfv (synC2nd) (.cv u))))
    have p0833 :=
      @gSyl (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0195
        (.classEq (synCfv syntaxClass0194 (synCsn (.cv a))) syntaxClass0196) p0831 p0832
    have p0834 :=
      @gSyl5eq (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCfv syntaxClass0194 (synCsn (.cv a))) syntaxClass0196 p0829 p0833
    have p0835 :=
      @gEqid (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
    have p0836 :=
      @gDfcleq x (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        dv_cache_0072 dv_cache_0072
    have p0837 := @gElima1c x syntaxClass0197 syntaxClass0200 dv_cache_0073 dv_cache_0074
    have p0838 := @gElsymdif syntaxClass0201 (synCins2 (synCsset)) syntaxClass0199
    have p0839 := @gSnex (.cv a)
    have p0840 :=
      @gOtelins2 (synCsn (.cv x)) (synCsn (.cv a))
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCsset) p0839
    have p0841 := (Nominal.biimpRefl syntaxFormula0202)
    have p0842 := @gSnex (.cv x)
    have p0843 := @gF1odm (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)) (.cv k)
    have p0844 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWf1o (.cv k) (synCfv (synC2nd) (.cv u)) (synCrn (.cv k)))
        (.classEq (synCdm (.cv k)) (synCfv (synC2nd) (.cv u))) p0006 p0843
    have p0845 := @gDmex (.cv k) p0082
    have p0846 :=
      @gSyl6eqelr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synCfv (synC2nd) (.cv u)) (synCdm (.cv k)) (synCvv) p0844 p0845
    have p0847 := @gHwnisoexg (synCfv (synC2nd) (.cv u))
    have p0848 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synC2nd) (.cv u)) (synCvv))
        (.classMem (synChwniso (synCfv (synC2nd) (.cv u))) (synCvv)) p0846 p0847
    have p0849 :=
      @gImaexg (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)) (synCvv)
        (synCvv)
    have p0850 :=
      @gSylancl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synChwniso (synCfv (synC2nd) (.cv u))) (synCvv))
        (.classMem (synCsn (.cv a)) (synCvv)) syntaxFormula0203 p0848 p0839 p0849
    have p0851 :=
      @gBrssetg (synCsn (.cv x))
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))) (synCvv)
        (synCvv)
    have p0852 :=
      @gSylancr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCsn (.cv x)) (synCvv)) syntaxFormula0203
        (synWb syntaxFormula0202 (synWss (synCsn (.cv x))
            (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))))
        p0842 p0850 p0851
    have p0853 := @gVex x
    have p0854 :=
      @gSnss (.cv x)
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))) p0853
    have p0855 :=
      @gSyl6bbr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0202
        (synWss (synCsn (.cv x))
          (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
        syntaxFormula0204 p0852 p0854
    have p0856 :=
      @gSyl5bbr
        (.classMem (synCop (synCsn (.cv x))
            (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
          (synCsset))
        syntaxFormula0202 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        syntaxFormula0204 p0841 p0855
    have p0857 :=
      @gSyl5bb syntaxFormula0205
        (.classMem (synCop (synCsn (.cv x))
            (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
          (synCsset))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0204 p0840 p0856
    have p0858 := @gNfcv b (synCsn (.cv x)) dv_cache_0075
    have p0859 := @gIssetf b (synCsn (.cv x)) p0858
    have p0860 := @gVex b
    have p0861 :=
      @gOpexg (.cv b)
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))) (synCvv)
        (synCvv)
    have p0862 :=
      @gSylancr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv b) (synCvv)) syntaxFormula0203 syntaxFormula0207 p0860 p0850
        p0861
    have p0863 :=
      @gBiantrud (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0207
        syntaxFormula0208 p0862
    have p0864 := (Nominal.classEqRefl syntaxClass0199)
    have p0865 :=
      @gEleq2i syntaxClass0199 (synCtxp syntaxClass0198 (synCvv)) syntaxClass0209 p0864
    have p0866 :=
      @gOteltxp (.cv b) (synCsn (.cv a))
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        syntaxClass0198 (synCvv)
    have p0867 :=
      @gBitri syntaxFormula0210
        (.classMem syntaxClass0209 (synCtxp syntaxClass0198 (synCvv))) syntaxFormula0211
        p0865 p0866
    have p0868 :=
      @gSyl6rbbr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0208
        syntaxFormula0211 syntaxFormula0210 p0863 p0867
    have p0869 := @gOpeq1 (.cv b) (synCsn (.cv x)) syntaxClass0197
    have p0870 :=
      @gEleq1d (.classEq (.cv b) (synCsn (.cv x))) syntaxClass0209 syntaxClass0201
        syntaxClass0199 p0869
    have p0871 := @gOpeq1 (.cv b) (synCsn (.cv x)) (synCsn (.cv a))
    have p0872 :=
      @gEleq1d (.classEq (.cv b) (synCsn (.cv x))) (synCop (.cv b) (synCsn (.cv a)))
        (synCop (synCsn (.cv x)) (synCsn (.cv a))) syntaxClass0198 p0871
    have p0873 :=
      @gBibi12d (.classEq (.cv b) (synCsn (.cv x))) syntaxFormula0210 syntaxFormula0212
        syntaxFormula0208 syntaxFormula0213 p0870 p0872
    have p0874 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWb syntaxFormula0210 syntaxFormula0208) (.classEq (.cv b) (synCsn (.cv x)))
        syntaxFormula0214 p0868 p0873
    have p0875 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0215 b
        dv_cache_0076 p0874
    have p0876 := @gNfv syntaxFormula0214 b dv_cache_0077
    have p0877 :=
      @gN1923 (.classEq (.cv b) (synCsn (.cv x))) syntaxFormula0214 b p0876
    have p0878 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all b syntaxFormula0215)
        (.imp (synWex b (.classEq (.cv b) (synCsn (.cv x)))) syntaxFormula0214) p0875
        p0877
    have p0879 :=
      @gSyl5bi (.classMem (synCsn (.cv x)) (synCvv))
        (synWex b (.classEq (.cv b) (synCsn (.cv x))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0214 p0859 p0878
    have p0880 := @gElex (synCsn (.cv x)) (synCvv)
    have p0881 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (synCsn (.cv x)) (synCvv)) syntaxFormula0214))
        (.imp (.classMem (synCsn (.cv x)) (synCvv)) (.classMem (synCsn (.cv x)) (synCvv)))
        p0879 p0880
    have p0882 := @gElex syntaxClass0201 syntaxClass0199
    have p0883 := @gOpexb (synCsn (.cv x)) syntaxClass0197
    have p0884 :=
      @gSimplbi (.classMem syntaxClass0201 (synCvv))
        (.classMem (synCsn (.cv x)) (synCvv)) syntaxFormula0216 p0883
    have p0885 :=
      @gSyl syntaxFormula0212 (.classMem syntaxClass0201 (synCvv))
        (.classMem (synCsn (.cv x)) (synCvv)) p0882 p0884
    have p0886 := @gElex (synCop (synCsn (.cv x)) (synCsn (.cv a))) syntaxClass0198
    have p0887 := @gOpexb (synCsn (.cv x)) (synCsn (.cv a))
    have p0888 :=
      @gSimplbi (.classMem (synCop (synCsn (.cv x)) (synCsn (.cv a))) (synCvv))
        (.classMem (synCsn (.cv x)) (synCvv)) (.classMem (synCsn (.cv a)) (synCvv))
        p0887
    have p0889 :=
      @gSyl syntaxFormula0213
        (.classMem (synCop (synCsn (.cv x)) (synCsn (.cv a))) (synCvv))
        (.classMem (synCsn (.cv x)) (synCvv)) p0886 p0888
    have p0890 :=
      @gPm521ni syntaxFormula0212 (.classMem (synCsn (.cv x)) (synCvv))
        syntaxFormula0213 p0885 p0889
    have p0891 :=
      @gPm261d1 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCsn (.cv x)) (synCvv)) syntaxFormula0214 p0881 p0890
    have p0892 :=
      @gBrcnv (synCsn (.cv x)) (.cv t)
        (synCsi (synChwniso (synCfv (synC2nd) (.cv u))))
    have p0893 :=
      @gBrsnsi2 y (.cv x) (.cv t) (synChwniso (synCfv (synC2nd) (.cv u)))
        dv_cache_0078 dv_cache_0079 dv_cache_0080 p0853
    have p0894 :=
      @gBitri syntaxFormula0217
        (synWbr (.cv t) (synCsi (synChwniso (synCfv (synC2nd) (.cv u)))) (synCsn (.cv x)))
        syntaxFormula0219 p0892 p0893
    have p0895 :=
      @gAnbi1i syntaxFormula0217 syntaxFormula0219
        (synWbr (.cv t) (synCsset) (synCsn (.cv a))) p0894
    have p0896 :=
      @gN1941v syntaxFormula0218 (synWbr (.cv t) (synCsset) (synCsn (.cv a))) y
        dv_cache_0081
    have p0897 :=
      @gBitr4i syntaxFormula0220
        (synWa syntaxFormula0219 (synWbr (.cv t) (synCsset) (synCsn (.cv a))))
        syntaxFormula0222 p0895 p0896
    have p0898 := @gExbii syntaxFormula0220 syntaxFormula0222 t p0897
    have p0899 := @gExcom syntaxFormula0221 t y
    have p0900 :=
      @gAnass (.classEq (.cv t) (synCsn (.cv y)))
        (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x))
        (synWbr (.cv t) (synCsset) (synCsn (.cv a)))
    have p0901 := @gExbii syntaxFormula0221 syntaxFormula0224 t p0900
    have p0902 := @gSnex (.cv y)
    have p0903 := @gBreq1 (.cv t) (synCsn (.cv y)) (synCsn (.cv a)) (synCsset)
    have p0904 :=
      @gAnbi2d (.classEq (.cv t) (synCsn (.cv y)))
        (synWbr (.cv t) (synCsset) (synCsn (.cv a)))
        (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a)))
        (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x)) p0903
    have p0905 :=
      @gAncom (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x))
        (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a)))
    have p0906 := @gVex y
    have p0907 := @gBrssetsn (.cv y) (synCsn (.cv a)) p0906 p0839
    have p0908 :=
      @gAnbi1i (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a)))
        (.classMem (.cv y) (synCsn (.cv a)))
        (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x)) p0907
    have p0909 :=
      @gBitri
        (synWa (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x))
          (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a))))
        (synWa (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a)))
          (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x)))
        syntaxFormula0225 p0905 p0908
    have p0910 :=
      @gSyl6bb (.classEq (.cv t) (synCsn (.cv y))) syntaxFormula0223
        (synWa (synWbr (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x))
          (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a))))
        syntaxFormula0225 p0904 p0909
    have p0911 :=
      @gCeqsexv syntaxFormula0223 syntaxFormula0225 t (synCsn (.cv y)) dv_cache_0082
        dv_cache_0083 p0902 p0910
    have p0912 :=
      @gBitri syntaxFormula0226 (synWex t syntaxFormula0224) syntaxFormula0225 p0901
        p0911
    have p0913 := @gExbii syntaxFormula0226 syntaxFormula0225 y p0912
    have p0914 :=
      @gN3bitri syntaxFormula0227 (synWex t syntaxFormula0222)
        (synWex y syntaxFormula0226) (synWex y syntaxFormula0225) p0898 p0899 p0913
    have p0915 :=
      @gOpelco t (synCsn (.cv x)) (synCsn (.cv a)) (synCsset)
        (synCcnv (synCsi (synChwniso (synCfv (synC2nd) (.cv u))))) dv_cache_0084
        dv_cache_0085 dv_cache_0086 dv_cache_0087
    have p0916 :=
      @gElima2 y (.cv x) (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))
        dv_cache_0078 dv_cache_0080 dv_cache_0088
    have p0917 :=
      @gN3bitr4i syntaxFormula0227 (synWex y syntaxFormula0225) syntaxFormula0213
        syntaxFormula0204 p0914 p0915 p0916
    have p0918 :=
      @gSyl6bb (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0212
        syntaxFormula0213 syntaxFormula0204 p0891 p0917
    have p0919 :=
      @gBibi12d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0205
        syntaxFormula0204 syntaxFormula0212 syntaxFormula0204 p0857 p0918
    have p0920 :=
      @gNotbid (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0228
        syntaxFormula0229 p0919
    have p0921 :=
      @gSyl5bb syntaxFormula0230 (.neg syntaxFormula0228)
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0231 p0838 p0920
    have p0922 :=
      @gExbidv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0230
        syntaxFormula0231 x dv_cache_0089 p0921
    have p0923 := @gExnal syntaxFormula0229 x
    have p0924 :=
      @gSyl6bb (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0232
        (synWex x syntaxFormula0231) syntaxFormula0234 p0922 p0923
    have p0925 :=
      @gSyl5bb syntaxFormula0236 syntaxFormula0232
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0234 p0837 p0924
    have p0926 :=
      @gCon2bid (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0236
        syntaxFormula0233 p0925
    have p0927 :=
      (Nominal.classEqRefl (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))))
    have p0928 :=
      @gBreqi (synCsn (.cv a))
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) syntaxClass0237 p0927
    have p0929 := (Nominal.biimpRefl syntaxFormula0238)
    have p0930 :=
      @gOpexg (synCsn (.cv a))
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))) (synCvv)
        (synCvv)
    have p0931 :=
      @gSylancr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCsn (.cv a)) (synCvv)) syntaxFormula0203 syntaxFormula0216 p0839
        p0850 p0930
    have p0932 := @gElcomplg syntaxClass0197 syntaxClass0235 (synCvv)
    have p0933 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0216
        (synWb syntaxFormula0239 syntaxFormula0240) p0931 p0932
    have p0934 :=
      @gSyl5bb syntaxFormula0238 syntaxFormula0239
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0240 p0929 p0933
    have p0935 :=
      @gSyl5bb syntaxFormula0241 syntaxFormula0238
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0240 p0928 p0934
    have p0936 :=
      @gBitr4d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0233
        syntaxFormula0240 syntaxFormula0241 p0926 p0935
    have p0937 :=
      @gSyl5rbb
        (.classEq (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
          (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
        syntaxFormula0233 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        syntaxFormula0241 p0836 p0936
    have p0938 :=
      @gMpbiri (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0241
        (.classEq (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
          (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
        p0835 p0937
    have p0939 := @gTru
    have p0941 :=
      @gImaexg (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x) (synCvv) (synCvv)
    have p0942 :=
      @gSylancl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synChwniso (synCfv (synC2nd) (.cv u))) (synCvv))
        (.classMem (.cv x) (synCvv))
        (.classMem (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x)) (synCvv))
        p0848 p0853 p0941
    have p0943 :=
      @gEueq y (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x))
        dv_cache_0090
    have p0944 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x)) (synCvv))
        (synWeu y (.classEq (.cv y)
            (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x))))
        p0942 p0943
    have p0947 :=
      @gBrimage (.cv x) (.cv y) (synChwniso (synCfv (synC2nd) (.cv u))) p0853 p0906
    have p0948 :=
      @gEubii syntaxFormula0242
        (.classEq (.cv y) (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x))) y
        p0947
    have p0949 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWeu y (.classEq (.cv y)
            (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (.cv x))))
        syntaxFormula0243 p0944 p0948
    have p0950 :=
      @gRalrimivw (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0243 x
        (synCvv) dv_cache_0089 p0949
    have p0951 :=
      @gFnres x y (synCvv) (synCimage (synChwniso (synCfv (synC2nd) (.cv u))))
        dv_cache_0091 dv_cache_0059 dv_cache_0092 dv_cache_0093 dv_cache_0007
    have p0952 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWral x (synCvv) syntaxFormula0243)
        (synWfn (synCres (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
          (synCvv))
        p0950 p0951
    have p0953 := @gResid (synCimage (synChwniso (synCfv (synC2nd) (.cv u))))
    have p0954 :=
      @gFneq1i (synCvv)
        (synCres (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
        (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) p0953
    have p0955 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfn (synCres (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
          (synCvv))
        (synWfn (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv)) p0952
        p0954
    have p0956 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfn (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
        synWtru p0955
    have p0957 := @gA1i (.classMem (synCsn (.cv a)) (synCvv)) synWtru p0839
    have p0958 :=
      @g_pm3_2 (synWfn (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
        (.classMem (synCsn (.cv a)) (synCvv))
    have p0959 :=
      @gSyl5 synWtru (.classMem (synCsn (.cv a)) (synCvv))
        (synWfn (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
        syntaxFormula0244 p0957 p0958
    have p0960 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) synWtru
        (synWfn (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
        (.imp synWtru syntaxFormula0244) p0956 p0959
    have p0961 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) synWtru
        syntaxFormula0244 p0960
    exact
      continuation p0691 p0697 p0705 p0715 p0717 p0719 p0721 p0722 p0724 p0726 p0734 p0736
        p0738 p0742 p0744 p0746 p0747 p0752 p0754 p0764 p0766 p0771 p0773 p0779 p0781
        p0791 p0794 p0796 p0798 p0805 p0807 p0809 p0815 p0820 p0824 p0825 p0827 p0828
        p0831 p0834 p0839 p0842 p0846 p0848 p0853 p0859 p0860 p0871 p0880 p0888 p0902
        p0903 p0906 p0907 p0938 p0939 p0955 p0957 p0961

end NFChoice.DirectNominalPrf.WPPReplay

end
