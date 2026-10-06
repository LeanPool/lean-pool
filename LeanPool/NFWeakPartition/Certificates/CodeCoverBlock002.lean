/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block020

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `ReplaySupport.CodeCover4`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_cfbhnqinjcodecoverddndv_stage4`. -/
@[expose]
noncomputable def gCfbhnqinjcodecoverddndvStage4 (u : Var) (P : Class) (k : Var)
    (Y : Class) (p0011 : _) (p0374 : _) (p0400 : _) (p0403 : _) (p0406 : _) (p0415 : _)
    (p0417 : _) (p0420 : _) (p0424 : _) (p0425 : _) (p0430 : _) (p0431 : _) (p0444 : _)
    (p0451 : _) (p0453 : _) (p0455 : _) (p0462 : _) (p0466 : _) (p0478 : _) (p0480 : _)
    (p0489 : _) (p0503 : _) (p0565 : _) (p0570 : _) (p0580 : _) (p0586 : _) (p0590 : _)
    (p0605 : _) (p0621 : _) (p0624 : _) (p0626 : _) (p0677 : _) (p0679 : _) (p0697 : _)
    (p0705 : _) (p0722 : _) (p0724 : _) (p0726 : _) (p0747 : _) (p0752 : _) (p0754 : _)
    (p0766 : _) (p0771 : _) (p0773 : _) (p0779 : _) (p0781 : _) (p0825 : _) (p0827 : _)
    (p0828 : _) (p0834 : _) (p0846 : _) (p0938 : _) (p0939 : _) (p0955 : _) (p0961 : _)
    {Result : Type}
    (continuation : _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → Result) :=
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
    let v : Var := freshVar proofSupport 11
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
    have fresh_y_ne_k : y ≠ k := by
      intro h
      exact
        fresh_y
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
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
    have fresh_a_ne_k : a ≠ k := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_a_not_Y : a ∉ Y.fv := by
      intro h
      exact fresh_a (Finset.mem_union_right _ (h))
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
    have fresh_z_ne_k : z ≠ k := by
      intro h
      exact
        fresh_z
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
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
    have fresh_p_ne_k : p ≠ k := by
      intro h
      exact
        fresh_p
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
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
    have fresh_q_ne_k : q ≠ k := by
      intro h
      exact
        fresh_q
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_q_not_Y : q ∉ Y.fv := by
      intro h
      exact fresh_q (Finset.mem_union_right _ (h))
    have fresh_v : v ∉ proofSupport :=
      by
      change freshVar proofSupport 11 ∉ proofSupport
      exact freshVar_not_mem proofSupport 11
    have fresh_v_ne_u : v ≠ u := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_v_ne_k : v ≠ k := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_v_not_Y : v ∉ Y.fv := by
      intro h
      exact fresh_v (Finset.mem_union_right _ (h))
    have fresh_a_ne_p : a ≠ p :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
    have fresh_a_ne_q : a ≠ q :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
    have fresh_a_ne_v : a ≠ v :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 4) (j := 11) (by decide)
    have fresh_p_ne_v : p ≠ v :=
      by
      change freshVar proofSupport 6 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 6) (j := 11) (by decide)
    have fresh_v_ne_p : v ≠ p := Ne.symm fresh_p_ne_v
    have fresh_q_ne_v : q ≠ v :=
      by
      change freshVar proofSupport 7 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 7) (j := 11) (by decide)
    have fresh_v_ne_q : v ≠ q := Ne.symm fresh_q_ne_v
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
    have dv_cache_0094 :
      a ∉
        ((Wff.imp (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) (.classEq
              (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv u)))
              (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0095 : p ∉ ((synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_p_ne_u, fresh_p_not_Y, fresh_p_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0096 : q ∉ ((synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_u, fresh_q_not_Y, fresh_q_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0097 : a ∉ ((synCuni (.cv p))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_p,
            not_false_eq_true])
    have dv_cache_0098 :
      a ∉
        ((Wff.imp (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
            (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u)))
                (synCsn (synCuni (.cv p)))) (synCec (synCuni (.cv p))
                (synChwniso (synCfv (synC2nd) (.cv u))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_u, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0099 : a ∉ ((synCuni (.cv q))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_q,
            not_false_eq_true])
    have dv_cache_0100 :
      a ∉
        ((Wff.imp (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
            (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u)))
                (synCsn (synCuni (.cv q)))) (synCec (synCuni (.cv q))
                (synChwniso (synCfv (synC2nd) (.cv u))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_q, fresh_a_ne_u, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0101 : v ∉ ((synCuni (.cv q))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_v_ne_q,
            not_false_eq_true])
    have dv_cache_0102 :
      a ∉
        ((Wff.imp (synWa
              (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
              (.classMem (.cv v) (synChwcn (synCfv (synC2nd) (.cv u))))) (synWb (.classEq
                (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
                (synCec (.cv v) (synChwniso (synCfv (synC2nd) (.cv u)))))
              (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))
                (.cv v))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_u, fresh_a_ne_v,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0103 : v ∉ ((synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_v_ne_u, fresh_v_not_Y, fresh_v_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0104 : v ∉ ((synCuni (.cv p))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_v_ne_p,
            not_false_eq_true])
    have dv_cache_0105 : v ∉ ((synCvv)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0106 :
      v ∉
        ((Wff.imp (synWa
              (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
              (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))) (synWb
              (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
                (synCec (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u)))))
              (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))
                (synCuni (.cv q)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_singleton, fresh_v_ne_p, fresh_v_ne_u, fresh_v_ne_q,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0107 : z ∉ ((synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_Y, fresh_z_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0108 : y ∉ ((synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_u, fresh_y_not_Y, fresh_y_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    let syntaxFormula0073 : Wff :=
      (synWbr (synCsn (.cv u)) (synChnqmap1 (synCun P Y))
        (synCec (.cv u) (synChwniso (synCun P Y))))
    let syntaxFormula0074 : Wff :=
      (synWbr (.cv x) (synChnqmap1 (synCun P Y))
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
    let syntaxFormula0114 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
        (synCec (synCuni (.cv p)) (synChwniso (synCun P Y))))
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
    let syntaxFormula0141 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) (.classMem (synCuni (.cv p)) (synCvv)))
    let syntaxFormula0148 : Wff :=
      (.imp (.classMem (synCuni (.cv q)) (synCvv)) (.classMem (synCuni (.cv q)) (synCvv)))
    let syntaxFormula0149 : Wff :=
      (synWa (.classMem (synCuni (.cv p)) (synCvv)) (.classMem (synCuni (.cv q)) (synCvv)))
    let syntaxFormula0151 : Wff :=
      (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCun P Y)))
        (synCec (synCuni (.cv q)) (synChwniso (synCun P Y))))
    let syntaxFormula0155 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
        (synCec (synCuni (.cv q)) (synChwniso (synCun P Y))))
    let syntaxFormula0156 : Wff := (synWb syntaxFormula0114 syntaxFormula0155)
    let syntaxFormula0157 : Wff := (.imp syntaxFormula0114 syntaxFormula0155)
    let syntaxFormula0164 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
        (synCfv (synChnqmap1 (synCun P Y)) (.cv q)))
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
    let syntaxClass0194 : Class :=
      (synCres (synCimage (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxClass0196 : Class :=
      (synCfv (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCsn (.cv a)))
    let syntaxFormula0241 : Wff :=
      (synWbr (synCsn (.cv a)) (synCimage (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
    let syntaxFormula0244 : Wff :=
      (synWa (synWfn (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
        (.classMem (synCsn (.cv a)) (synCvv)))
    let syntaxFormula0245 : Wff :=
      (.classEq syntaxClass0196
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
    let syntaxFormula0246 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        syntaxClass0196)
    let syntaxFormula0247 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0248 : Wff := (synWb syntaxFormula0246 syntaxFormula0247)
    let syntaxFormula0249 : Wff :=
      (.imp (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0247)
    let syntaxFormula0250 : Wff :=
      (.imp (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0079)
    let syntaxFormula0251 : Wff := (.imp (.classEq (.cv a) (.cv u)) syntaxFormula0250)
    let syntaxFormula0252 : Wff :=
      (synWfn syntaxClass0194 (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0253 : Wff := (.imp syntaxFormula0095 syntaxFormula0098)
    let syntaxFormula0254 : Wff := (.imp syntaxFormula0102 syntaxFormula0101)
    let syntaxFormula0255 : Wff :=
      (.imp syntaxFormula0103 (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv p))))
    let syntaxFormula0256 : Wff := (synWb syntaxFormula0104 syntaxFormula0117)
    let syntaxFormula0257 : Wff :=
      (.classEq (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0258 : Wff := (.imp syntaxFormula0121 syntaxFormula0114)
    let syntaxFormula0259 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0119)
    let syntaxFormula0260 : Wff :=
      (.imp (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0259)
    let syntaxFormula0261 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p)) syntaxClass0118)
    let syntaxFormula0262 : Wff := (synWb syntaxFormula0261 syntaxFormula0120)
    let syntaxFormula0263 : Wff :=
      (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)))
    let syntaxFormula0264 : Wff :=
      (.imp (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0123)
    let syntaxFormula0265 : Wff :=
      (.imp (.classEq (.cv a) (synCuni (.cv q))) syntaxFormula0264)
    let syntaxFormula0266 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)) syntaxClass0122)
    let syntaxFormula0267 : Wff := (synWb syntaxFormula0266 syntaxFormula0124)
    let syntaxFormula0268 : Wff := (synWb syntaxFormula0263 syntaxFormula0126)
    let syntaxFormula0269 : Wff :=
      (synWa (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv v) (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0270 : Wff :=
      (synWa (.classMem (synCfv (synC2nd) (.cv u)) (synCvv)) syntaxFormula0269)
    let syntaxFormula0271 : Wff :=
      (.classEq (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (.cv v) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0272 : Wff :=
      (synWb syntaxFormula0271
        (synWbr (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv v)))
    let syntaxFormula0273 : Wff :=
      (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (.cv v) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0274 : Wff :=
      (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv v) (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0275 : Wff :=
      (synWb syntaxFormula0273
        (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv v)))
    let syntaxFormula0276 : Wff := (.imp syntaxFormula0274 syntaxFormula0275)
    let syntaxFormula0277 : Wff :=
      (.imp (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0276)
    let syntaxFormula0278 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0276)
    let syntaxFormula0279 : Wff := (.imp syntaxFormula0125 syntaxFormula0128)
    let syntaxFormula0280 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0279)
    let syntaxFormula0281 : Wff :=
      (.imp (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0280)
    let syntaxFormula0282 : Wff :=
      (.imp (.classMem (synCuni (.cv q)) (synCvv)) syntaxFormula0280)
    let syntaxFormula0283 : Wff :=
      (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0282)
    let syntaxFormula0284 : Wff :=
      (.imp syntaxFormula0121
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))))
    let syntaxFormula0285 : Wff := (.imp syntaxFormula0121 syntaxFormula0155)
    let syntaxFormula0286 : Wff := (.imp syntaxFormula0106 syntaxFormula0167)
    let syntaxFormula0287 : Wff := (.imp syntaxFormula0103 syntaxFormula0106)
    let syntaxFormula0288 : Wff := (.imp syntaxFormula0103 syntaxFormula0167)
    let syntaxFormula0289 : Wff := (.imp syntaxFormula0103 syntaxFormula0117)
    let syntaxFormula0290 : Wff := (.imp syntaxFormula0103 syntaxFormula0164)
    let syntaxFormula0291 : Wff :=
      (.imp syntaxFormula0103 (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q))))
    let syntaxFormula0292 : Wff := (.imp syntaxFormula0102 syntaxFormula0170)
    let syntaxFormula0293 : Wff := (.imp syntaxFormula0171 syntaxFormula0172)
    let syntaxFormula0294 : Wff := (.imp syntaxFormula0101 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0295 : Wff := (.imp syntaxFormula0102 syntaxFormula0294)
    let syntaxFormula0296 : Wff := (.imp syntaxFormula0102 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0297 : Wff := (.imp syntaxFormula0095 syntaxFormula0174)
    let syntaxFormula0298 : Wff := (.imp syntaxFormula0175 syntaxFormula0176)
    let syntaxFormula0299 : Wff := (.imp syntaxFormula0098 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0300 : Wff := (.imp syntaxFormula0095 syntaxFormula0299)
    have p0962 :=
      @gMpi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) synWtru syntaxFormula0244
        p0939 p0961
    have p0963 :=
      @gFnbrfvb (synCvv) (synCsn (.cv a))
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCimage (synChwniso (synCfv (synC2nd) (.cv u))))
    have p0964 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0244
        (synWb syntaxFormula0245 syntaxFormula0241) p0962 p0963
    have p0965 :=
      @gMpbird (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0245
        syntaxFormula0241 p0938 p0964
    have p0966 :=
      (Nominal.classEqRefl (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
    have p0967 :=
      @gSyl6eqr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxClass0196
        (synCima (synChwniso (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))) p0965 p0966
    have p0968 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq syntaxClass0196 (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) p0967
    have p0969 :=
      @gEqeq2 syntaxClass0196
        (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
    have p0970 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq syntaxClass0196 (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0248 p0968 p0969
    have p0971 := @gBi1 syntaxFormula0246 syntaxFormula0247
    have p0972 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0248
        (.imp syntaxFormula0246 syntaxFormula0247) p0970 p0971
    have p0973 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0246
        syntaxFormula0247 p0834 p0972
    have p0974 := @gEleq1 (.cv a) (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p0975 := @gSneq (.cv a) (.cv u)
    have p0976 :=
      @gFveq2d (.classEq (.cv a) (.cv u)) (synCsn (.cv a)) (synCsn (.cv u))
        (synChnqmap1 (synCfv (synC2nd) (.cv u))) p0975
    have p0977 := @gEceq1 (.cv a) (.cv u) (synChwniso (synCfv (synC2nd) (.cv u)))
    have p0978 :=
      @gEqeq12d (.classEq (.cv a) (.cv u))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv u)))
        (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u)))) p0976 p0977
    have p0979 :=
      @gImbi12d (.classEq (.cv a) (.cv u))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0247
        syntaxFormula0079 p0974 p0978
    have p0980 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0249
        (.classEq (.cv a) (.cv u)) syntaxFormula0250 p0973 p0979
    have p0981 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0251 a
        dv_cache_0024 p0980
    have p0982 := @gNfv syntaxFormula0250 a dv_cache_0094
    have p0983 := @gN1923 (.classEq (.cv a) (.cv u)) syntaxFormula0250 a p0982
    have p0984 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all a syntaxFormula0251)
        (.imp (synWex a (.classEq (.cv a) (.cv u))) syntaxFormula0250) p0981 p0983
    have p0985 :=
      @gSyl5bi (.classMem (.cv u) (synCvv)) (synWex a (.classEq (.cv a) (.cv u)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0250 p0827 p0984
    have p0986 := @gElex (.cv u) (synCvv)
    have p0987 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (.cv u) (synCvv)) syntaxFormula0250))
        (.imp (.classMem (.cv u) (synCvv)) (.classMem (.cv u) (synCvv))) p0985 p0986
    have p0988 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv u) (synCvv))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0079
        p0987
    have p0989 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv u) (synCvv)) syntaxFormula0079 p0825 p0988
    have p0990 :=
      @gSyl5com (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0079 p0011 p0989
    have p0991 := @gSsv (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
    have p0992 :=
      @gJctir (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfn (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
        (synWss (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) (synCvv)) p0955
        p0991
    have p0993 :=
      @gFnssres (synCvv) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synCimage (synChwniso (synCfv (synC2nd) (.cv u))))
    have p0994 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa (synWfn (synCimage (synChwniso (synCfv (synC2nd) (.cv u)))) (synCvv))
          (synWss (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) (synCvv)))
        syntaxFormula0252 p0992 p0993
    have p0996 :=
      @gFneq1i (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synChnqmap1 (synCfv (synC2nd) (.cv u))) syntaxClass0194 p0828
    have p0997 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0252
        syntaxFormula0081 p0994 p0996
    have p0998 :=
      @gA1d (.classMem (.cv u) (synChwcn P)) syntaxFormula0080
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0400
    have p0999 := @g_pm3_2 syntaxFormula0081 syntaxFormula0080
    have p1000 :=
      @gSyl9 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0080
        syntaxFormula0081 syntaxFormula0082 p0998 p0999
    have p1001 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0081
        (.classMem (.cv u) (synChwcn P))
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0082) p0997
        p1000
    have p1002 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0082 p1001
    have p1004 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0082
        syntaxFormula0084 p1002 p0403
    have p1005 := @gBi1 syntaxFormula0079 syntaxFormula0083
    have p1006 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0084
        (.imp syntaxFormula0079 syntaxFormula0083) p1004 p1005
    have p1007 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0079
        syntaxFormula0083 p0990 p1006
    have p1009 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0083
        syntaxFormula0085 p1007 p0406
    have p1010 :=
      @gJctird (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0085
        syntaxFormula0073 p1009 p0374
    have p1018 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0088
        syntaxFormula0089 p1010 p0415
    have p1020 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0089
        syntaxFormula0091 p1018 p0417
    have p1023 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0091
        syntaxFormula0092 p1020 p0420
    have p1027 :=
      @gA1i syntaxFormula0253 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0424
    have p1029 :=
      Nominal.ax17 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p dv_cache_0095
    have p1035 :=
      @gA1i syntaxFormula0254 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0430
    have p1037 :=
      Nominal.ax17 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) q dv_cache_0096
    have p1051 :=
      @gA1i syntaxFormula0255 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0444
    have p1060 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0081
        (synWfun (synChnqmap1 (synCfv (synC2nd) (.cv u)))) p0997 p0453
    have p1062 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfun (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (.imp (synWbr (.cv p) (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv x))
          syntaxFormula0104)
        p1060 p0455
    have p1063 :=
      @gSyl5 syntaxFormula0103
        (synWbr (.cv p) (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv x))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0104 p0451 p1062
    have p1070 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfun (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (.imp (synWbr (.cv q) (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv x))
          syntaxFormula0105)
        p1060 p0466
    have p1071 :=
      @gSyl5 syntaxFormula0103
        (synWbr (.cv q) (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv x))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0105 p0462 p1070
    have p1072 :=
      @gEqcom (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)) (.cv x)
    have p1073 :=
      @gSyl6ib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        syntaxFormula0105
        (.classEq (.cv x) (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)))
        p1071 p1072
    have p1074 :=
      @gEqeq2 (.cv x) (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p))
    have p1075 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        (.classEq (.cv x) (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)))
        syntaxFormula0256 p1073 p1074
    have p1076 := @gBi1 syntaxFormula0104 syntaxFormula0117
    have p1077 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        syntaxFormula0256 (.imp syntaxFormula0104 syntaxFormula0117) p1075 p1076
    have p1078 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        syntaxFormula0104 syntaxFormula0117 p1063 p1077
    have p1089 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0081
        syntaxFormula0257 p0997 p0480
    have p1090 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0257
        syntaxFormula0103 p1089
    have p1091 :=
      @gEleq2 (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) (.cv p)
    have p1092 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        syntaxFormula0257
        (synWb (.classMem (.cv p) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))))
        p1090 p1091
    have p1093 :=
      @gBi1 (.classMem (.cv p) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    have p1094 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        (synWb (.classMem (.cv p) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))))
        (.imp (.classMem (.cv p) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))))
        p1092 p1093
    have p1095 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        (.classMem (.cv p) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))) p0478
        p1094
    have p1103 :=
      @gEleq2 (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) (.cv q)
    have p1104 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        syntaxFormula0257
        (synWb (.classMem (.cv q) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))))
        p1090 p1103
    have p1105 :=
      @gBi1 (.classMem (.cv q) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    have p1106 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        (synWb (.classMem (.cv q) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))))
        (.imp (.classMem (.cv q) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
          (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))))
        p1104 p1105
    have p1107 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        (.classMem (.cv q) (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))) p0489
        p1106
    have p1108 :=
      @gJcad (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        (.classMem (.cv p) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))) p1095
        p1107
    have p1109 :=
      @gA1d (.classMem (.cv u) (synChwcn P)) syntaxFormula0258
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0565
    have p1120 := @gNfcv a (synCuni (.cv p)) dv_cache_0097
    have p1121 := @gIssetf a (synCuni (.cv p)) p1120
    have p1122 :=
      @gEleq1 (.cv a) (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p1123 := @gSneq (.cv a) (synCuni (.cv p))
    have p1124 :=
      @gFveq2d (.classEq (.cv a) (synCuni (.cv p))) (synCsn (.cv a))
        (synCsn (synCuni (.cv p))) (synChnqmap1 (synCfv (synC2nd) (.cv u))) p1123
    have p1125 :=
      @gEceq1 (.cv a) (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))
    have p1126 :=
      @gEqeq12d (.classEq (.cv a) (synCuni (.cv p)))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        syntaxClass0118 (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))) p1124
        p1125
    have p1127 :=
      @gImbi12d (.classEq (.cv a) (synCuni (.cv p)))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0247 syntaxFormula0119 p1122 p1126
    have p1128 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0249
        (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0259 p0973 p1127
    have p1129 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0260 a
        dv_cache_0024 p1128
    have p1130 := @gNfv syntaxFormula0259 a dv_cache_0098
    have p1131 :=
      @gN1923 (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0259 a p1130
    have p1132 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all a syntaxFormula0260)
        (.imp (synWex a (.classEq (.cv a) (synCuni (.cv p)))) syntaxFormula0259) p1129
        p1131
    have p1133 :=
      @gSyl5bi (.classMem (synCuni (.cv p)) (synCvv))
        (synWex a (.classEq (.cv a) (synCuni (.cv p))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0259 p1121 p1132
    have p1135 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0259))
        syntaxFormula0141 p1133 p0677
    have p1136 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv p)) (synCvv))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0119 p1135
    have p1137 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0119 p0621 p1136
    have p1138 :=
      @gSyl5 syntaxFormula0106
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0119 p0503 p1137
    have p1139 :=
      @gEqeq2 syntaxClass0118
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p))
    have p1140 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0106
        syntaxFormula0119 syntaxFormula0262 p1138 p1139
    have p1141 := @gBi1 syntaxFormula0261 syntaxFormula0120
    have p1142 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0106
        syntaxFormula0262 (.imp syntaxFormula0261 syntaxFormula0120) p1140 p1141
    have p1143 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0106
        syntaxFormula0261 syntaxFormula0120 p0570 p1142
    have p1144 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0106
        syntaxFormula0120 syntaxFormula0117 p1143
    have p1145 :=
      @gEqcom (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p))
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
    have p1146 :=
      @gSyl6ib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0121
        syntaxFormula0120
        (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
          (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p)))
        p1144 p1145
    have p1148 :=
      @gEqeq2d syntaxFormula0121
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))) p0580
    have p1149 :=
      @gMpbidi syntaxFormula0121
        (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
          (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv p)))
        syntaxFormula0263 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p1146 p1148
    have p1160 := @gNfcv a (synCuni (.cv q)) dv_cache_0099
    have p1161 := @gIssetf a (synCuni (.cv q)) p1160
    have p1162 :=
      @gEleq1 (.cv a) (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p1163 := @gSneq (.cv a) (synCuni (.cv q))
    have p1164 :=
      @gFveq2d (.classEq (.cv a) (synCuni (.cv q))) (synCsn (.cv a))
        (synCsn (synCuni (.cv q))) (synChnqmap1 (synCfv (synC2nd) (.cv u))) p1163
    have p1165 :=
      @gEceq1 (.cv a) (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u)))
    have p1166 :=
      @gEqeq12d (.classEq (.cv a) (synCuni (.cv q)))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        syntaxClass0122 (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u)))) p1164
        p1165
    have p1167 :=
      @gImbi12d (.classEq (.cv a) (synCuni (.cv q)))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0247 syntaxFormula0123 p1162 p1166
    have p1168 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0249
        (.classEq (.cv a) (synCuni (.cv q))) syntaxFormula0264 p0973 p1167
    have p1169 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0265 a
        dv_cache_0024 p1168
    have p1170 := @gNfv syntaxFormula0264 a dv_cache_0100
    have p1171 :=
      @gN1923 (.classEq (.cv a) (synCuni (.cv q))) syntaxFormula0264 a p1170
    have p1172 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all a syntaxFormula0265)
        (.imp (synWex a (.classEq (.cv a) (synCuni (.cv q)))) syntaxFormula0264) p1169
        p1171
    have p1173 :=
      @gSyl5bi (.classMem (synCuni (.cv q)) (synCvv))
        (synWex a (.classEq (.cv a) (synCuni (.cv q))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0264 p1161 p1172
    have p1175 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (synCuni (.cv q)) (synCvv)) syntaxFormula0264))
        syntaxFormula0148 p1173 p0697
    have p1176 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv q)) (synCvv))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0123 p1175
    have p1177 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv q)) (synCvv)) syntaxFormula0123 p0624 p1176
    have p1178 :=
      @gSyl5 syntaxFormula0106
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0123 p0590 p1177
    have p1179 :=
      @gEqeq2 syntaxClass0122
        (synCec (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
    have p1180 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0106
        syntaxFormula0123 syntaxFormula0267 p1178 p1179
    have p1181 := @gBi1 syntaxFormula0266 syntaxFormula0124
    have p1182 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0106
        syntaxFormula0267 (.imp syntaxFormula0266 syntaxFormula0124) p1180 p1181
    have p1183 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0106
        syntaxFormula0266 syntaxFormula0124 p0586 p1182
    have p1184 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0106
        syntaxFormula0124 syntaxFormula0117 p1183
    have p1185 :=
      @gEqeq2 (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
        (synCec (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
    have p1186 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0121
        syntaxFormula0124 syntaxFormula0268 p1184 p1185
    have p1187 := @gBi1 syntaxFormula0263 syntaxFormula0126
    have p1188 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0121
        syntaxFormula0268 (.imp syntaxFormula0263 syntaxFormula0126) p1186 p1187
    have p1189 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0121
        syntaxFormula0263 syntaxFormula0126 p1149 p1188
    have p1207 := @gNfcv v (synCuni (.cv q)) dv_cache_0101
    have p1208 := @gIssetf v (synCuni (.cv q)) p1207
    have p1211 := @gId syntaxFormula0269
    have p1212 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synC2nd) (.cv u)) (synCvv)) syntaxFormula0269 p0846
    have p1213 :=
      @g_pm3_2 (.classMem (synCfv (synC2nd) (.cv u)) (synCvv)) syntaxFormula0269
    have p1214 :=
      @gSyl56 syntaxFormula0269 syntaxFormula0269
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synC2nd) (.cv u)) (synCvv))
        (.imp syntaxFormula0269 syntaxFormula0270) p1211 p1212 p1213
    have p1215 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0269
        syntaxFormula0270 p1214
    have p1216 := @gHwnisoclasseqb v a (synCfv (synC2nd) (.cv u))
    have p1217 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0269
        syntaxFormula0270 syntaxFormula0272 p1215 p1216
    have p1219 := @gBiid (.classMem (.cv v) (synChwcn (synCfv (synC2nd) (.cv u))))
    have p1220 :=
      @gA1i
        (synWb (.classMem (.cv v) (synChwcn (synCfv (synC2nd) (.cv u))))
          (.classMem (.cv v) (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classEq (.cv a) (synCuni (.cv p))) p1219
    have p1221 :=
      @gAnbi12d (.classEq (.cv a) (synCuni (.cv p)))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv v) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv v) (synChwcn (synCfv (synC2nd) (.cv u)))) p1122 p1220
    have p1223 :=
      @gEqeq1d (.classEq (.cv a) (synCuni (.cv p)))
        (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (.cv v) (synChwniso (synCfv (synC2nd) (.cv u)))) p1125
    have p1224 :=
      @gBreq1 (.cv a) (synCuni (.cv p)) (.cv v)
        (synChwniso (synCfv (synC2nd) (.cv u)))
    have p1225 :=
      @gBibi12d (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0271 syntaxFormula0273
        (synWbr (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv v))
        (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv v))
        p1223 p1224
    have p1226 :=
      @gImbi12d (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0269 syntaxFormula0274
        syntaxFormula0272 syntaxFormula0275 p1221 p1225
    have p1227 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0269 syntaxFormula0272) (.classEq (.cv a) (synCuni (.cv p)))
        syntaxFormula0276 p1217 p1226
    have p1228 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0277 a
        dv_cache_0024 p1227
    have p1229 := @gNfv syntaxFormula0276 a dv_cache_0102
    have p1230 :=
      @gN1923 (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0276 a p1229
    have p1231 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all a syntaxFormula0277)
        (.imp (synWex a (.classEq (.cv a) (synCuni (.cv p)))) syntaxFormula0276) p1228
        p1230
    have p1232 :=
      @gSyl5bi (.classMem (synCuni (.cv p)) (synCvv))
        (synWex a (.classEq (.cv a) (synCuni (.cv p))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0276 p1121 p1231
    have p1234 :=
      @gA1ii (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0278)
        syntaxFormula0141 p1232 p0677
    have p1236 :=
      @gA1i
        (synWb (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
          (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classEq (.cv v) (synCuni (.cv q))) p0679
    have p1237 :=
      @gEleq1 (.cv v) (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u)))
    have p1238 :=
      @gAnbi12d (.classEq (.cv v) (synCuni (.cv q)))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv v) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCfv (synC2nd) (.cv u)))) p1236
        p1237
    have p1239 :=
      @gEceq1 (.cv v) (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u)))
    have p1240 :=
      @gEqeq2d (.classEq (.cv v) (synCuni (.cv q)))
        (synCec (.cv v) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (synCuni (.cv q)) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u)))) p1239
    have p1241 :=
      @gBreq2 (.cv v) (synCuni (.cv q)) (synCuni (.cv p))
        (synChwniso (synCfv (synC2nd) (.cv u)))
    have p1242 :=
      @gBibi12d (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0273 syntaxFormula0126
        (synWbr (synCuni (.cv p)) (synChwniso (synCfv (synC2nd) (.cv u))) (.cv v))
        syntaxFormula0127 p1240 p1241
    have p1243 :=
      @gImbi12d (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0274 syntaxFormula0125
        syntaxFormula0275 syntaxFormula0128 p1238 p1242
    have p1244 :=
      @gImbi2d (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0276 syntaxFormula0279
        (.classMem (synCuni (.cv p)) (synCvv)) p1243
    have p1245 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0278
        (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0280 p1234 p1244
    have p1246 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0281 v
        dv_cache_0103 p1245
    have p1247 := @gNfcv v (synCuni (.cv p)) dv_cache_0104
    have p1248 := @gNfel1 v (synCuni (.cv p)) (synCvv) dv_cache_0105 p1247
    have p1249 := @gNfv syntaxFormula0279 v dv_cache_0106
    have p1250 :=
      @gNfim (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0279 v p1248 p1249
    have p1251 :=
      @gN1923 (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0280 v p1250
    have p1252 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all v syntaxFormula0281)
        (.imp (synWex v (.classEq (.cv v) (synCuni (.cv q)))) syntaxFormula0280) p1246
        p1251
    have p1253 :=
      @gSyl5bi (.classMem (synCuni (.cv q)) (synCvv))
        (synWex v (.classEq (.cv v) (synCuni (.cv q))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0280 p1208 p1252
    have p1255 := @gA1ii syntaxFormula0283 syntaxFormula0148 p1253 p0697
    have p1257 := @gA1ii syntaxFormula0283 syntaxFormula0141 p1255 p0677
    have p1258 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv q)) (synCvv)) (.classMem (synCuni (.cv p)) (synCvv))
        syntaxFormula0279 p1257
    have p1259 :=
      @gImp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv p)) (synCvv)) (.classMem (synCuni (.cv q)) (synCvv))
        syntaxFormula0279 p1258
    have p1260 :=
      @gSyl5 syntaxFormula0125 syntaxFormula0149
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0279 p0626 p1259
    have p1261 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0125
        syntaxFormula0128 p1260
    have p1262 :=
      @gSyl5 syntaxFormula0121 syntaxFormula0125
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0128 p0605 p1261
    have p1263 := @gBi1 syntaxFormula0126 syntaxFormula0127
    have p1264 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0121
        syntaxFormula0128 (.imp syntaxFormula0126 syntaxFormula0127) p1262 p1263
    have p1265 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0121
        syntaxFormula0126 syntaxFormula0127 p1189 p1264
    have p1266 :=
      @gA2d (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0127
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))) p0705
    have p1267 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0121 syntaxFormula0127) (.classMem (.cv u) (synChwcn P))
        syntaxFormula0284 p1265 p1266
    have p1268 :=
      @gA2d (.classMem (.cv u) (synChwcn P)) syntaxFormula0121
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q)))
        syntaxFormula0151 p0722
    have p1269 :=
      @gSyld (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0284
        (.imp syntaxFormula0121 syntaxFormula0151) p1267 p1268
    have p1271 :=
      @gSyl8 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0121
        syntaxFormula0151 syntaxFormula0156 p1269 p0724
    have p1273 :=
      @gSyl8 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0121
        syntaxFormula0156 syntaxFormula0157 p1271 p0726
    have p1274 := Nominal.ax2 syntaxFormula0121 syntaxFormula0114 syntaxFormula0155
    have p1275 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0121 syntaxFormula0157)
        (.imp syntaxFormula0258 syntaxFormula0285) p1273 p1274
    have p1276 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0258
        syntaxFormula0285 p1109 p1275
    have p1277 :=
      @gA2d (.classMem (.cv u) (synChwcn P)) syntaxFormula0121 syntaxFormula0155
        syntaxFormula0164 p0747
    have p1278 :=
      @gSyld (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0285
        (.imp syntaxFormula0121 syntaxFormula0164) p1276 p1277
    have p1279 :=
      @gExp4a (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0106
        syntaxFormula0117 syntaxFormula0164 p1278
    have p1280 :=
      @gA1dd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0286
        syntaxFormula0103 p1279
    have p1281 := Nominal.ax2 syntaxFormula0103 syntaxFormula0106 syntaxFormula0167
    have p1282 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0103 syntaxFormula0286)
        (.imp syntaxFormula0287 syntaxFormula0288) p1280 p1281
    have p1283 :=
      @gMpdi (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0287
        syntaxFormula0288 p1108 p1282
    have p1284 := Nominal.ax2 syntaxFormula0103 syntaxFormula0117 syntaxFormula0164
    have p1285 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0288
        (.imp syntaxFormula0289 syntaxFormula0290) p1283 p1284
    have p1286 :=
      @gMpdi (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0289
        syntaxFormula0290 p1078 p1285
    have p1288 :=
      @gSyl8 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        syntaxFormula0164 syntaxFormula0168 p1286 p0752
    have p1290 :=
      @gSyl8 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0103
        syntaxFormula0168 syntaxFormula0169 p1288 p0754
    have p1291 :=
      Nominal.ax2 syntaxFormula0103
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv p)))
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q)))
    have p1292 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0103 syntaxFormula0169)
        (.imp syntaxFormula0255 syntaxFormula0291) p1290 p1291
    have p1293 :=
      @gMpdi (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0255
        syntaxFormula0291 p1051 p1292
    have p1304 :=
      @gBiimpd syntaxFormula0103
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q)))
        (.classEq (.cv y) (.cv z)) p0766
    have p1305 :=
      @gA2i syntaxFormula0103
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q)))
        (.classEq (.cv y) (.cv z)) p1304
    have p1306 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0291
        (.imp syntaxFormula0103 (.classEq (.cv y) (.cv z))) p1293 p1305
    have p1307 :=
      @gExp4a (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0102
        syntaxFormula0100 (.classEq (.cv y) (.cv z)) p1306
    have p1308 :=
      @gAlimdv (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0292 q dv_cache_0061
        p1307
    have p1309 := @gAlim syntaxFormula0102 syntaxFormula0170 q
    have p1310 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (.all q (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y))
        (.all q syntaxFormula0292) syntaxFormula0293 p1308 p1309
    have p1311 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.all q (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y))
        (.classMem (.cv u) (synChwcn P)) syntaxFormula0293 p1037 p1310
    have p1312 :=
      @gSyl7 syntaxFormula0102 syntaxFormula0171 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0172 p0431 p1311
    have p1314 :=
      @gSyl8 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0102
        syntaxFormula0172 syntaxFormula0173 p1312 p0771
    have p1316 :=
      @gA1i (.imp (synWex q (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0773
    have p1317 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp (synWex q (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z)))
        syntaxFormula0102 p1316
    have p1318 :=
      @gImim2 (synWex q (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z))
        syntaxFormula0101
    have p1319 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0102
        (.imp (synWex q (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z)))
        (.imp syntaxFormula0173 syntaxFormula0294) p1317 p1318
    have p1320 :=
      @gA2d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0102
        syntaxFormula0173 syntaxFormula0294 p1319
    have p1321 :=
      @gSylcom (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0102 syntaxFormula0173) syntaxFormula0295 p1314 p1320
    have p1322 :=
      Nominal.ax2 syntaxFormula0102 syntaxFormula0101 (.classEq (.cv y) (.cv z))
    have p1323 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0295
        (.imp syntaxFormula0254 syntaxFormula0296) p1321 p1322
    have p1324 :=
      @gMpdi (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0254
        syntaxFormula0296 p1035 p1323
    have p1325 :=
      @gExp4a (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0095
        syntaxFormula0097 (.classEq (.cv y) (.cv z)) p1324
    have p1326 :=
      @gAlimdv (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0297 p dv_cache_0063
        p1325
    have p1327 := @gAlim syntaxFormula0095 syntaxFormula0174 p
    have p1328 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (.all p (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y))
        (.all p syntaxFormula0297) syntaxFormula0298 p1326 p1327
    have p1329 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.all p (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y))
        (.classMem (.cv u) (synChwcn P)) syntaxFormula0298 p1029 p1328
    have p1330 :=
      @gSyl7 syntaxFormula0095 syntaxFormula0175 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0176 p0425 p1329
    have p1332 :=
      @gSyl8 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0095
        syntaxFormula0176 syntaxFormula0177 p1330 p0779
    have p1334 :=
      @gA1i (.imp (synWex p (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0781
    have p1335 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp (synWex p (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z)))
        syntaxFormula0095 p1334
    have p1336 :=
      @gImim2 (synWex p (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z))
        syntaxFormula0098
    have p1337 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0095
        (.imp (synWex p (.classEq (.cv y) (.cv z))) (.classEq (.cv y) (.cv z)))
        (.imp syntaxFormula0177 syntaxFormula0299) p1335 p1336
    have p1338 :=
      @gA2d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0095
        syntaxFormula0177 syntaxFormula0299 p1337
    have p1339 :=
      @gSylcom (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0095 syntaxFormula0177) syntaxFormula0300 p1332 p1338
    have p1340 :=
      Nominal.ax2 syntaxFormula0095 syntaxFormula0098 (.classEq (.cv y) (.cv z))
    have p1341 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0300
        (.imp syntaxFormula0253 syntaxFormula0178) p1339 p1340
    have p1342 :=
      @gMpdi (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0253
        syntaxFormula0178 p1027 p1341
    have p1343 :=
      @gAlrimdv (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0178 z dv_cache_0065
        dv_cache_0107 p1342
    have p1344 :=
      @gAlrimdv (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0179 y dv_cache_0057
        dv_cache_0108 p1343
    have p1345 :=
      @gAlrimdv (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0180 x dv_cache_0055
        dv_cache_0089 p1344
    exact
      continuation p0973 p0974 p0977 p0986 p0997 p1023 p1089 p1121 p1123 p1161 p1163 p1208
        p1248 p1345

end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `ReplaySupport.CodeCover5`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_cfbhnqinjcodecoverddndv_stage5`. -/
@[expose]
noncomputable def gCfbhnqinjcodecoverddndvStage5 (u : Var) (P : Class) (k : Var)
    (Y : Class) (p0000 : _) (p0001 : _) (p0011 : _) (p0013 : _) (p0022 : _) (p0036 : _)
    (p0050 : _) (p0069 : _) (p0082 : _) (p0084 : _) (p0140 : _) (p0282 : _) (p0286 : _)
    (p0288 : _) (p0296 : _) (p0306 : _) (p0310 : _) (p0330 : _) (p0364 : _) (p0534 : _)
    (p0541 : _) (p0548 : _) (p0553 : _) (p0791 : _) (p0794 : _) (p0796 : _) (p0798 : _)
    (p0805 : _) (p0807 : _) (p0809 : _) (p0815 : _) (p0820 : _) (p0825 : _) (p0827 : _)
    (p0831 : _) (p0839 : _) (p0848 : _) (p0973 : _) (p0974 : _) (p0977 : _) (p0986 : _)
    (p0997 : _) (p1023 : _) (p1089 : _) (p1345 : _) {Result : Type}
    (continuation : _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → Result) :=
  show Result from
    by
    let proofSupport : Finset Var :=
      ({ u } : Finset Var) ∪ P.fv ∪ ({ k } : Finset Var) ∪ Y.fv
    let r : Var := freshVar proofSupport 0
    let y : Var := freshVar proofSupport 1
    let x : Var := freshVar proofSupport 2
    let f : Var := freshVar proofSupport 3
    let a : Var := freshVar proofSupport 4
    let z : Var := freshVar proofSupport 5
    let q : Var := freshVar proofSupport 7
    let h : Var := freshVar proofSupport 8
    let v : Var := freshVar proofSupport 11
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
    have fresh_a_not_P : a ∉ P.fv := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_a_ne_k : a ≠ k := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_a_not_Y : a ∉ Y.fv := by
      intro h
      exact fresh_a (Finset.mem_union_right _ (h))
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
    have fresh_z_ne_k : z ≠ k := by
      intro h
      exact
        fresh_z
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_z_not_Y : z ∉ Y.fv := by
      intro h
      exact fresh_z (Finset.mem_union_right _ (h))
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
    have fresh_q_ne_k : q ≠ k := by
      intro h
      exact
        fresh_q
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_q_not_Y : q ∉ Y.fv := by
      intro h
      exact fresh_q (Finset.mem_union_right _ (h))
    have fresh_v : v ∉ proofSupport :=
      by
      change freshVar proofSupport 11 ∉ proofSupport
      exact freshVar_not_mem proofSupport 11
    have fresh_v_ne_u : v ≠ u := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_v_ne_k : v ≠ k := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_r_ne_f : r ≠ f :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
    have fresh_f_ne_r : f ≠ r := Ne.symm fresh_r_ne_f
    have fresh_r_ne_v : r ≠ v :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 0) (j := 11) (by decide)
    have fresh_v_ne_r : v ≠ r := Ne.symm fresh_r_ne_v
    have fresh_y_ne_x : y ≠ x :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 2
      exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
    have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
    have fresh_y_ne_z : y ≠ z :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
    have fresh_x_ne_a : x ≠ a :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
    have fresh_x_ne_z : x ≠ z :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
    have fresh_f_ne_v : f ≠ v :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 3) (j := 11) (by decide)
    have fresh_v_ne_f : v ≠ f := Ne.symm fresh_f_ne_v
    have fresh_a_ne_z : a ≠ z :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
    have fresh_a_ne_q : a ≠ q :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
    have fresh_q_ne_a : q ≠ a := Ne.symm fresh_a_ne_q
    have fresh_z_ne_q : z ≠ q :=
      by
      change freshVar proofSupport 5 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
    have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
    have dv_cache_0002 : f ≠ r := by exact (show f ≠ r from (by exact fresh_f_ne_r))
    have dv_cache_0007 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
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
    have dv_cache_0096 : q ∉ ((synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_u, fresh_q_not_Y, fresh_q_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0107 : z ∉ ((synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_u, fresh_z_not_Y, fresh_z_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0109 : a ∉ ((Class.cv q)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_q, not_false_eq_true])
    have dv_cache_0110 :
      a ∉
        ((Wff.classMem (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
            (synChnord (synCfv (synC2nd) (.cv u))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_q, fresh_a_ne_u, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0111 : q ∉ ((synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0112 : q ∉ ((synChnord (synCfv (synC2nd) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0113 : q ∉ ((synChnqmap1 (synCfv (synC2nd) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0114 : a ∉ ((Class.cv z)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_z, not_false_eq_true])
    have dv_cache_0115 : a ∉ ((synChwniso (synCfv (synC2nd) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0116 : q ∉ ((synCsn (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_a,
            not_false_eq_true])
    have dv_cache_0117 :
      q ∉
        ((Wff.classEq (.cv z) (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u)))
              (synCsn (.cv a))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_z, fresh_q_ne_a, fresh_q_ne_u,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0118 :
      a ∉
        ((synWrex q (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) (.classEq (.cv z)
              (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_u,
            fresh_a_ne_z, fresh_a_ne_q, compact_fv_not_mem_empty, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0119 : z ∉ ((synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0120 : z ∉ ((synChnord (synCfv (synC2nd) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0121 : z ∉ ((synChnqmap1 (synCfv (synC2nd) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0122 : q ≠ z := by exact (show q ≠ z from (by exact fresh_q_ne_z))
    have dv_cache_0123 :
      a ∉
        ((Wff.imp (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))
            (.classMem (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
              (synChnord (synCfv (synC2nd) (.cv u)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_u, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    have dv_cache_0124 : r ∉ ((synCvv)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0125 :
      r ∉
        ((Wff.classEq (synCfv (synChwgen)
              (synCop (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
                (synCfv (synC1st) (.cv u))))
            (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            Finset.mem_union, Finset.mem_singleton, fresh_r_ne_k, fresh_r_ne_u,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0126 :
      r ∉ ((Wff.classEq (.cv f) (synCres (.cv k) (synCfv (synC2nd) (.cv u))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_r_ne_f, fresh_r_ne_k, fresh_r_ne_u,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0127 : f ∉ ((synCres (.cv k) (synCfv (synC2nd) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
            Finset.mem_singleton, fresh_f_ne_k, fresh_f_ne_u, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0128 : f ∉ ((synChwbij)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0129 :
      f ∉
        ((synWrex r (synCvv) (.classEq (synCfv (synChwgen)
                (synCop (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (.cv r)))
              (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_f_ne_k,
            fresh_f_ne_u, fresh_f_ne_r, compact_fv_not_mem_empty, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0130 :
      f ∉ ((Wff.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            Finset.mem_union, Finset.mem_singleton, fresh_f_ne_v, fresh_f_ne_u,
            fresh_f_ne_k, or_false, not_false_eq_true])
    have dv_cache_0131 :
      r ∉ ((Wff.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            Finset.mem_union, Finset.mem_singleton, fresh_r_ne_v, fresh_r_ne_u,
            fresh_r_ne_k, or_false, not_false_eq_true])
    have dv_cache_0132 : f ∉ ((synCvv)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0133 : f ≠ u := by exact (show f ≠ u from (by exact fresh_f_ne_u))
    have dv_cache_0134 : f ≠ v := by exact (show f ≠ v from (by exact fresh_f_ne_v))
    have dv_cache_0135 : r ≠ u := by exact (show r ≠ u from (by exact fresh_r_ne_u))
    have dv_cache_0136 : r ≠ v := by exact (show r ≠ v from (by exact fresh_r_ne_v))
    have dv_cache_0137 : v ∉ ((synCfv (synChncodetrnfn (.cv k)) (.cv u))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_v_ne_u, fresh_v_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0138 :
      v ∉
        ((synWb (synWbr (.cv u) (synChwniso (synCvv))
              (synCfv (synChncodetrnfn (.cv k)) (.cv u))) (synWa
              (synWa (.classMem (.cv u) (synChwcn (synCvv)))
                (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCvv))))
              (synWrex f (synChwbij) (synWrex r (synCvv)
                  (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r))) (synCop (.cv u)
                      (synCfv (synChncodetrnfn (.cv k)) (.cv u))))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwbij,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwgen,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_u, fresh_v_ne_k,
            fresh_v_ne_f, fresh_v_ne_r, compact_fv_not_mem_empty, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0139 : a ∉ ((synCfv (synChncodetrnfn (.cv k)) (.cv u))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_u, fresh_a_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0140 :
      x ∉ ((synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_k, fresh_x_ne_a, or_false,
            not_false_eq_true])
    have dv_cache_0141 :
      x ∉
        ((synCop (synCsn (.cv a))
            (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0142 :
      x ∉
        ((synCsymdif (synCins2 (synCsset)) (synCins3 (synCcom (synCsset)
                (synCcnv (synCsi (synChwniso (synCrn (.cv k))))))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_k, compact_fv_not_mem_empty, or_false,
            not_false_eq_true])
    let syntaxFormula0005 : Wff :=
      (.classEq (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCfv (synC2nd) (.cv u)))
    let syntaxFormula0009 : Wff :=
      (synWf1o (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxClass0035 : Class :=
      (synCcom (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
    let syntaxClass0036 : Class :=
      (synCcom syntaxClass0035 (synCcnv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxClass0042 : Class :=
      (synCop syntaxClass0036 (synCrn (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0060 : Wff :=
      (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCrn (.cv k))))
    let syntaxFormula0065 : Wff :=
      (synWss (synCfv (synC1st) (.cv a))
        (synCxp (synCfv (synC2nd) (.cv a)) (synCfv (synC2nd) (.cv a))))
    let syntaxFormula0081 : Wff :=
      (synWfn (synChnqmap1 (synCfv (synC2nd) (.cv u)))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
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
    let syntaxFormula0109 : Wff :=
      (synWa (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y)))
    let syntaxFormula0110 : Wff :=
      (.classMem (synCop (synCfv (synC1st) (.cv a)) (synCfv (synC2nd) (.cv a)))
        (synChwcodes (synCun P Y)))
    let syntaxFormula0111 : Wff :=
      (synWa (.classMem (.cv a) (synChwcodes (synCun P Y))) syntaxFormula0065)
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
    let syntaxFormula0195 : Wff :=
      (.classMem (synCsn (.cv a)) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0247 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0301 : Wff :=
      (.classEq (synCdm (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)))
        syntaxClass0184)
    let syntaxFormula0302 : Wff :=
      (.classEq syntaxClass0184 (synCrn (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
    let syntaxClass0303 : Class :=
      (synCqs (synChwcn (synCfv (synC2nd) (.cv u)))
        (synChwniso (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0304 : Wff :=
      (.classMem (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))) syntaxClass0303)
    let syntaxFormula0305 : Wff :=
      (.classMem (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0306 : Wff :=
      (.classMem (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synChnord (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0307 : Wff := (synWb syntaxFormula0306 syntaxFormula0305)
    let syntaxFormula0308 : Wff := (synWb syntaxFormula0305 syntaxFormula0306)
    let syntaxFormula0309 : Wff := (.imp syntaxFormula0305 syntaxFormula0306)
    let syntaxFormula0310 : Wff :=
      (synWa (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv q) (synCsn (.cv a))))
    let syntaxFormula0311 : Wff :=
      (.classMem (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
        (synChnord (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0312 : Wff :=
      (synWral q (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0311)
    let syntaxFormula0313 : Wff :=
      (synWss (synCrn (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0314 : Wff :=
      (synWf (synChnqmap1 (synCfv (synC2nd) (.cv u)))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0315 : Wff :=
      (synWa (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))))
    let syntaxFormula0316 : Wff :=
      (.classEq (.cv z) (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
    let syntaxFormula0317 : Wff :=
      (synWb (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0316)
    let syntaxFormula0318 : Wff := (synWa syntaxFormula0195 syntaxFormula0316)
    let syntaxFormula0319 : Wff :=
      (.classEq (.cv z) (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q)))
    let syntaxFormula0320 : Wff :=
      (synWrex q (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0319)
    let syntaxFormula0321 : Wff :=
      (synWral z (synChnord (synCfv (synC2nd) (.cv u))) syntaxFormula0320)
    let syntaxFormula0322 : Wff := (synWb syntaxFormula0301 syntaxFormula0186)
    let syntaxFormula0323 : Wff :=
      (.imp (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0188)
    let syntaxFormula0324 : Wff := (.imp (.classEq (.cv a) (.cv u)) syntaxFormula0323)
    let syntaxFormula0325 : Wff := (synWb syntaxFormula0092 syntaxFormula0191)
    let syntaxFormula0326 : Wff := (.imp syntaxFormula0092 syntaxFormula0191)
    let syntaxClass0327 : Class :=
      (synCop (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (synCfv (synC1st) (.cv u)))
    let syntaxClass0328 : Class := (synCfv (synChwgen) syntaxClass0327)
    let syntaxClass0329 : Class :=
      (synCop (synCfv (synC1st) (.cv u))
        (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u)))))
    let syntaxClass0330 : Class := (synCop syntaxClass0329 syntaxClass0042)
    let syntaxFormula0331 : Wff := (.classEq syntaxClass0328 syntaxClass0330)
    let syntaxFormula0332 : Wff :=
      (.classEq syntaxClass0329
        (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))))
    let syntaxFormula0333 : Wff := (.classEq syntaxClass0329 (.cv u))
    let syntaxFormula0334 : Wff := (synWb syntaxFormula0332 syntaxFormula0333)
    let syntaxClass0335 : Class := (synCop (.cv u) syntaxClass0042)
    let syntaxFormula0336 : Wff := (.classEq syntaxClass0330 syntaxClass0335)
    let syntaxFormula0337 : Wff :=
      (.classEq syntaxClass0330 (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
    let syntaxFormula0338 : Wff :=
      (.classEq syntaxClass0328 (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
    let syntaxFormula0339 : Wff := (synWb syntaxFormula0331 syntaxFormula0338)
    let syntaxFormula0340 : Wff :=
      (synWa (.classMem (synCfv (synC1st) (.cv u)) (synCvv)) syntaxFormula0338)
    let syntaxClass0341 : Class :=
      (synCfv (synChwgen) (synCop (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (.cv r)))
    let syntaxFormula0342 : Wff :=
      (.classEq syntaxClass0341 (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
    let syntaxFormula0343 : Wff := (synWrex r (synCvv) syntaxFormula0342)
    let syntaxFormula0344 : Wff :=
      (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r)))
        (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
    let syntaxFormula0345 : Wff := (synWrex r (synCvv) syntaxFormula0344)
    let syntaxFormula0346 : Wff := (synWrex f (synChwbij) syntaxFormula0345)
    let syntaxFormula0347 : Wff :=
      (synWa (.classMem (.cv u) (synChwcn (synCvv)))
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCvv))))
    let syntaxFormula0348 : Wff :=
      (.classEq (synCfv (synChwgen) (synCop (.cv f) (.cv r))) (synCop (.cv u) (.cv v)))
    let syntaxFormula0349 : Wff := (synWrex r (synCvv) syntaxFormula0348)
    let syntaxFormula0350 : Wff := (synWrex f (synChwbij) syntaxFormula0349)
    let syntaxFormula0351 : Wff :=
      (synWbr (.cv u) (synChwniso (synCvv)) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
    let syntaxFormula0352 : Wff :=
      (synWa (synWa (.classMem (.cv u) (synChwcn (synCvv)))
          (.classMem (.cv v) (synChwcn (synCvv)))) syntaxFormula0350)
    let syntaxFormula0353 : Wff := (synWa syntaxFormula0347 syntaxFormula0346)
    let syntaxFormula0354 : Wff := (synWb syntaxFormula0351 syntaxFormula0353)
    let syntaxFormula0355 : Wff := (synWb syntaxFormula0353 syntaxFormula0351)
    let syntaxFormula0356 : Wff := (.imp syntaxFormula0353 syntaxFormula0351)
    let syntaxFormula0357 : Wff :=
      (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCun P Y)))
    let syntaxFormula0358 : Wff :=
      (synWbr (.cv u) (synChwniso (synCun P Y)) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
    let syntaxFormula0359 : Wff := (synWb syntaxFormula0351 syntaxFormula0358)
    let syntaxClass0360 : Class :=
      (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso (synCun P Y)))
    let syntaxFormula0361 : Wff :=
      (.classEq (synCec (.cv u) (synChwniso (synCun P Y))) syntaxClass0360)
    let syntaxFormula0362 : Wff := (synWb syntaxFormula0361 syntaxFormula0358)
    let syntaxFormula0363 : Wff := (synWb syntaxFormula0358 syntaxFormula0361)
    let syntaxFormula0364 : Wff := (.imp syntaxFormula0358 syntaxFormula0361)
    let syntaxFormula0365 : Wff := (.classEq syntaxClass0190 syntaxClass0360)
    let syntaxFormula0366 : Wff := (synWb syntaxFormula0191 syntaxFormula0365)
    let syntaxClass0367 : Class :=
      (synCres (synCimage (synChwniso (synCrn (.cv k))))
        (synCpw1 (synChwcn (synCrn (.cv k)))))
    let syntaxClass0368 : Class :=
      (synCop (synCsn (.cv a)) (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
    let syntaxClass0369 : Class :=
      (synCins3 (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCrn (.cv k)))))))
    let syntaxClass0370 : Class := (synCsymdif (synCins2 (synCsset)) syntaxClass0369)
    let syntaxClass0371 : Class := (synCop (synCsn (.cv x)) syntaxClass0368)
    let syntaxFormula0372 : Wff :=
      (synWbr (synCsn (.cv x)) (synCsset)
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
    have p1346 :=
      @gDffun2 x y z syntaxClass0090 dv_cache_0066 dv_cache_0067 dv_cache_0068
        dv_cache_0007 dv_cache_0069 dv_cache_0070
    have p1347_e01_recanon :
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
        p1346
    have p1347 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0181
        (synWfun syntaxClass0090) p1345 p1347_e01_recanon
    have p1351 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (synWfun syntaxClass0090)
        (synWfun (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y))) p1347 p0791
    have p1354 :=
      @gA1i syntaxFormula0301 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0794
    have p1357 :=
      @gSyl5eq (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synCrn (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (synCdm (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) p0798 p1089
    have p1361 :=
      @gSseq12 (synCrn (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synCdm (synChnqmap1 (synCun P Y))) (synCpw1 (synChwcn (synCun P Y)))
    have p1362 :=
      @gSylancl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (synCrn (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
          (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (.classEq (synCdm (synChnqmap1 (synCun P Y))) (synCpw1 (synChwcn (synCun P Y))))
        (synWb syntaxFormula0183 syntaxFormula0182) p1357 p0805 p1361
    have p1363 :=
      @gSyl5ibrcom (.classMem (.cv u) (synChwcn P)) syntaxFormula0183
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0182 p0796 p1362
    have p1365 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0183
        syntaxFormula0185 p1363 p0807
    have p1367 :=
      @gEqcomi (synCrn (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synCdm (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u))))) p0809
    have p1368 :=
      @gA1i
        (.classEq (synCdm (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
          (synCrn (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p1367
    have p1369 :=
      @gEqeq2d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synCdm (synCcnv (synChnqmap1 (synCfv (synC2nd) (.cv u)))))
        (synCrn (synChnqmap1 (synCfv (synC2nd) (.cv u)))) syntaxClass0184 p1368
    have p1370 :=
      @gMpbidi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0185
        syntaxFormula0302 (.classMem (.cv u) (synChwcn P)) p1365 p1369
    have p1371 :=
      @gElpw1 a (.cv q) (synChwcn (synCfv (synC2nd) (.cv u))) dv_cache_0109
        dv_cache_0046
    have p1372 := @gId (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
    have p1373 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synChwniso (synCfv (synC2nd) (.cv u))) (synCvv))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) p0848
    have p1374 :=
      @gEcelqsg (synChwcn (synCfv (synC2nd) (.cv u))) (.cv a)
        (synChwniso (synCfv (synC2nd) (.cv u))) (synCvv)
    have p1375 :=
      @gEx (.classMem (synChwniso (synCfv (synC2nd) (.cv u))) (synCvv))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0304
        p1374
    have p1376 :=
      @gSyl56 (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synChwniso (synCfv (synC2nd) (.cv u))) (synCvv))
        (.imp (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0304)
        p1372 p1373 p1375
    have p1377 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0304
        p1376
    have p1378 := (Nominal.classEqRefl (synChnord (synCfv (synC2nd) (.cv u))))
    have p1379 :=
      @gEleq2i (synChnord (synCfv (synC2nd) (.cv u))) syntaxClass0303
        (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))) p1378
    have p1380 :=
      @gSyl6ibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0304
        syntaxFormula0305 p1377 p1379
    have p1381 :=
      @gEleq1 (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u)))
    have p1382 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0247
        syntaxFormula0307 p0973 p1381
    have p1383 := @gBicom syntaxFormula0306 syntaxFormula0305
    have p1384 :=
      @gSyl6ib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0307
        syntaxFormula0308 p1382 p1383
    have p1385 := @gBi1 syntaxFormula0305 syntaxFormula0306
    have p1386 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0308
        syntaxFormula0309 p1384 p1385
    have p1387 := @gId syntaxFormula0305
    have p1388 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0309))
        (.imp syntaxFormula0305 syntaxFormula0305) p1386 p1387
    have p1389 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0305
        syntaxFormula0306 p1380 p1388
    have p1390 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0306
        (.classEq (.cv q) (synCsn (.cv a))) p1389
    have p1391 :=
      @gSimpr (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv q) (synCsn (.cv a)))
    have p1392 :=
      @gFveq2 (.cv q) (synCsn (.cv a)) (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p1393 :=
      @gSyl syntaxFormula0310 (.classEq (.cv q) (synCsn (.cv a)))
        (.classEq (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
          (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
        p1391 p1392
    have p1394 :=
      @gEleq1d syntaxFormula0310
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synChnord (synCfv (synC2nd) (.cv u))) p1393
    have p1395 := @gBiimprd syntaxFormula0310 syntaxFormula0311 syntaxFormula0306 p1394
    have p1396 :=
      @gSylcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0310
        syntaxFormula0306 syntaxFormula0311 p1390 p1395
    have p1397 :=
      @gExp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv q) (synCsn (.cv a))) syntaxFormula0311 p1396
    have p1398 :=
      @gRexlimdv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (.cv q) (synCsn (.cv a))) syntaxFormula0311 a
        (synChwcn (synCfv (synC2nd) (.cv u))) dv_cache_0110 dv_cache_0024 p1397
    have p1399 :=
      @gSyl5bi (.classMem (.cv q) (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))))
        (synWrex a (synChwcn (synCfv (synC2nd) (.cv u)))
          (.classEq (.cv q) (synCsn (.cv a))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0311 p1371 p1398
    have p1400 :=
      @gRalrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0311 q
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) dv_cache_0096 p1399
    have p1401 :=
      @gJca (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0081
        syntaxFormula0312 p0997 p1400
    have p1402 :=
      @gFnfvrnss q (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u)))
        (synChnqmap1 (synCfv (synC2nd) (.cv u))) dv_cache_0111 dv_cache_0112
        dv_cache_0113
    have p1403 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa syntaxFormula0081 syntaxFormula0312) syntaxFormula0313 p1401 p1402
    have p1404 :=
      @gJca (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0081
        syntaxFormula0313 p0997 p1403
    have p1405 := (Nominal.biimpRefl syntaxFormula0314)
    have p1406 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa syntaxFormula0081 syntaxFormula0313) syntaxFormula0314 p1404 p1405
    have p1408 :=
      @gEleq2i (synChnord (synCfv (synC2nd) (.cv u))) syntaxClass0303 (.cv z) p1378
    have p1409 :=
      @gBiimpi (.classMem (.cv z) (synChnord (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv z) syntaxClass0303) p1408
    have p1410 :=
      @gElqsi a (synChwcn (synCfv (synC2nd) (.cv u))) (.cv z)
        (synChwniso (synCfv (synC2nd) (.cv u))) dv_cache_0046 dv_cache_0114
        dv_cache_0115
    have p1411 :=
      @gSyl (.classMem (.cv z) (synChnord (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv z) syntaxClass0303)
        (synWrex a (synChwcn (synCfv (synC2nd) (.cv u)))
          (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))))
        p1409 p1410
    have p1414 :=
      @gAdantr (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        syntaxFormula0195
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
        p0831
    have p1415 :=
      @gSimpr (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
    have p1416 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0247
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
        p0973
    have p1417 :=
      @gEqcom (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
    have p1418 :=
      @gSyl6ib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0315
        syntaxFormula0247
        (.classEq (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
          (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
        p1416 p1417
    have p1419 :=
      @gEqeq2 (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))) (.cv z)
    have p1420 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0315
        (.classEq (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
          (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))))
        syntaxFormula0317 p1418 p1419
    have p1421 :=
      @gBi1
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0316
    have p1422 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0315
        syntaxFormula0317
        (.imp (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
          syntaxFormula0316)
        p1420 p1421
    have p1423 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0315
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0316 p1415 p1422
    have p1424 := @g_pm3_2 syntaxFormula0195 syntaxFormula0316
    have p1425 :=
      @gSyl9 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0315
        syntaxFormula0316 syntaxFormula0195 syntaxFormula0318 p1423 p1424
    have p1426 :=
      @gSyl5 syntaxFormula0315 syntaxFormula0195
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0315 syntaxFormula0318) p1414 p1425
    have p1427 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0315
        syntaxFormula0318 p1426
    have p1429 :=
      @gEqeq2d (.classEq (.cv q) (synCsn (.cv a)))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (.cv q))
        (synCfv (synChnqmap1 (synCfv (synC2nd) (.cv u))) (synCsn (.cv a))) (.cv z)
        p1392
    have p1430 :=
      @gRspcev syntaxFormula0319 syntaxFormula0316 q (synCsn (.cv a))
        (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u)))) dv_cache_0116 dv_cache_0111
        dv_cache_0117 p1429
    have p1431 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0315
        syntaxFormula0318 syntaxFormula0320 p1427 p1430
    have p1432 :=
      @gExp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0320 p1431
    have p1433 :=
      @gRexlimdv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u)))))
        syntaxFormula0320 a (synChwcn (synCfv (synC2nd) (.cv u))) dv_cache_0118
        dv_cache_0024 p1432
    have p1434 :=
      @gSyl5 (.classMem (.cv z) (synChnord (synCfv (synC2nd) (.cv u))))
        (synWrex a (synChwcn (synCfv (synC2nd) (.cv u)))
          (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0320 p1411 p1433
    have p1435 :=
      @gRalrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0320 z
        (synChnord (synCfv (synC2nd) (.cv u))) dv_cache_0107 p1434
    have p1436 :=
      @gJca (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0314
        syntaxFormula0321 p1406 p1435
    have p1437 :=
      @gDffo3 q z (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u)))
        (synChnqmap1 (synCfv (synC2nd) (.cv u))) dv_cache_0111 dv_cache_0119
        dv_cache_0112 dv_cache_0120 dv_cache_0113 dv_cache_0121 dv_cache_0122
    have p1438 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa syntaxFormula0314 syntaxFormula0321)
        (synWfo (synChnqmap1 (synCfv (synC2nd) (.cv u)))
          (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
          (synChnord (synCfv (synC2nd) (.cv u))))
        p1436 p1437
    have p1439 :=
      @gDffo2 (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u)))
        (synChnqmap1 (synCfv (synC2nd) (.cv u)))
    have p1440 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfo (synChnqmap1 (synCfv (synC2nd) (.cv u)))
          (synCpw1 (synChwcn (synCfv (synC2nd) (.cv u))))
          (synChnord (synCfv (synC2nd) (.cv u))))
        (synWa syntaxFormula0314
          (.classEq (synCrn (synChnqmap1 (synCfv (synC2nd) (.cv u))))
            (synChnord (synCfv (synC2nd) (.cv u)))))
        p1438 p1439
    have p1441 :=
      @gSimprd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0314
        (.classEq (synCrn (synChnqmap1 (synCfv (synC2nd) (.cv u))))
          (synChnord (synCfv (synC2nd) (.cv u))))
        p1440
    have p1442 :=
      @gEqeq2d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synCrn (synChnqmap1 (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u))) syntaxClass0184 p1441
    have p1443 :=
      @gMpbidi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0302
        (.classEq syntaxClass0184 (synChnord (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv u) (synChwcn P)) p1370 p1442
    have p1444 :=
      @gEqeq2 syntaxClass0184 (synChnord (synCfv (synC2nd) (.cv u)))
        (synCdm (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)))
    have p1445 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq syntaxClass0184 (synChnord (synCfv (synC2nd) (.cv u))))
        syntaxFormula0322 p1443 p1444
    have p1446 := @gBi1 syntaxFormula0301 syntaxFormula0186
    have p1447 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0322
        (.imp syntaxFormula0301 syntaxFormula0186) p1445 p1446
    have p1448 :=
      @gMpdi (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0301
        syntaxFormula0186 p1354 p1447
    have p1449 :=
      @gJcad (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfun (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)))
        syntaxFormula0186 p1351 p1448
    have p1451 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa (synWfun (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y)))
          syntaxFormula0186)
        syntaxFormula0187 p1449 p0815
    have p1457 :=
      @gEleq1d (.classEq (.cv a) (.cv u))
        (synCec (.cv a) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u))))
        (synChnord (synCfv (synC2nd) (.cv u))) p0977
    have p1458 :=
      @gImbi12d (.classEq (.cv a) (.cv u))
        (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0305
        syntaxFormula0188 p0974 p1457
    have p1459 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp (.classMem (.cv a) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0305)
        (.classEq (.cv a) (.cv u)) syntaxFormula0323 p1380 p1458
    have p1460 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0324 a
        dv_cache_0024 p1459
    have p1461 := @gNfv syntaxFormula0323 a dv_cache_0123
    have p1462 := @gN1923 (.classEq (.cv a) (.cv u)) syntaxFormula0323 a p1461
    have p1463 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all a syntaxFormula0324)
        (.imp (synWex a (.classEq (.cv a) (.cv u))) syntaxFormula0323) p1460 p1462
    have p1464 :=
      @gSyl5bi (.classMem (.cv u) (synCvv)) (synWex a (.classEq (.cv a) (.cv u)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0323 p0827 p1463
    have p1466 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (.cv u) (synCvv)) syntaxFormula0323))
        (.imp (.classMem (.cv u) (synCvv)) (.classMem (.cv u) (synCvv))) p1464 p0986
    have p1467 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv u) (synCvv))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u)))) syntaxFormula0188
        p1466
    have p1468 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv u) (synCvv)) syntaxFormula0188 p0825 p1467
    have p1469 :=
      @gSyl5com (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0188 p0011 p1468
    have p1470 :=
      @gJcad (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0187
        syntaxFormula0188 p1451 p1469
    have p1472 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0189
        syntaxFormula0192 p1470 p0820
    have p1473 := @gBicom syntaxFormula0191 syntaxFormula0092
    have p1474 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0192
        syntaxFormula0325 p1472 p1473
    have p1475 := @gBi1 syntaxFormula0092 syntaxFormula0191
    have p1476 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0325
        syntaxFormula0326 p1474 p1475
    have p1477 := @gId syntaxFormula0092
    have p1478 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0326))
        (.imp syntaxFormula0092 syntaxFormula0092) p1476 p1477
    have p1479 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0092
        syntaxFormula0191 p1023 p1478
    have p1480 := @gSsv (synCrn (.cv k))
    have p1481 := @gHwcnssbase (synCvv) (synCrn (.cv k)) p1480
    have p1482 :=
      @gSsel (synChwcn (synCrn (.cv k))) (synChwcn (synCvv))
        (synCfv (synChncodetrnfn (.cv k)) (.cv u))
    have p1483 := Nominal.mp p1481 p1482
    have p1484 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0060
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCvv)))
        p0286 p1483
    have p1485 := @gSsv (synCfv (synC2nd) (.cv u))
    have p1486 := @gHwcnssbase (synCvv) (synCfv (synC2nd) (.cv u)) p1485
    have p1487 :=
      @gSsel (synChwcn (synCfv (synC2nd) (.cv u))) (synChwcn (synCvv)) (.cv u)
    have p1488 := Nominal.mp p1486 p1487
    have p1489 :=
      @gSyl (.classMem (.cv u) (synChwcn P))
        (.classMem (.cv u) (synChwcn (synCfv (synC2nd) (.cv u))))
        (.classMem (.cv u) (synChwcn (synCvv))) p0011 p1488
    have p1490 :=
      @gJctild (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCvv)))
        (.classMem (.cv u) (synChwcn (synCvv))) p1484 p1489
    have p1493 := @gHwbijf1oclndv (synCres (.cv k) (synCfv (synC2nd) (.cv u))) p0084
    have p1494 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0009
        (.classMem (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (synChwbij)) p0050
        p1493
    have p1496 :=
      @gA1i (.classMem (synCfv (synC1st) (.cv u)) (synCvv))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0022
    have p1500 :=
      @gHwgenvalclndv (synCres (.cv k) (synCfv (synC2nd) (.cv u)))
        (synCfv (synC1st) (.cv u)) p0084 p0022
    have p1501 :=
      @gA1i syntaxFormula0331 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p1500
    have p1502 :=
      @gOpeq2 (synCdm (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCfv (synC2nd) (.cv u)) (synCfv (synC1st) (.cv u))
    have p1503 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0005
        syntaxFormula0332 p0036 p1502
    have p1504 :=
      @gEqcomd (.classMem (.cv u) (synChwcn P)) (.cv u)
        (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) p0013
    have p1505 :=
      @gA1d (.classMem (.cv u) (synChwcn P))
        (.classEq (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (.cv u))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p1504
    have p1506 :=
      @gEqeq2 (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (.cv u)
        syntaxClass0329
    have p1507 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (synCop (synCfv (synC1st) (.cv u)) (synCfv (synC2nd) (.cv u))) (.cv u))
        syntaxFormula0334 p1505 p1506
    have p1508 := @gBi1 syntaxFormula0332 syntaxFormula0333
    have p1509 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0334
        (.imp syntaxFormula0332 syntaxFormula0333) p1507 p1508
    have p1510 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0332
        syntaxFormula0333 p1503 p1509
    have p1511 := @gOpeq1 syntaxClass0329 (.cv u) syntaxClass0042
    have p1512 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0333
        syntaxFormula0336 p1510 p1511
    have p1515 :=
      @gEqcomi (synCfv (synChncodetrnfn (.cv k)) (.cv u)) syntaxClass0042 p0282
    have p1516 :=
      @gOpeq2i syntaxClass0042 (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (.cv u) p1515
    have p1517 :=
      @gA1i
        (.classEq syntaxClass0335
          (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p1516
    have p1518 :=
      @gEqeq2d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxClass0335
        (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) syntaxClass0330
        p1517
    have p1519 :=
      @gMpbidi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0336
        syntaxFormula0337 (.classMem (.cv u) (synChwcn P)) p1512 p1518
    have p1520 :=
      @gEqeq2 syntaxClass0330
        (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) syntaxClass0328
    have p1521 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0337
        syntaxFormula0339 p1519 p1520
    have p1522 := @gBi1 syntaxFormula0331 syntaxFormula0338
    have p1523 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0339
        (.imp syntaxFormula0331 syntaxFormula0338) p1521 p1522
    have p1524 :=
      @gMpdi (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0331
        syntaxFormula0338 p1501 p1523
    have p1525 :=
      @g_pm3_2 (.classMem (synCfv (synC1st) (.cv u)) (synCvv)) syntaxFormula0338
    have p1526 :=
      @gSyl9 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0338
        (.classMem (synCfv (synC1st) (.cv u)) (synCvv)) syntaxFormula0340 p1524 p1525
    have p1527 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synC1st) (.cv u)) (synCvv))
        (.classMem (.cv u) (synChwcn P))
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0340) p1496
        p1526
    have p1528 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0340 p1527
    have p1530 :=
      @gOpeq2d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) (.cv r)
        (synCfv (synC1st) (.cv u)) (synCres (.cv k) (synCfv (synC2nd) (.cv u))) p0069
    have p1531 :=
      @gFveq2d (.classEq (.cv r) (synCfv (synC1st) (.cv u)))
        (synCop (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (.cv r)) syntaxClass0327
        (synChwgen) p1530
    have p1532 :=
      @gEqeq1d (.classEq (.cv r) (synCfv (synC1st) (.cv u))) syntaxClass0341
        syntaxClass0328 (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        p1531
    have p1533 :=
      @gRspcev syntaxFormula0342 syntaxFormula0338 r (synCfv (synC1st) (.cv u))
        (synCvv) dv_cache_0014 dv_cache_0124 dv_cache_0125 p1532
    have p1534 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0340
        syntaxFormula0343 p1528 p1533
    have p1535 :=
      @gJcad (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (synChwbij))
        syntaxFormula0343 p1494 p1534
    have p1536 := @gId (.classEq (.cv f) (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
    have p1537 :=
      @gOpeq1d (.classEq (.cv f) (synCres (.cv k) (synCfv (synC2nd) (.cv u)))) (.cv f)
        (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (.cv r) p1536
    have p1538 :=
      @gFveq2d (.classEq (.cv f) (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCop (.cv f) (.cv r))
        (synCop (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (.cv r)) (synChwgen)
        p1537
    have p1539 :=
      @gEqeq1d (.classEq (.cv f) (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        (synCfv (synChwgen) (synCop (.cv f) (.cv r))) syntaxClass0341
        (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) p1538
    have p1540 :=
      @gRexbidv (.classEq (.cv f) (synCres (.cv k) (synCfv (synC2nd) (.cv u))))
        syntaxFormula0344 syntaxFormula0342 r (synCvv) dv_cache_0126 p1539
    have p1541 :=
      @gRspcev syntaxFormula0345 syntaxFormula0343 f
        (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (synChwbij) dv_cache_0127
        dv_cache_0128 dv_cache_0129 p1540
    have p1542 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa (.classMem (synCres (.cv k) (synCfv (synC2nd) (.cv u))) (synChwbij))
          syntaxFormula0343)
        syntaxFormula0346 p1535 p1541
    have p1543 :=
      @gJcad (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0347
        syntaxFormula0346 p1490 p1542
    have p1544 :=
      @gElex (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCvv))
    have p1545 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCvv)))
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv)) p1484 p1544
    have p1546 := @gId (.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
    have p1547 :=
      @gBreq2d (.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) (.cv v)
        (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (.cv u) (synChwniso (synCvv)) p1546
    have p1548 := @gBiid (.classMem (.cv u) (synChwcn (synCvv)))
    have p1549 :=
      @gA1i
        (synWb (.classMem (.cv u) (synChwcn (synCvv)))
          (.classMem (.cv u) (synChwcn (synCvv))))
        (.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) p1548
    have p1551 :=
      @gEleq1d (.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) (.cv v)
        (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCvv)) p1546
    have p1552 :=
      @gAnbi12d (.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (.classMem (.cv u) (synChwcn (synCvv)))
        (.classMem (.cv u) (synChwcn (synCvv)))
        (.classMem (.cv v) (synChwcn (synCvv)))
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCvv)))
        p1549 p1551
    have p1554 :=
      @gOpeq2d (.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) (.cv v)
        (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (.cv u) p1546
    have p1555 :=
      @gEqeq2d (.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synCop (.cv u) (.cv v))
        (synCop (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synCfv (synChwgen) (synCop (.cv f) (.cv r))) p1554
    have p1556 :=
      @gN2rexbidv (.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        syntaxFormula0348 syntaxFormula0344 f r (synChwbij) (synCvv) dv_cache_0130
        dv_cache_0131 p1555
    have p1557 :=
      @gAnbi12d (.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synWa (.classMem (.cv u) (synChwcn (synCvv)))
          (.classMem (.cv v) (synChwcn (synCvv))))
        syntaxFormula0347 syntaxFormula0350 syntaxFormula0346 p1552 p1556
    have p1558 :=
      @gBibi12d (.classEq (.cv v) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synWbr (.cv u) (synChwniso (synCvv)) (.cv v)) syntaxFormula0351
        syntaxFormula0352 syntaxFormula0353 p1547 p1557
    have p1559 :=
      @gElhwnisogen v u (synCvv) f r dv_cache_0132 dv_cache_0124 dv_cache_0002
        dv_cache_0133 dv_cache_0134 dv_cache_0135 dv_cache_0136
    have p1560 :=
      @gVtoclg
        (synWb (synWbr (.cv u) (synChwniso (synCvv)) (.cv v)) syntaxFormula0352)
        syntaxFormula0354 v (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv)
        dv_cache_0137 dv_cache_0138 p1558 p1559
    have p1561 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
        syntaxFormula0354 p1545 p1560
    have p1562 := @gBicom syntaxFormula0351 syntaxFormula0353
    have p1563 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0354
        syntaxFormula0355 p1561 p1562
    have p1564 := @gBi1 syntaxFormula0353 syntaxFormula0351
    have p1565 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0355
        syntaxFormula0356 p1563 p1564
    have p1566 := @gId syntaxFormula0353
    have p1567 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0356))
        (.imp syntaxFormula0353 syntaxFormula0353) p1565 p1566
    have p1568 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0353
        syntaxFormula0351 p1543 p1567
    have p1590 :=
      @gSyl6ss (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (synCrn (.cv k)) Y
        (synCun P Y) p0310 p0000
    have p1591 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWss (synCrn (.cv k)) (synCun P Y))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) p1590
    have p1592 := @gSstr (synCfv (synC2nd) (.cv a)) (synCrn (.cv k)) (synCun P Y)
    have p1593 :=
      @gEx (synWss (synCfv (synC2nd) (.cv a)) (synCrn (.cv k)))
        (synWss (synCrn (.cv k)) (synCun P Y))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y)) p1592
    have p1594 :=
      @gSyl9 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWss (synCrn (.cv k)) (synCun P Y))
        (synWss (synCfv (synC2nd) (.cv a)) (synCrn (.cv k)))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y)) p1591 p1593
    have p1595 :=
      @gSyl5 (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWss (synCfv (synC2nd) (.cv a)) (synCrn (.cv k)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
          (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y)))
        p0306 p1594
    have p1596 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y)) p1595
    have p1598 :=
      @gSyl9 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWss (synCfv (synC2nd) (.cv a)) (synCun P Y))
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        syntaxFormula0109 p1596 p0534
    have p1599 :=
      @gSyl5 (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWbr (synCfv (synC1st) (.cv a)) (synCwe) (synCfv (synC2nd) (.cv a)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0109) p0296
        p1598
    have p1600 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0109 p1599
    have p1605 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0109
        syntaxFormula0110 p1600 p0541
    have p1607 :=
      @gEleq1d (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) (.cv a)
        (synCop (synCfv (synC1st) (.cv a)) (synCfv (synC2nd) (.cv a)))
        (synChwcodes (synCun P Y)) p0288
    have p1608 :=
      @gBiimprd (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv a) (synChwcodes (synCun P Y))) syntaxFormula0110 p1607
    have p1609 :=
      @gSylcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0110
        (.classMem (.cv a) (synChwcodes (synCun P Y))) p1605 p1608
    have p1612 :=
      @gSyl5 (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0065
        (.classMem (.cv a) (synChwcodes (synCun P Y))) syntaxFormula0111 p0330 p0548
    have p1613 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv a) (synChwcodes (synCun P Y)))
        (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0111) p1609
        p1612
    have p1614 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0111 p1613
    have p1617 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0111
        (.classMem (.cv a) (synChwcn (synCun P Y))) p1614 p0553
    have p1618 :=
      @gSsrdv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) a
        (synChwcn (synCrn (.cv k))) (synChwcn (synCun P Y)) dv_cache_0022
        dv_cache_0047 dv_cache_0024 p1617
    have p1619 :=
      @gSsel (synChwcn (synCrn (.cv k))) (synChwcn (synCun P Y))
        (synCfv (synChncodetrnfn (.cv k)) (.cv u))
    have p1620 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWss (synChwcn (synCrn (.cv k))) (synChwcn (synCun P Y)))
        (.imp syntaxFormula0060 syntaxFormula0357) p1618 p1619
    have p1621 :=
      @gSylcom (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0060
        syntaxFormula0357 p0286 p1620
    have p1622 :=
      @gJctild (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0357
        (.classMem (.cv u) (synChwcn (synCun P Y))) p1621 p0364
    have p1623 := @gSsv (synCun P Y)
    have p1624 :=
      @gHwnisobasebicl (synCvv) (.cv u) (synCfv (synChncodetrnfn (.cv k)) (.cv u))
        (synCun P Y) p1623
    have p1625 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa (.classMem (.cv u) (synChwcn (synCun P Y))) syntaxFormula0357)
        syntaxFormula0359 p1622 p1624
    have p1626 := @gBi1 syntaxFormula0351 syntaxFormula0358
    have p1627 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0359
        (.imp syntaxFormula0351 syntaxFormula0358) p1625 p1626
    have p1628 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0351
        syntaxFormula0358 p1568 p1627
    have p1629 :=
      @gHwnisoclasseqbcl (synCun P Y) (.cv u)
        (synCfv (synChncodetrnfn (.cv k)) (.cv u)) p0001
    have p1630 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa (.classMem (.cv u) (synChwcn (synCun P Y))) syntaxFormula0357)
        syntaxFormula0362 p1622 p1629
    have p1631 := @gBicom syntaxFormula0361 syntaxFormula0358
    have p1632 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0362
        syntaxFormula0363 p1630 p1631
    have p1633 := @gBi1 syntaxFormula0358 syntaxFormula0361
    have p1634 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0363
        syntaxFormula0364 p1632 p1633
    have p1635 := @gId syntaxFormula0358
    have p1636 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0364))
        (.imp syntaxFormula0358 syntaxFormula0358) p1634 p1635
    have p1637 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0358
        syntaxFormula0361 p1628 p1636
    have p1638 :=
      @gEqeq2 (synCec (.cv u) (synChwniso (synCun P Y))) syntaxClass0360
        syntaxClass0190
    have p1639 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0361
        syntaxFormula0366 p1637 p1638
    have p1640 := @gBi1 syntaxFormula0191 syntaxFormula0365
    have p1641 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0366
        (.imp syntaxFormula0191 syntaxFormula0365) p1639 p1640
    have p1642 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0191
        syntaxFormula0365 p1479 p1641
    have p1643 :=
      @gElex (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCrn (.cv k)))
    have p1644 := @gNfcv a (synCfv (synChncodetrnfn (.cv k)) (.cv u)) dv_cache_0139
    have p1645 := @gIssetf a (synCfv (synChncodetrnfn (.cv k)) (.cv u)) p1644
    have p1646 := (Nominal.classEqRefl (synChnqmap1 (synCrn (.cv k))))
    have p1647 :=
      @gFveq1i (synCsn (.cv a)) (synChnqmap1 (synCrn (.cv k))) syntaxClass0367 p1646
    have p1648 := @gSnelpw1 (.cv a) (synChwcn (synCrn (.cv k)))
    have p1649 :=
      @gBiimpri (.classMem (synCsn (.cv a)) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) p1648
    have p1650 :=
      @gFvres (synCsn (.cv a)) (synCpw1 (synChwcn (synCrn (.cv k))))
        (synCimage (synChwniso (synCrn (.cv k))))
    have p1651 :=
      @gSyl (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (synCsn (.cv a)) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classEq (synCfv syntaxClass0367 (synCsn (.cv a)))
          (synCfv (synCimage (synChwniso (synCrn (.cv k)))) (synCsn (.cv a))))
        p1649 p1650
    have p1652 :=
      @gSyl5eq (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synCfv syntaxClass0367 (synCsn (.cv a)))
        (synCfv (synCimage (synChwniso (synCrn (.cv k)))) (synCsn (.cv a))) p1647
        p1651
    have p1653 := @gEqid (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))
    have p1654 :=
      @gDfcleq x (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))) dv_cache_0140
        dv_cache_0140
    have p1655 := @gElima1c x syntaxClass0368 syntaxClass0370 dv_cache_0141 dv_cache_0142
    have p1656 := @gElsymdif syntaxClass0371 (synCins2 (synCsset)) syntaxClass0369
    have p1658 :=
      @gOtelins2 (synCsn (.cv x)) (synCsn (.cv a))
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))) (synCsset) p0839
    have p1659 := (Nominal.biimpRefl syntaxFormula0372)
    have p1661 := @gRnex (.cv k) p0082
    have p1662 :=
      @gSyl6eqel (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (synCrn (.cv k))
        (synCrn (.cv k)) (synCvv) p0140 p1661
    exact
      continuation p1618 p1621 p1642 p1643 p1645 p1646 p1649 p1652 p1653 p1654 p1655 p1656
        p1658 p1659 p1662

end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `ReplaySupport.CodeCover6`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_cfbhnqinjcodecoverddndv_stage6`. -/
@[expose]
noncomputable def gCfbhnqinjcodecoverddndvStage6 (u : Var) (P : Class) (k : Var)
    (Y : Class) (p0001 : _) (p0286 : _) (p0370 : _) (p0442 : _) (p0558 : _) (p0560 : _)
    (p0562 : _) (p0839 : _) (p0842 : _) (p0853 : _) (p0859 : _) (p0860 : _) (p0871 : _)
    (p0880 : _) (p0888 : _) (p0902 : _) (p0903 : _) (p0906 : _) (p0907 : _) (p0939 : _)
    (p0957 : _) (p1123 : _) (p1618 : _) (p1621 : _) (p1643 : _) (p1645 : _) (p1646 : _)
    (p1652 : _) (p1653 : _) (p1654 : _) (p1655 : _) (p1656 : _) (p1658 : _) (p1659 : _)
    (p1662 : _) {Result : Type}
    (continuation : _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ →
        _ → _ → _ → _ → _ → _ → _ → _ → _ → Result) :=
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
    have fresh_a_ne_k : a ≠ k := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_a_not_Y : a ∉ Y.fv := by
      intro h
      exact fresh_a (Finset.mem_union_right _ (h))
    have fresh_p : p ∉ proofSupport :=
      by
      change freshVar proofSupport 6 ∉ proofSupport
      exact freshVar_not_mem proofSupport 6
    have fresh_p_not_P : p ∉ P.fv := by
      intro h
      exact
        fresh_p
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_p_ne_k : p ≠ k := by
      intro h
      exact
        fresh_p
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_p_not_Y : p ∉ Y.fv := by
      intro h
      exact fresh_p (Finset.mem_union_right _ (h))
    have fresh_q : q ∉ proofSupport :=
      by
      change freshVar proofSupport 7 ∉ proofSupport
      exact freshVar_not_mem proofSupport 7
    have fresh_q_not_P : q ∉ P.fv := by
      intro h
      exact
        fresh_q
          (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
    have fresh_q_ne_k : q ≠ k := by
      intro h
      exact
        fresh_q
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_q_not_Y : q ∉ Y.fv := by
      intro h
      exact fresh_q (Finset.mem_union_right _ (h))
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
    have fresh_t_ne_k : t ≠ k := by
      intro h
      exact
        fresh_t
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_y_ne_x : y ≠ x :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 2
      exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
    have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
    have fresh_y_ne_a : y ≠ a :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
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
    have fresh_p_ne_q : p ≠ q :=
      by
      change freshVar proofSupport 6 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
    have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
    have dv_cache_0007 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
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
    have dv_cache_0059 : y ∉ ((synCvv)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            compact_fv_not_mem_empty, not_false_eq_true])
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
    have dv_cache_0091 : x ∉ ((synCvv)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0143 :
      b ∉
        ((synWb (.classMem (synCop (synCsn (.cv x)) (synCop (synCsn (.cv a))
                  (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))) (synCins3
                (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCrn (.cv k))))))))
            (.classMem (synCop (synCsn (.cv x)) (synCsn (.cv a))) (synCcom (synCsset)
                (synCcnv (synCsi (synChwniso (synCrn (.cv k))))))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a, fresh_b_ne_k,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0144 : y ∉ ((synChwniso (synCrn (.cv k)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_k,
            not_false_eq_true])
    have dv_cache_0145 :
      t ∉
        ((synWa (.classMem (.cv y) (synCsn (.cv a)))
            (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x)))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
            Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_a, fresh_t_ne_x, fresh_t_ne_k,
            or_false, not_false_eq_true])
    have dv_cache_0146 : t ∉ ((synCcnv (synCsi (synChwniso (synCrn (.cv k)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_k,
            not_false_eq_true])
    have dv_cache_0147 : y ∉ ((synCima (synChwniso (synCrn (.cv k))) (.cv x))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_k, fresh_y_ne_x, or_false,
            not_false_eq_true])
    have dv_cache_0148 : x ∉ ((synCimage (synChwniso (synCrn (.cv k))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_k,
            not_false_eq_true])
    have dv_cache_0149 : y ∉ ((synCimage (synChwniso (synCrn (.cv k))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimage,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_k,
            not_false_eq_true])
    have dv_cache_0150 :
      a ∉
        ((Wff.imp (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u))
              (synChwcn (synCrn (.cv k)))) (.classEq (synCfv (synChnqmap1 (synCrn (.cv k)))
                (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
              (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u))
                (synChwniso (synCrn (.cv k))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_u, fresh_a_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0151 :
      x ∉ ((synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0152 :
      x ∉
        ((synWa (synWbr (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u))
                (synChwniso (synCrn (.cv k)))) (synCcnv (synChnqmap1 (synCrn (.cv k))))
              (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
            (synWbr (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
              (synChnqmap1 (synCun P Y)) (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u))
                (synChwniso (synCun P Y)))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_ne_k, fresh_x_not_P,
            fresh_x_not_Y, or_false, not_false_eq_true])
    have dv_cache_0153 :
      x ∉
        ((synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u))
            (synChwniso (synCrn (.cv k))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0154 :
      x ∉
        ((synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u))
            (synChwniso (synCun P Y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chncodetrnfn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_ne_k, fresh_x_not_P,
            fresh_x_not_Y, or_false, not_false_eq_true])
    have dv_cache_0155 : x ∉ ((synCcnv (synChnqmap1 (synCrn (.cv k))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_k,
            not_false_eq_true])
    have dv_cache_0156 : p ∉ ((synCcnv (synChnqmap1 (synCrn (.cv k))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_p_ne_k,
            not_false_eq_true])
    have dv_cache_0157 :
      p ∉
        ((synWa (synWbr (.cv x) (synCcom (synChnqmap1 (synCun P Y))
                (synCcnv (synChnqmap1 (synCrn (.cv k))))) (.cv y)) (synWbr (.cv x)
              (synCcom (synChnqmap1 (synCun P Y))
                (synCcnv (synChnqmap1 (synCrn (.cv k))))) (.cv z)))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
            Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, fresh_p_not_P,
            fresh_p_not_Y, fresh_p_ne_k, fresh_p_ne_z, or_false, not_false_eq_true])
    have dv_cache_0158 : q ∉ ((synCcnv (synChnqmap1 (synCrn (.cv k))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_k,
            not_false_eq_true])
    have dv_cache_0159 :
      q ∉
        ((synWa (synWa (synWbr (.cv x) (synCcom (synChnqmap1 (synCun P Y))
                  (synCcnv (synChnqmap1 (synCrn (.cv k))))) (.cv y)) (synWbr (.cv x)
                (synCcom (synChnqmap1 (synCun P Y))
                  (synCcnv (synChnqmap1 (synCrn (.cv k))))) (.cv z)))
            (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv p))
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_x, fresh_q_ne_y, fresh_q_not_P,
            fresh_q_not_Y, fresh_q_ne_k, fresh_q_ne_z, fresh_q_ne_p, or_false,
            not_false_eq_true])
    let syntaxFormula0060 : Wff :=
      (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCrn (.cv k))))
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
    let syntaxFormula0357 : Wff :=
      (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCun P Y)))
    let syntaxClass0360 : Class :=
      (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso (synCun P Y)))
    let syntaxClass0367 : Class :=
      (synCres (synCimage (synChwniso (synCrn (.cv k))))
        (synCpw1 (synChwcn (synCrn (.cv k)))))
    let syntaxClass0368 : Class :=
      (synCop (synCsn (.cv a)) (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
    let syntaxClass0369 : Class :=
      (synCins3 (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCrn (.cv k)))))))
    let syntaxClass0370 : Class := (synCsymdif (synCins2 (synCsset)) syntaxClass0369)
    let syntaxClass0371 : Class := (synCop (synCsn (.cv x)) syntaxClass0368)
    let syntaxFormula0372 : Wff :=
      (synWbr (synCsn (.cv x)) (synCsset)
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
    let syntaxFormula0373 : Wff :=
      (.classMem (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))) (synCvv))
    let syntaxFormula0374 : Wff :=
      (.classMem (.cv x) (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
    let syntaxFormula0375 : Wff := (.classMem syntaxClass0371 (synCins2 (synCsset)))
    let syntaxFormula0376 : Wff :=
      (.classMem (synCop (.cv b) (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
        (synCvv))
    let syntaxFormula0377 : Wff :=
      (.classMem (synCop (.cv b) (synCsn (.cv a)))
        (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCrn (.cv k)))))))
    let syntaxClass0378 : Class := (synCop (.cv b) syntaxClass0368)
    let syntaxFormula0379 : Wff := (.classMem syntaxClass0378 syntaxClass0369)
    let syntaxFormula0380 : Wff := (synWa syntaxFormula0377 syntaxFormula0376)
    let syntaxFormula0381 : Wff := (.classMem syntaxClass0371 syntaxClass0369)
    let syntaxFormula0382 : Wff :=
      (.classMem (synCop (synCsn (.cv x)) (synCsn (.cv a)))
        (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCrn (.cv k)))))))
    let syntaxFormula0383 : Wff := (synWb syntaxFormula0381 syntaxFormula0382)
    let syntaxFormula0384 : Wff :=
      (.imp (.classEq (.cv b) (synCsn (.cv x))) syntaxFormula0383)
    let syntaxFormula0385 : Wff := (.classMem syntaxClass0368 (synCvv))
    let syntaxFormula0386 : Wff :=
      (synWbr (synCsn (.cv x)) (synCcnv (synCsi (synChwniso (synCrn (.cv k))))) (.cv t))
    let syntaxFormula0387 : Wff :=
      (synWa (.classEq (.cv t) (synCsn (.cv y)))
        (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x)))
    let syntaxFormula0388 : Wff := (synWex y syntaxFormula0387)
    let syntaxFormula0389 : Wff :=
      (synWa syntaxFormula0386 (synWbr (.cv t) (synCsset) (synCsn (.cv a))))
    let syntaxFormula0390 : Wff :=
      (synWa syntaxFormula0387 (synWbr (.cv t) (synCsset) (synCsn (.cv a))))
    let syntaxFormula0391 : Wff := (synWex y syntaxFormula0390)
    let syntaxFormula0392 : Wff :=
      (synWa (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x))
        (synWbr (.cv t) (synCsset) (synCsn (.cv a))))
    let syntaxFormula0393 : Wff :=
      (synWa (.classMem (.cv y) (synCsn (.cv a)))
        (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x)))
    let syntaxFormula0394 : Wff := (synWex t syntaxFormula0390)
    let syntaxFormula0395 : Wff := (synWb syntaxFormula0375 syntaxFormula0381)
    let syntaxFormula0396 : Wff := (synWb syntaxFormula0374 syntaxFormula0374)
    let syntaxFormula0397 : Wff := (.classMem syntaxClass0371 syntaxClass0370)
    let syntaxFormula0398 : Wff := (.neg syntaxFormula0396)
    let syntaxFormula0399 : Wff := (synWex x syntaxFormula0397)
    let syntaxFormula0400 : Wff := (.all x syntaxFormula0396)
    let syntaxFormula0401 : Wff := (.neg syntaxFormula0400)
    let syntaxClass0402 : Class := (synCima syntaxClass0370 (synC1c))
    let syntaxFormula0403 : Wff := (.classMem syntaxClass0368 syntaxClass0402)
    let syntaxClass0404 : Class := (synCcompl syntaxClass0402)
    let syntaxFormula0405 : Wff :=
      (synWbr (synCsn (.cv a)) syntaxClass0404
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
    let syntaxFormula0406 : Wff := (.classMem syntaxClass0368 syntaxClass0404)
    let syntaxFormula0407 : Wff := (.neg syntaxFormula0403)
    let syntaxFormula0408 : Wff :=
      (synWbr (synCsn (.cv a)) (synCimage (synChwniso (synCrn (.cv k))))
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
    let syntaxFormula0409 : Wff :=
      (synWa (synWfn (synCimage (synChwniso (synCrn (.cv k)))) (synCvv))
        (.classMem (synCsn (.cv a)) (synCvv)))
    let syntaxFormula0410 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synCfv (synCimage (synChwniso (synCrn (.cv k)))) (synCsn (.cv a))))
    let syntaxFormula0411 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
    let syntaxFormula0412 : Wff := (synWb syntaxFormula0410 syntaxFormula0411)
    let syntaxClass0413 : Class :=
      (synCfv (synChnqmap1 (synCrn (.cv k)))
        (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
    let syntaxClass0414 : Class :=
      (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso (synCrn (.cv k))))
    let syntaxFormula0415 : Wff := (.classEq syntaxClass0413 syntaxClass0414)
    let syntaxFormula0416 : Wff :=
      (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0411)
    let syntaxFormula0417 : Wff := (.imp syntaxFormula0060 syntaxFormula0415)
    let syntaxFormula0418 : Wff :=
      (.imp (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) syntaxFormula0417)
    let syntaxFormula0419 : Wff :=
      (synWfn (synChnqmap1 (synCrn (.cv k))) (synCpw1 (synChwcn (synCrn (.cv k)))))
    let syntaxFormula0420 : Wff :=
      (.classMem (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synCpw1 (synChwcn (synCrn (.cv k)))))
    let syntaxFormula0421 : Wff := (synWa syntaxFormula0419 syntaxFormula0420)
    let syntaxFormula0422 : Wff :=
      (synWbr (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synChnqmap1 (synCrn (.cv k))) syntaxClass0414)
    let syntaxFormula0423 : Wff := (synWb syntaxFormula0415 syntaxFormula0422)
    let syntaxFormula0424 : Wff :=
      (synWbr syntaxClass0414 (synCcnv (synChnqmap1 (synCrn (.cv k))))
        (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
    let syntaxClass0425 : Class :=
      (synCfv (synChnqmap1 (synCun P Y))
        (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
    let syntaxFormula0426 : Wff := (.classEq syntaxClass0425 syntaxClass0360)
    let syntaxFormula0427 : Wff :=
      (.classMem (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synCpw1 (synChwcn (synCun P Y))))
    let syntaxFormula0428 : Wff :=
      (synWa (synWfn (synChnqmap1 (synCun P Y)) (synCpw1 (synChwcn (synCun P Y))))
        syntaxFormula0427)
    let syntaxFormula0429 : Wff :=
      (synWbr (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synChnqmap1 (synCun P Y)) syntaxClass0360)
    let syntaxFormula0430 : Wff := (synWb syntaxFormula0426 syntaxFormula0429)
    let syntaxFormula0431 : Wff :=
      (synWbr syntaxClass0414 (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv x))
    let syntaxFormula0432 : Wff :=
      (synWbr (.cv x) (synChnqmap1 (synCun P Y)) syntaxClass0360)
    let syntaxFormula0433 : Wff := (synWa syntaxFormula0431 syntaxFormula0432)
    let syntaxFormula0434 : Wff := (synWa syntaxFormula0424 syntaxFormula0429)
    let syntaxFormula0435 : Wff := (synWex x syntaxFormula0433)
    let syntaxClass0436 : Class :=
      (synCcom (synChnqmap1 (synCun P Y)) (synCcnv (synChnqmap1 (synCrn (.cv k)))))
    let syntaxFormula0437 : Wff :=
      (synWbr syntaxClass0414 syntaxClass0436 syntaxClass0360)
    let syntaxFormula0438 : Wff :=
      (synWbr syntaxClass0414 (synChnqinc (synCrn (.cv k)) (synCun P Y)) syntaxClass0360)
    let syntaxFormula0439 : Wff := (synWbr (.cv x) syntaxClass0436 (.cv y))
    let syntaxFormula0440 : Wff := (synWbr (.cv x) syntaxClass0436 (.cv z))
    let syntaxFormula0441 : Wff := (synWa syntaxFormula0439 syntaxFormula0440)
    let syntaxFormula0442 : Wff :=
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv p))
        (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y)))
    let syntaxFormula0443 : Wff := (synWex p syntaxFormula0442)
    let syntaxFormula0444 : Wff :=
      (synWa (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv q))
        (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z)))
    let syntaxFormula0445 : Wff := (synWex q syntaxFormula0444)
    let syntaxFormula0446 : Wff := (synWa syntaxFormula0441 syntaxFormula0442)
    let syntaxFormula0447 : Wff := (synWa syntaxFormula0446 syntaxFormula0444)
    let syntaxFormula0448 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q)))
    let syntaxFormula0449 : Wff :=
      (synWb (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p)) (.cv x))
        syntaxFormula0448)
    let syntaxFormula0450 : Wff :=
      (.classEq (synCdm (synChnqmap1 (synCrn (.cv k))))
        (synCpw1 (synChwcn (synCrn (.cv k)))))
    let syntaxFormula0451 : Wff :=
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k))))))
    have p1663 := @gHwnisoexg (synCrn (.cv k))
    have p1664 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCrn (.cv k)) (synCvv))
        (.classMem (synChwniso (synCrn (.cv k))) (synCvv)) p1662 p1663
    have p1665 :=
      @gImaexg (synChwniso (synCrn (.cv k))) (synCsn (.cv a)) (synCvv) (synCvv)
    have p1666 :=
      @gSylancl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synChwniso (synCrn (.cv k))) (synCvv))
        (.classMem (synCsn (.cv a)) (synCvv)) syntaxFormula0373 p1664 p0839 p1665
    have p1667 :=
      @gBrssetg (synCsn (.cv x))
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))) (synCvv) (synCvv)
    have p1668 :=
      @gSylancr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCsn (.cv x)) (synCvv)) syntaxFormula0373
        (synWb syntaxFormula0372 (synWss (synCsn (.cv x))
            (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))))
        p0842 p1666 p1667
    have p1670 :=
      @gSnss (.cv x) (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))) p0853
    have p1671 :=
      @gSyl6bbr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0372
        (synWss (synCsn (.cv x)) (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
        syntaxFormula0374 p1668 p1670
    have p1672 :=
      @gSyl5bbr
        (.classMem (synCop (synCsn (.cv x))
            (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))) (synCsset))
        syntaxFormula0372 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        syntaxFormula0374 p1659 p1671
    have p1673 :=
      @gSyl5bb syntaxFormula0375
        (.classMem (synCop (synCsn (.cv x))
            (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))) (synCsset))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0374 p1658 p1672
    have p1677 :=
      @gOpexg (.cv b) (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))
        (synCvv) (synCvv)
    have p1678 :=
      @gSylancr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv b) (synCvv)) syntaxFormula0373 syntaxFormula0376 p0860 p1666
        p1677
    have p1679 :=
      @gBiantrud (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0376
        syntaxFormula0377 p1678
    have p1680 := (Nominal.classEqRefl syntaxClass0369)
    have p1681 :=
      @gEleq2i syntaxClass0369
        (synCtxp (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCrn (.cv k))))))
          (synCvv))
        syntaxClass0378 p1680
    have p1682 :=
      @gOteltxp (.cv b) (synCsn (.cv a))
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))
        (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCrn (.cv k))))))
        (synCvv)
    have p1683 :=
      @gBitri syntaxFormula0379
        (.classMem syntaxClass0378 (synCtxp
            (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCrn (.cv k))))))
            (synCvv)))
        syntaxFormula0380 p1681 p1682
    have p1684 :=
      @gSyl6rbbr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0377
        syntaxFormula0380 syntaxFormula0379 p1679 p1683
    have p1685 := @gOpeq1 (.cv b) (synCsn (.cv x)) syntaxClass0368
    have p1686 :=
      @gEleq1d (.classEq (.cv b) (synCsn (.cv x))) syntaxClass0378 syntaxClass0371
        syntaxClass0369 p1685
    have p1688 :=
      @gEleq1d (.classEq (.cv b) (synCsn (.cv x))) (synCop (.cv b) (synCsn (.cv a)))
        (synCop (synCsn (.cv x)) (synCsn (.cv a)))
        (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCrn (.cv k)))))) p0871
    have p1689 :=
      @gBibi12d (.classEq (.cv b) (synCsn (.cv x))) syntaxFormula0379 syntaxFormula0381
        syntaxFormula0377 syntaxFormula0382 p1686 p1688
    have p1690 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWb syntaxFormula0379 syntaxFormula0377) (.classEq (.cv b) (synCsn (.cv x)))
        syntaxFormula0383 p1684 p1689
    have p1691 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0384 b
        dv_cache_0076 p1690
    have p1692 := @gNfv syntaxFormula0383 b dv_cache_0143
    have p1693 :=
      @gN1923 (.classEq (.cv b) (synCsn (.cv x))) syntaxFormula0383 b p1692
    have p1694 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all b syntaxFormula0384)
        (.imp (synWex b (.classEq (.cv b) (synCsn (.cv x)))) syntaxFormula0383) p1691
        p1693
    have p1695 :=
      @gSyl5bi (.classMem (synCsn (.cv x)) (synCvv))
        (synWex b (.classEq (.cv b) (synCsn (.cv x))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0383 p0859 p1694
    have p1697 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (synCsn (.cv x)) (synCvv)) syntaxFormula0383))
        (.imp (.classMem (synCsn (.cv x)) (synCvv)) (.classMem (synCsn (.cv x)) (synCvv)))
        p1695 p0880
    have p1698 := @gElex syntaxClass0371 syntaxClass0369
    have p1699 := @gOpexb (synCsn (.cv x)) syntaxClass0368
    have p1700 :=
      @gSimplbi (.classMem syntaxClass0371 (synCvv))
        (.classMem (synCsn (.cv x)) (synCvv)) syntaxFormula0385 p1699
    have p1701 :=
      @gSyl syntaxFormula0381 (.classMem syntaxClass0371 (synCvv))
        (.classMem (synCsn (.cv x)) (synCvv)) p1698 p1700
    have p1702 :=
      @gElex (synCop (synCsn (.cv x)) (synCsn (.cv a)))
        (synCcom (synCsset) (synCcnv (synCsi (synChwniso (synCrn (.cv k))))))
    have p1705 :=
      @gSyl syntaxFormula0382
        (.classMem (synCop (synCsn (.cv x)) (synCsn (.cv a))) (synCvv))
        (.classMem (synCsn (.cv x)) (synCvv)) p1702 p0888
    have p1706 :=
      @gPm521ni syntaxFormula0381 (.classMem (synCsn (.cv x)) (synCvv))
        syntaxFormula0382 p1701 p1705
    have p1707 :=
      @gPm261d1 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCsn (.cv x)) (synCvv)) syntaxFormula0383 p1697 p1706
    have p1708 :=
      @gBrcnv (synCsn (.cv x)) (.cv t) (synCsi (synChwniso (synCrn (.cv k))))
    have p1709 :=
      @gBrsnsi2 y (.cv x) (.cv t) (synChwniso (synCrn (.cv k))) dv_cache_0078
        dv_cache_0079 dv_cache_0144 p0853
    have p1710 :=
      @gBitri syntaxFormula0386
        (synWbr (.cv t) (synCsi (synChwniso (synCrn (.cv k)))) (synCsn (.cv x)))
        syntaxFormula0388 p1708 p1709
    have p1711 :=
      @gAnbi1i syntaxFormula0386 syntaxFormula0388
        (synWbr (.cv t) (synCsset) (synCsn (.cv a))) p1710
    have p1712 :=
      @gN1941v syntaxFormula0387 (synWbr (.cv t) (synCsset) (synCsn (.cv a))) y
        dv_cache_0081
    have p1713 :=
      @gBitr4i syntaxFormula0389
        (synWa syntaxFormula0388 (synWbr (.cv t) (synCsset) (synCsn (.cv a))))
        syntaxFormula0391 p1711 p1712
    have p1714 := @gExbii syntaxFormula0389 syntaxFormula0391 t p1713
    have p1715 := @gExcom syntaxFormula0390 t y
    have p1716 :=
      @gAnass (.classEq (.cv t) (synCsn (.cv y)))
        (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x))
        (synWbr (.cv t) (synCsset) (synCsn (.cv a)))
    have p1717 :=
      @gExbii syntaxFormula0390
        (synWa (.classEq (.cv t) (synCsn (.cv y))) syntaxFormula0392) t p1716
    have p1720 :=
      @gAnbi2d (.classEq (.cv t) (synCsn (.cv y)))
        (synWbr (.cv t) (synCsset) (synCsn (.cv a)))
        (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a)))
        (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x)) p0903
    have p1721 :=
      @gAncom (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x))
        (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a)))
    have p1724 :=
      @gAnbi1i (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a)))
        (.classMem (.cv y) (synCsn (.cv a)))
        (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x)) p0907
    have p1725 :=
      @gBitri
        (synWa (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x))
          (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a))))
        (synWa (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a)))
          (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x)))
        syntaxFormula0393 p1721 p1724
    have p1726 :=
      @gSyl6bb (.classEq (.cv t) (synCsn (.cv y))) syntaxFormula0392
        (synWa (synWbr (.cv y) (synChwniso (synCrn (.cv k))) (.cv x))
          (synWbr (synCsn (.cv y)) (synCsset) (synCsn (.cv a))))
        syntaxFormula0393 p1720 p1725
    have p1727 :=
      @gCeqsexv syntaxFormula0392 syntaxFormula0393 t (synCsn (.cv y)) dv_cache_0082
        dv_cache_0145 p0902 p1726
    have p1728 :=
      @gBitri syntaxFormula0394
        (synWex t (synWa (.classEq (.cv t) (synCsn (.cv y))) syntaxFormula0392))
        syntaxFormula0393 p1717 p1727
    have p1729 := @gExbii syntaxFormula0394 syntaxFormula0393 y p1728
    have p1730 :=
      @gN3bitri (synWex t syntaxFormula0389) (synWex t syntaxFormula0391)
        (synWex y syntaxFormula0394) (synWex y syntaxFormula0393) p1714 p1715 p1729
    have p1731 :=
      @gOpelco t (synCsn (.cv x)) (synCsn (.cv a)) (synCsset)
        (synCcnv (synCsi (synChwniso (synCrn (.cv k))))) dv_cache_0084 dv_cache_0085
        dv_cache_0086 dv_cache_0146
    have p1732 :=
      @gElima2 y (.cv x) (synChwniso (synCrn (.cv k))) (synCsn (.cv a)) dv_cache_0078
        dv_cache_0144 dv_cache_0088
    have p1733 :=
      @gN3bitr4i (synWex t syntaxFormula0389) (synWex y syntaxFormula0393)
        syntaxFormula0382 syntaxFormula0374 p1730 p1731 p1732
    have p1734 :=
      @gSyl6bb (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0381
        syntaxFormula0382 syntaxFormula0374 p1707 p1733
    have p1735 :=
      @gBibi12d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0375
        syntaxFormula0374 syntaxFormula0381 syntaxFormula0374 p1673 p1734
    have p1736 :=
      @gNotbid (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0395
        syntaxFormula0396 p1735
    have p1737 :=
      @gSyl5bb syntaxFormula0397 (.neg syntaxFormula0395)
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0398 p1656 p1736
    have p1738 :=
      @gExbidv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0397
        syntaxFormula0398 x dv_cache_0089 p1737
    have p1739 := @gExnal syntaxFormula0396 x
    have p1740 :=
      @gSyl6bb (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0399
        (synWex x syntaxFormula0398) syntaxFormula0401 p1738 p1739
    have p1741 :=
      @gSyl5bb syntaxFormula0403 syntaxFormula0399
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0401 p1655 p1740
    have p1742 :=
      @gCon2bid (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0403
        syntaxFormula0400 p1741
    have p1743 := (Nominal.classEqRefl (synCimage (synChwniso (synCrn (.cv k)))))
    have p1744 :=
      @gBreqi (synCsn (.cv a))
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))
        (synCimage (synChwniso (synCrn (.cv k)))) syntaxClass0404 p1743
    have p1745 := (Nominal.biimpRefl syntaxFormula0405)
    have p1746 :=
      @gOpexg (synCsn (.cv a))
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))) (synCvv) (synCvv)
    have p1747 :=
      @gSylancr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCsn (.cv a)) (synCvv)) syntaxFormula0373 syntaxFormula0385 p0839
        p1666 p1746
    have p1748 := @gElcomplg syntaxClass0368 syntaxClass0402 (synCvv)
    have p1749 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0385
        (synWb syntaxFormula0406 syntaxFormula0407) p1747 p1748
    have p1750 :=
      @gSyl5bb syntaxFormula0405 syntaxFormula0406
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0407 p1745 p1749
    have p1751 :=
      @gSyl5bb syntaxFormula0408 syntaxFormula0405
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0407 p1744 p1750
    have p1752 :=
      @gBitr4d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0400
        syntaxFormula0407 syntaxFormula0408 p1742 p1751
    have p1753 :=
      @gSyl5rbb
        (.classEq (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))
          (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
        syntaxFormula0400 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        syntaxFormula0408 p1654 p1752
    have p1754 :=
      @gMpbiri (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0408
        (.classEq (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))
          (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
        p1653 p1753
    have p1757 := @gImaexg (synChwniso (synCrn (.cv k))) (.cv x) (synCvv) (synCvv)
    have p1758 :=
      @gSylancl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synChwniso (synCrn (.cv k))) (synCvv))
        (.classMem (.cv x) (synCvv))
        (.classMem (synCima (synChwniso (synCrn (.cv k))) (.cv x)) (synCvv)) p1664
        p0853 p1757
    have p1759 :=
      @gEueq y (synCima (synChwniso (synCrn (.cv k))) (.cv x)) dv_cache_0147
    have p1760 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCima (synChwniso (synCrn (.cv k))) (.cv x)) (synCvv))
        (synWeu y (.classEq (.cv y) (synCima (synChwniso (synCrn (.cv k))) (.cv x))))
        p1758 p1759
    have p1763 := @gBrimage (.cv x) (.cv y) (synChwniso (synCrn (.cv k))) p0853 p0906
    have p1764 :=
      @gEubii (synWbr (.cv x) (synCimage (synChwniso (synCrn (.cv k)))) (.cv y))
        (.classEq (.cv y) (synCima (synChwniso (synCrn (.cv k))) (.cv x))) y p1763
    have p1765 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWeu y (.classEq (.cv y) (synCima (synChwniso (synCrn (.cv k))) (.cv x))))
        (synWeu y (synWbr (.cv x) (synCimage (synChwniso (synCrn (.cv k)))) (.cv y)))
        p1760 p1764
    have p1766 :=
      @gRalrimivw (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWeu y (synWbr (.cv x) (synCimage (synChwniso (synCrn (.cv k)))) (.cv y)))
        x (synCvv) dv_cache_0089 p1765
    have p1767 :=
      @gFnres x y (synCvv) (synCimage (synChwniso (synCrn (.cv k)))) dv_cache_0091
        dv_cache_0059 dv_cache_0148 dv_cache_0149 dv_cache_0007
    have p1768 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWral x (synCvv) (synWeu y
            (synWbr (.cv x) (synCimage (synChwniso (synCrn (.cv k)))) (.cv y))))
        (synWfn (synCres (synCimage (synChwniso (synCrn (.cv k)))) (synCvv)) (synCvv))
        p1766 p1767
    have p1769 := @gResid (synCimage (synChwniso (synCrn (.cv k))))
    have p1770 :=
      @gFneq1i (synCvv)
        (synCres (synCimage (synChwniso (synCrn (.cv k)))) (synCvv))
        (synCimage (synChwniso (synCrn (.cv k)))) p1769
    have p1771 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfn (synCres (synCimage (synChwniso (synCrn (.cv k)))) (synCvv)) (synCvv))
        (synWfn (synCimage (synChwniso (synCrn (.cv k)))) (synCvv)) p1768 p1770
    have p1772 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfn (synCimage (synChwniso (synCrn (.cv k)))) (synCvv)) synWtru p1771
    have p1774 :=
      @g_pm3_2 (synWfn (synCimage (synChwniso (synCrn (.cv k)))) (synCvv))
        (.classMem (synCsn (.cv a)) (synCvv))
    have p1775 :=
      @gSyl5 synWtru (.classMem (synCsn (.cv a)) (synCvv))
        (synWfn (synCimage (synChwniso (synCrn (.cv k)))) (synCvv)) syntaxFormula0409
        p0957 p1774
    have p1776 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) synWtru
        (synWfn (synCimage (synChwniso (synCrn (.cv k)))) (synCvv))
        (.imp synWtru syntaxFormula0409) p1772 p1775
    have p1777 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) synWtru
        syntaxFormula0409 p1776
    have p1778 :=
      @gMpi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) synWtru syntaxFormula0409
        p0939 p1777
    have p1779 :=
      @gFnbrfvb (synCvv) (synCsn (.cv a))
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))
        (synCimage (synChwniso (synCrn (.cv k))))
    have p1780 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0409
        (synWb (.classEq
            (synCfv (synCimage (synChwniso (synCrn (.cv k)))) (synCsn (.cv a)))
            (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))) syntaxFormula0408)
        p1778 p1779
    have p1781 :=
      @gMpbird (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (synCfv (synCimage (synChwniso (synCrn (.cv k)))) (synCsn (.cv a)))
          (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a))))
        syntaxFormula0408 p1754 p1780
    have p1782 := (Nominal.classEqRefl (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
    have p1783 :=
      @gSyl6eqr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synCfv (synCimage (synChwniso (synCrn (.cv k)))) (synCsn (.cv a)))
        (synCima (synChwniso (synCrn (.cv k))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCrn (.cv k)))) p1781 p1782
    have p1784 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (synCfv (synCimage (synChwniso (synCrn (.cv k)))) (synCsn (.cv a)))
          (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) p1783
    have p1785 :=
      @gEqeq2 (synCfv (synCimage (synChwniso (synCrn (.cv k)))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCrn (.cv k))))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
    have p1786 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classEq (synCfv (synCimage (synChwniso (synCrn (.cv k)))) (synCsn (.cv a)))
          (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
        syntaxFormula0412 p1784 p1785
    have p1787 := @gBi1 syntaxFormula0410 syntaxFormula0411
    have p1788 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0412
        (.imp syntaxFormula0410 syntaxFormula0411) p1786 p1787
    have p1789 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0410
        syntaxFormula0411 p1652 p1788
    have p1790 :=
      @gEleq1 (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))
        (synChwcn (synCrn (.cv k)))
    have p1791 := @gSneq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))
    have p1792 :=
      @gFveq2d (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synCsn (.cv a)) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synChnqmap1 (synCrn (.cv k))) p1791
    have p1793 :=
      @gEceq1 (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))
        (synChwniso (synCrn (.cv k)))
    have p1794 :=
      @gEqeq12d (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))) syntaxClass0413
        (synCec (.cv a) (synChwniso (synCrn (.cv k)))) syntaxClass0414 p1792 p1793
    have p1795 :=
      @gImbi12d (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0060
        syntaxFormula0411 syntaxFormula0415 p1790 p1794
    have p1796 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0416
        (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) syntaxFormula0417
        p1789 p1795
    have p1797 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0418 a
        dv_cache_0024 p1796
    have p1798 := @gNfv syntaxFormula0417 a dv_cache_0150
    have p1799 :=
      @gN1923 (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        syntaxFormula0417 a p1798
    have p1800 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all a syntaxFormula0418)
        (.imp (synWex a (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
          syntaxFormula0417)
        p1797 p1799
    have p1801 :=
      @gSyl5bi (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
        (synWex a (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0417 p1645 p1800
    have p1802 := @gElex (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv)
    have p1803 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
            syntaxFormula0417))
        (.imp (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
          (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv)))
        p1801 p1802
    have p1804 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
        syntaxFormula0060 syntaxFormula0415 p1803
    have p1805 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0060
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
        syntaxFormula0415 p1643 p1804
    have p1806 :=
      @gSylcom (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0060
        syntaxFormula0415 p0286 p1805
    have p1807 := @gSsv (synCpw1 (synChwcn (synCrn (.cv k))))
    have p1808 :=
      @gJctir (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfn (synCimage (synChwniso (synCrn (.cv k)))) (synCvv))
        (synWss (synCpw1 (synChwcn (synCrn (.cv k)))) (synCvv)) p1771 p1807
    have p1809 :=
      @gFnssres (synCvv) (synCpw1 (synChwcn (synCrn (.cv k))))
        (synCimage (synChwniso (synCrn (.cv k))))
    have p1810 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa (synWfn (synCimage (synChwniso (synCrn (.cv k)))) (synCvv))
          (synWss (synCpw1 (synChwcn (synCrn (.cv k)))) (synCvv)))
        (synWfn syntaxClass0367 (synCpw1 (synChwcn (synCrn (.cv k))))) p1808 p1809
    have p1812 :=
      @gFneq1i (synCpw1 (synChwcn (synCrn (.cv k)))) (synChnqmap1 (synCrn (.cv k)))
        syntaxClass0367 p1646
    have p1813 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfn syntaxClass0367 (synCpw1 (synChwcn (synCrn (.cv k)))))
        syntaxFormula0419 p1810 p1812
    have p1814 :=
      @gSnelpw1 (synCfv (synChncodetrnfn (.cv k)) (.cv u))
        (synChwcn (synCrn (.cv k)))
    have p1815 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0060
        syntaxFormula0420 p0286 p1814
    have p1816 := @g_pm3_2 syntaxFormula0419 syntaxFormula0420
    have p1817 :=
      @gSyl9 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0420
        syntaxFormula0419 syntaxFormula0421 p1815 p1816
    have p1818 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0419
        (.classMem (.cv u) (synChwcn P))
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0421) p1813
        p1817
    have p1819 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0421 p1818
    have p1820 :=
      @gFnbrfvb (synCpw1 (synChwcn (synCrn (.cv k))))
        (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))) syntaxClass0414
        (synChnqmap1 (synCrn (.cv k)))
    have p1821 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0421
        syntaxFormula0423 p1819 p1820
    have p1822 := @gBi1 syntaxFormula0415 syntaxFormula0422
    have p1823 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0423
        (.imp syntaxFormula0415 syntaxFormula0422) p1821 p1822
    have p1824 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0415
        syntaxFormula0422 p1806 p1823
    have p1825 :=
      @gBrcnv syntaxClass0414 (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synChnqmap1 (synCrn (.cv k)))
    have p1826 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0422
        syntaxFormula0424 p1824 p1825
    have p1827 :=
      @gHnqmap1valcl (synCun P Y) (synCfv (synChncodetrnfn (.cv k)) (.cv u)) p0001
    have p1828 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0357
        syntaxFormula0426 p1621 p1827
    have p1830 :=
      @gA1i (synWfn (synChnqmap1 (synCun P Y)) (synCpw1 (synChwcn (synCun P Y))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p0370
    have p1831 :=
      @gSnelpw1 (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCun P Y))
    have p1832 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0357
        syntaxFormula0427 p1621 p1831
    have p1833 :=
      @g_pm3_2 (synWfn (synChnqmap1 (synCun P Y)) (synCpw1 (synChwcn (synCun P Y))))
        syntaxFormula0427
    have p1834 :=
      @gSyl9 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0427
        (synWfn (synChnqmap1 (synCun P Y)) (synCpw1 (synChwcn (synCun P Y))))
        syntaxFormula0428 p1832 p1833
    have p1835 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfn (synChnqmap1 (synCun P Y)) (synCpw1 (synChwcn (synCun P Y))))
        (.classMem (.cv u) (synChwcn P))
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0428) p1830
        p1834
    have p1836 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0428 p1835
    have p1837 :=
      @gFnbrfvb (synCpw1 (synChwcn (synCun P Y)))
        (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))) syntaxClass0360
        (synChnqmap1 (synCun P Y))
    have p1838 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0428
        syntaxFormula0430 p1836 p1837
    have p1839 := @gBi1 syntaxFormula0426 syntaxFormula0429
    have p1840 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0430
        (.imp syntaxFormula0426 syntaxFormula0429) p1838 p1839
    have p1841 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0426
        syntaxFormula0429 p1828 p1840
    have p1842 :=
      @gJcad (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0424
        syntaxFormula0429 p1826 p1841
    have p1843 := @gSnex (synCfv (synChncodetrnfn (.cv k)) (.cv u))
    have p1844 :=
      @gId (.classEq (.cv x) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
    have p1845 :=
      @gBreq2d (.classEq (.cv x) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
        (.cv x) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))) syntaxClass0414
        (synCcnv (synChnqmap1 (synCrn (.cv k)))) p1844
    have p1847 :=
      @gBreq1d (.classEq (.cv x) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
        (.cv x) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))) syntaxClass0360
        (synChnqmap1 (synCun P Y)) p1844
    have p1848 :=
      @gAnbi12d (.classEq (.cv x) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
        syntaxFormula0431 syntaxFormula0424 syntaxFormula0432 syntaxFormula0429 p1845
        p1847
    have p1849 :=
      @gSpcev syntaxFormula0433 syntaxFormula0434 x
        (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))) dv_cache_0151 dv_cache_0152
        p1843 p1848
    have p1850 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0434
        syntaxFormula0435 p1842 p1849
    have p1851 :=
      @gBrco x syntaxClass0414 syntaxClass0360 (synChnqmap1 (synCun P Y))
        (synCcnv (synChnqmap1 (synCrn (.cv k)))) dv_cache_0153 dv_cache_0154
        dv_cache_0029 dv_cache_0155
    have p1852 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0435
        syntaxFormula0437 p1850 p1851
    have p1853 := (Nominal.classEqRefl (synChnqinc (synCrn (.cv k)) (synCun P Y)))
    have p1854 :=
      @gBreqi syntaxClass0414 syntaxClass0360
        (synChnqinc (synCrn (.cv k)) (synCun P Y)) syntaxClass0436 p1853
    have p1855 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0437
        syntaxFormula0438 p1852 p1854
    have p1856 := @gSimpl syntaxFormula0439 syntaxFormula0440
    have p1857 :=
      @gBrco p (.cv x) (.cv y) (synChnqmap1 (synCun P Y))
        (synCcnv (synChnqmap1 (synCrn (.cv k)))) dv_cache_0034 dv_cache_0035
        dv_cache_0036 dv_cache_0156
    have p1858 :=
      @gSylib syntaxFormula0441 syntaxFormula0439 syntaxFormula0443 p1856 p1857
    have p1859 := Nominal.ax17 syntaxFormula0441 p dv_cache_0157
    have p1860 := @gSimpl syntaxFormula0441 syntaxFormula0442
    have p1861 := @gSimpr syntaxFormula0439 syntaxFormula0440
    have p1862 :=
      @gBrco q (.cv x) (.cv z) (synChnqmap1 (synCun P Y))
        (synCcnv (synChnqmap1 (synCrn (.cv k)))) dv_cache_0039 dv_cache_0040
        dv_cache_0041 dv_cache_0158
    have p1863 :=
      @gSylib syntaxFormula0441 syntaxFormula0440 syntaxFormula0445 p1861 p1862
    have p1864 := @gSyl syntaxFormula0446 syntaxFormula0441 syntaxFormula0445 p1860 p1863
    have p1865 := Nominal.ax17 syntaxFormula0446 q dv_cache_0159
    have p1866 := @gSimpl syntaxFormula0446 syntaxFormula0444
    have p1867 := @gSimpr syntaxFormula0441 syntaxFormula0442
    have p1868 := @gSyl syntaxFormula0447 syntaxFormula0446 syntaxFormula0442 p1866 p1867
    have p1869 :=
      @gSimpr (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv p))
        (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y))
    have p1870 :=
      @gSyl syntaxFormula0447 syntaxFormula0442
        (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y)) p1868 p1869
    have p1876 :=
      @gSyl syntaxFormula0447 (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y))
        (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p)) (.cv y)) p1870 p0442
    have p1877 :=
      @gEqcomd syntaxFormula0447 (synCfv (synChnqmap1 (synCun P Y)) (.cv p)) (.cv y)
        p1876
    have p1881 :=
      @gSimpl (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv p))
        (synWbr (.cv p) (synChnqmap1 (synCun P Y)) (.cv y))
    have p1882 :=
      @gSyl syntaxFormula0447 syntaxFormula0442
        (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv p)) p1868 p1881
    have p1883 := @gBrcnv (.cv x) (.cv p) (synChnqmap1 (synCrn (.cv k)))
    have p1884 :=
      @gSylib syntaxFormula0447
        (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv p))
        (synWbr (.cv p) (synChnqmap1 (synCrn (.cv k))) (.cv x)) p1882 p1883
    have p1885 :=
      @gFnfun (synCpw1 (synChwcn (synCrn (.cv k)))) (synChnqmap1 (synCrn (.cv k)))
    have p1886 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0419
        (synWfun (synChnqmap1 (synCrn (.cv k)))) p1813 p1885
    have p1887 := @gFunbrfv (.cv p) (.cv x) (synChnqmap1 (synCrn (.cv k)))
    have p1888 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfun (synChnqmap1 (synCrn (.cv k))))
        (.imp (synWbr (.cv p) (synChnqmap1 (synCrn (.cv k))) (.cv x))
          (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p)) (.cv x)))
        p1886 p1887
    have p1889 :=
      @gSyl5 syntaxFormula0447 (synWbr (.cv p) (synChnqmap1 (synCrn (.cv k))) (.cv x))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p)) (.cv x)) p1884 p1888
    have p1890 := @gSimpr syntaxFormula0446 syntaxFormula0444
    have p1891 :=
      @gSimpl (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv q))
        (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z))
    have p1892 :=
      @gSyl syntaxFormula0447 syntaxFormula0444
        (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv q)) p1890 p1891
    have p1893 := @gBrcnv (.cv x) (.cv q) (synChnqmap1 (synCrn (.cv k)))
    have p1894 :=
      @gSylib syntaxFormula0447
        (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv q))
        (synWbr (.cv q) (synChnqmap1 (synCrn (.cv k))) (.cv x)) p1892 p1893
    have p1895 := @gFunbrfv (.cv q) (.cv x) (synChnqmap1 (synCrn (.cv k)))
    have p1896 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfun (synChnqmap1 (synCrn (.cv k))))
        (.imp (synWbr (.cv q) (synChnqmap1 (synCrn (.cv k))) (.cv x))
          (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q)) (.cv x)))
        p1886 p1895
    have p1897 :=
      @gSyl5 syntaxFormula0447 (synWbr (.cv q) (synChnqmap1 (synCrn (.cv k))) (.cv x))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q)) (.cv x)) p1894 p1896
    have p1898 := @gEqcom (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q)) (.cv x)
    have p1899 :=
      @gSyl6ib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q)) (.cv x))
        (.classEq (.cv x) (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))) p1897 p1898
    have p1900 :=
      @gEqeq2 (.cv x) (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p))
    have p1901 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        (.classEq (.cv x) (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q)))
        syntaxFormula0449 p1899 p1900
    have p1902 :=
      @gBi1 (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p)) (.cv x))
        syntaxFormula0448
    have p1903 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0449
        (.imp (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p)) (.cv x))
          syntaxFormula0448)
        p1901 p1902
    have p1904 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p)) (.cv x))
        syntaxFormula0448 p1889 p1903
    have p1912 := @gBreldm (.cv p) (.cv x) (synChnqmap1 (synCrn (.cv k)))
    have p1913 :=
      @gSyl syntaxFormula0447 (synWbr (.cv p) (synChnqmap1 (synCrn (.cv k))) (.cv x))
        (.classMem (.cv p) (synCdm (synChnqmap1 (synCrn (.cv k))))) p1884 p1912
    have p1914 :=
      @gFndm (synCpw1 (synChwcn (synCrn (.cv k)))) (synChnqmap1 (synCrn (.cv k)))
    have p1915 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0419
        syntaxFormula0450 p1813 p1914
    have p1916 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0450
        syntaxFormula0447 p1915
    have p1917 :=
      @gEleq2 (synCdm (synChnqmap1 (synCrn (.cv k))))
        (synCpw1 (synChwcn (synCrn (.cv k)))) (.cv p)
    have p1918 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0450
        (synWb (.classMem (.cv p) (synCdm (synChnqmap1 (synCrn (.cv k)))))
          (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k))))))
        p1916 p1917
    have p1919 :=
      @gBi1 (.classMem (.cv p) (synCdm (synChnqmap1 (synCrn (.cv k)))))
        (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k)))))
    have p1920 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        (synWb (.classMem (.cv p) (synCdm (synChnqmap1 (synCrn (.cv k)))))
          (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k))))))
        (.imp (.classMem (.cv p) (synCdm (synChnqmap1 (synCrn (.cv k)))))
          (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k))))))
        p1918 p1919
    have p1921 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        (.classMem (.cv p) (synCdm (synChnqmap1 (synCrn (.cv k)))))
        (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k))))) p1913 p1920
    have p1927 := @gBreldm (.cv q) (.cv x) (synChnqmap1 (synCrn (.cv k)))
    have p1928 :=
      @gSyl syntaxFormula0447 (synWbr (.cv q) (synChnqmap1 (synCrn (.cv k))) (.cv x))
        (.classMem (.cv q) (synCdm (synChnqmap1 (synCrn (.cv k))))) p1894 p1927
    have p1929 :=
      @gEleq2 (synCdm (synChnqmap1 (synCrn (.cv k))))
        (synCpw1 (synChwcn (synCrn (.cv k)))) (.cv q)
    have p1930 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0450
        (synWb (.classMem (.cv q) (synCdm (synChnqmap1 (synCrn (.cv k)))))
          (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k))))))
        p1916 p1929
    have p1931 :=
      @gBi1 (.classMem (.cv q) (synCdm (synChnqmap1 (synCrn (.cv k)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k)))))
    have p1932 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        (synWb (.classMem (.cv q) (synCdm (synChnqmap1 (synCrn (.cv k)))))
          (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k))))))
        (.imp (.classMem (.cv q) (synCdm (synChnqmap1 (synCrn (.cv k)))))
          (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k))))))
        p1930 p1931
    have p1933 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        (.classMem (.cv q) (synCdm (synChnqmap1 (synCrn (.cv k)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k))))) p1928 p1932
    have p1934 :=
      @gJcad (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k))))) p1921 p1933
    have p1935 :=
      @gSimpl (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k)))))
    have p1936 := @gHnwpw1argcl (synChwcn (synCrn (.cv k))) p
    have p1937 :=
      @gSimprd (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p1936
    have p1938 :=
      @gSyl syntaxFormula0451
        (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p1935 p1937
    have p1939 :=
      @gFveq2d syntaxFormula0451 (.cv p) (synCsn (synCuni (.cv p)))
        (synChnqmap1 (synCun P Y)) p1938
    have p1942 :=
      @gSimpld (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classEq (.cv p) (synCsn (synCuni (.cv p)))) p1936
    have p1943 :=
      @gSyl syntaxFormula0451
        (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k)))) p1935 p1942
    have p1944 :=
      @gSseld (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synChwcn (synCrn (.cv k))) (synChwcn (synCun P Y)) (synCuni (.cv p)) p1618
    have p1945 :=
      @gSyl5 syntaxFormula0451
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv p)) (synChwcn (synCun P Y))) p1943 p1944
    have p1947 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        (.classMem (synCuni (.cv p)) (synChwcn (synCun P Y))) syntaxFormula0112 p1945
        p0558
    have p1949 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0112 syntaxFormula0115 p1947 p0560
    have p1951 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0115 syntaxFormula0116 p1949 p0562
    have p1952 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0113 syntaxFormula0114 p1939 p1951
    have p1953 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0114 syntaxFormula0448 p1952
    have p1958 :=
      @gFveq2d syntaxFormula0451 (.cv p) (synCsn (synCuni (.cv p)))
        (synChnqmap1 (synCrn (.cv k))) p1938
    have p1963 := @gElex (synCuni (.cv p)) (synChwcn (synCrn (.cv k)))
    have p1966 := @gEleq1 (.cv a) (synCuni (.cv p)) (synChwcn (synCrn (.cv k)))
    have p1968 :=
      @gFveq2d (.classEq (.cv a) (synCuni (.cv p))) (synCsn (.cv a))
        (synCsn (synCuni (.cv p))) (synChnqmap1 (synCrn (.cv k))) p1123
    exact
      continuation p1664 p1789 p1790 p1793 p1802 p1813 p1841 p1843 p1844 p1847 p1853 p1855
        p1858 p1859 p1864 p1865 p1877 p1890 p1904 p1915 p1934 p1943 p1945 p1953 p1958
        p1963 p1966 p1968

end NFChoice.DirectNominalPrf.WPPReplay

end
