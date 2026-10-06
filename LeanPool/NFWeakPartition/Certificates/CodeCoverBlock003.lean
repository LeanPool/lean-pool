/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk017Compact001Block020

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `ReplaySupport.CodeCover7`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_cfbhnqinjcodecoverddndv_stage7`. -/
@[expose]
noncomputable def gCfbhnqinjcodecoverddndvStage7 (u : Var) (P : Class) (k : Var)
    (Y : Class) (p0628 : _) (p0630 : _) (p0639 : _) (p0641 : _) (p0653 : _) (p0657 : _)
    (p0660 : _) (p0668 : _) (p0677 : _) (p0684 : _) (p0691 : _) (p0697 : _) (p0715 : _)
    (p0717 : _) (p0719 : _) (p0721 : _) (p0724 : _) (p0726 : _) (p0734 : _) (p0736 : _)
    (p0738 : _) (p0742 : _) (p0744 : _) (p0746 : _) (p0752 : _) (p0754 : _) (p0764 : _)
    (p0773 : _) (p0781 : _) (p0805 : _) (p1121 : _) (p1161 : _) (p1163 : _) (p1208 : _)
    (p1248 : _) (p1618 : _) (p1662 : _) (p1664 : _) (p1789 : _) (p1853 : _) (p1858 : _)
    (p1859 : _) (p1864 : _) (p1865 : _) (p1877 : _) (p1890 : _) (p1904 : _) (p1915 : _)
    (p1934 : _) (p1943 : _) (p1945 : _) (p1953 : _) (p1958 : _) (p1963 : _) (p1966 : _)
    (p1968 : _) {Result : Type} (continuation : _ → _ → _ → _ → _ → _ → _ → Result) :=
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
    have fresh_q_ne_k : q ≠ k := by
      intro h
      exact
        fresh_q
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_q_not_Y : q ∉ Y.fv := by
      intro h
      exact fresh_q (Finset.mem_union_right _ (h))
    have fresh_h : h ∉ proofSupport :=
      by
      change freshVar proofSupport 8 ∉ proofSupport
      exact freshVar_not_mem proofSupport 8
    have fresh_h_ne_k : h ≠ k := by
      intro h
      exact
        fresh_h
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
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
    have fresh_y_ne_x : y ≠ x :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 2
      exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
    have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
    have fresh_y_ne_z : y ≠ z :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
    have fresh_y_ne_p : y ≠ p :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
    have fresh_y_ne_q : y ≠ q :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
    have fresh_y_ne_h : y ≠ h :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 8
      exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
    have fresh_h_ne_y : h ≠ y := Ne.symm fresh_y_ne_h
    have fresh_x_ne_z : x ≠ z :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
    have fresh_x_ne_p : x ≠ p :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
    have fresh_x_ne_h : x ≠ h :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 8
      exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
    have fresh_h_ne_x : h ≠ x := Ne.symm fresh_x_ne_h
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
    have dv_cache_0007 : x ≠ y := by exact (show x ≠ y from (by exact fresh_x_ne_y))
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
    have dv_cache_0052 : h ≠ x := by exact (show h ≠ x from (by exact fresh_h_ne_x))
    have dv_cache_0053 : h ≠ y := by exact (show h ≠ y from (by exact fresh_h_ne_y))
    have dv_cache_0069 : x ≠ z := by exact (show x ≠ z from (by exact fresh_x_ne_z))
    have dv_cache_0070 : y ≠ z := by exact (show y ≠ z from (by exact fresh_y_ne_z))
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
    have dv_cache_0109 : a ∉ ((Class.cv q)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_q, not_false_eq_true])
    have dv_cache_0160 :
      a ∉
        ((Wff.imp (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k)))) (.classEq
              (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (synCuni (.cv p))))
              (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0161 :
      a ∉
        ((Wff.imp (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))) (.classEq
              (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (synCuni (.cv q))))
              (synCec (synCuni (.cv q)) (synChwniso (synCrn (.cv k))))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_q, fresh_a_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0162 :
      a ∉
        ((Wff.imp (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
              (.classMem (.cv v) (synChwcn (synCrn (.cv k))))) (synWb
              (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
                (synCec (.cv v) (synChwniso (synCrn (.cv k)))))
              (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (.cv v))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_k, fresh_a_ne_v, or_false,
            not_false_eq_true])
    have dv_cache_0163 :
      v ∉
        ((Wff.imp (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
              (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k))))) (synWb
              (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
                (synCec (synCuni (.cv q)) (synChwniso (synCrn (.cv k)))))
              (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k)))
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_singleton, fresh_v_ne_p, fresh_v_ne_k, fresh_v_ne_q, or_false,
            not_false_eq_true])
    have dv_cache_0164 : h ∉ ((synCrn (.cv k))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_h_ne_k,
            not_false_eq_true])
    have dv_cache_0165 :
      x ∉
        ((Wff.imp (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
              (.classMem (.cv y) (synChwcn (synCrn (.cv k)))))
            (.imp (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (.cv y))
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_p, fresh_x_ne_k, fresh_x_ne_y, fresh_x_not_P,
            fresh_x_not_Y, or_false, not_false_eq_true])
    have dv_cache_0166 :
      y ∉
        ((Wff.imp (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
              (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k))))) (.imp
              (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (synCuni (.cv q)))
              (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y))
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_k, fresh_y_ne_q, fresh_y_not_P,
            fresh_y_not_Y, or_false, not_false_eq_true])
    have dv_cache_0167 :
      x ∉
        ((synCcom (synChnqmap1 (synCun P Y))
            (synCcnv (synChnqmap1 (synCrn (.cv k)))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_x_not_P, fresh_x_not_Y, fresh_x_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0168 :
      y ∉
        ((synCcom (synChnqmap1 (synCun P Y))
            (synCcnv (synChnqmap1 (synCrn (.cv k)))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_y_not_P, fresh_y_not_Y, fresh_y_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0169 :
      z ∉
        ((synCcom (synChnqmap1 (synCun P Y))
            (synCcnv (synChnqmap1 (synCrn (.cv k)))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_z_not_P, fresh_z_not_Y, fresh_z_ne_k, or_false,
            not_false_eq_true])
    let syntaxFormula0114 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv p))
        (synCec (synCuni (.cv p)) (synChwniso (synCun P Y))))
    let syntaxFormula0130 : Wff :=
      (synWa (.classMem (.cv x) (synChwcn (synCun P Y)))
        (.classMem (.cv y) (synChwcn (synCun P Y))))
    let syntaxFormula0131 : Wff :=
      (synWa (.classMem (.cv x) (synChwcodes (synCun P Y)))
        (.classMem (.cv y) (synChwcodes (synCun P Y))))
    let syntaxFormula0133 : Wff :=
      (synWiso (.cv h) (synCfv (synC1st) (.cv x)) (synCfv (synC1st) (.cv y))
        (synCfv (synC2nd) (.cv x)) (synCfv (synC2nd) (.cv y)))
    let syntaxFormula0134 : Wff := (synWex h syntaxFormula0133)
    let syntaxFormula0135 : Wff := (synWa syntaxFormula0131 syntaxFormula0134)
    let syntaxFormula0141 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) (.classMem (synCuni (.cv p)) (synCvv)))
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
    let syntaxFormula0168 : Wff :=
      (synWb (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv p)))
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q))))
    let syntaxFormula0169 : Wff :=
      (.imp (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv p)))
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q))))
    let syntaxFormula0411 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
    let syntaxFormula0416 : Wff :=
      (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0411)
    let syntaxClass0436 : Class :=
      (synCcom (synChnqmap1 (synCun P Y)) (synCcnv (synChnqmap1 (synCrn (.cv k)))))
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
    let syntaxFormula0451 : Wff :=
      (synWa (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k))))))
    let syntaxFormula0452 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (synCuni (.cv p))))
        (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k)))))
    let syntaxFormula0453 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k)))) syntaxFormula0452)
    let syntaxFormula0454 : Wff :=
      (.imp (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0453)
    let syntaxFormula0455 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (synCuni (.cv p)))))
    let syntaxFormula0456 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p))
        (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k)))))
    let syntaxFormula0457 : Wff := (synWb syntaxFormula0455 syntaxFormula0456)
    let syntaxFormula0458 : Wff := (synWa syntaxFormula0451 syntaxFormula0448)
    let syntaxFormula0459 : Wff :=
      (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q)))
    let syntaxFormula0460 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (synCuni (.cv q))))
        (synCec (synCuni (.cv q)) (synChwniso (synCrn (.cv k)))))
    let syntaxFormula0461 : Wff :=
      (.imp (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))) syntaxFormula0460)
    let syntaxFormula0462 : Wff :=
      (.imp (.classEq (.cv a) (synCuni (.cv q))) syntaxFormula0461)
    let syntaxFormula0463 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (synCuni (.cv q)))))
    let syntaxFormula0464 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
        (synCec (synCuni (.cv q)) (synChwniso (synCrn (.cv k)))))
    let syntaxFormula0465 : Wff := (synWb syntaxFormula0463 syntaxFormula0464)
    let syntaxFormula0466 : Wff :=
      (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
        (synCec (synCuni (.cv q)) (synChwniso (synCrn (.cv k)))))
    let syntaxFormula0467 : Wff := (synWb syntaxFormula0459 syntaxFormula0466)
    let syntaxFormula0468 : Wff :=
      (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))))
    let syntaxFormula0469 : Wff :=
      (synWa (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv v) (synChwcn (synCrn (.cv k)))))
    let syntaxFormula0470 : Wff :=
      (synWa (.classMem (synCrn (.cv k)) (synCvv)) syntaxFormula0469)
    let syntaxFormula0471 : Wff :=
      (.classEq (synCec (.cv a) (synChwniso (synCrn (.cv k))))
        (synCec (.cv v) (synChwniso (synCrn (.cv k)))))
    let syntaxFormula0472 : Wff :=
      (synWb syntaxFormula0471 (synWbr (.cv a) (synChwniso (synCrn (.cv k))) (.cv v)))
    let syntaxFormula0473 : Wff :=
      (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
        (synCec (.cv v) (synChwniso (synCrn (.cv k)))))
    let syntaxFormula0474 : Wff :=
      (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv v) (synChwcn (synCrn (.cv k)))))
    let syntaxFormula0475 : Wff :=
      (synWb syntaxFormula0473
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (.cv v)))
    let syntaxFormula0476 : Wff := (.imp syntaxFormula0474 syntaxFormula0475)
    let syntaxFormula0477 : Wff :=
      (.imp (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0476)
    let syntaxFormula0478 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0476)
    let syntaxFormula0479 : Wff :=
      (synWb syntaxFormula0466
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (synCuni (.cv q))))
    let syntaxFormula0480 : Wff := (.imp syntaxFormula0468 syntaxFormula0479)
    let syntaxFormula0481 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0480)
    let syntaxFormula0482 : Wff :=
      (.imp (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0481)
    let syntaxFormula0483 : Wff :=
      (.imp (.classMem (synCuni (.cv q)) (synCvv)) syntaxFormula0481)
    let syntaxFormula0484 : Wff :=
      (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0483)
    let syntaxFormula0485 : Wff :=
      (synWa (.classMem (.cv x) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv y) (synChwcn (synCrn (.cv k)))))
    let syntaxFormula0486 : Wff :=
      (synWa syntaxFormula0485 (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y)))
    let syntaxFormula0487 : Wff :=
      (synWa (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv y) (synChwcn (synCrn (.cv k)))))
    let syntaxFormula0488 : Wff :=
      (.imp (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (.cv y))
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (.cv y)))
    let syntaxFormula0489 : Wff := (.imp syntaxFormula0487 syntaxFormula0488)
    let syntaxFormula0490 : Wff :=
      (.imp (.classEq (.cv x) (synCuni (.cv p))) syntaxFormula0489)
    let syntaxFormula0491 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0489)
    let syntaxFormula0492 : Wff :=
      (.imp (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (synCuni (.cv q)))
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))))
    let syntaxFormula0493 : Wff := (.imp syntaxFormula0468 syntaxFormula0492)
    let syntaxFormula0494 : Wff :=
      (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0493)
    let syntaxFormula0495 : Wff :=
      (.imp (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0494)
    let syntaxFormula0496 : Wff :=
      (.imp (.classMem (synCuni (.cv q)) (synCvv)) syntaxFormula0494)
    let syntaxFormula0497 : Wff :=
      (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0496)
    let syntaxFormula0498 : Wff := (.imp syntaxFormula0444 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0499 : Wff := (.all q syntaxFormula0498)
    let syntaxFormula0500 : Wff := (.imp syntaxFormula0442 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0501 : Wff := (.all p syntaxFormula0500)
    let syntaxFormula0502 : Wff := (.imp syntaxFormula0441 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0503 : Wff := (.all z syntaxFormula0502)
    let syntaxFormula0504 : Wff := (.all y syntaxFormula0503)
    let syntaxFormula0505 : Wff := (.all x syntaxFormula0504)
    let syntaxFormula0506 : Wff :=
      (synWss (synCrn (synCcnv (synChnqmap1 (synCrn (.cv k)))))
        (synCdm (synChnqmap1 (synCun P Y))))
    let syntaxClass0507 : Class := (synCdm syntaxClass0436)
    let syntaxFormula0508 : Wff :=
      (.classMem (synCec (.cv a) (synChwniso (synCrn (.cv k))))
        (synCqs (synChwcn (synCrn (.cv k))) (synChwniso (synCrn (.cv k)))))
    have p1969 := @gEceq1 (.cv a) (synCuni (.cv p)) (synChwniso (synCrn (.cv k)))
    have p1970 :=
      @gEqeq12d (.classEq (.cv a) (synCuni (.cv p)))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (synCuni (.cv p))))
        (synCec (.cv a) (synChwniso (synCrn (.cv k))))
        (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k)))) p1968 p1969
    have p1971 :=
      @gImbi12d (.classEq (.cv a) (synCuni (.cv p)))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k)))) syntaxFormula0411
        syntaxFormula0452 p1966 p1970
    have p1972 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0416
        (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0453 p1789 p1971
    have p1973 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0454 a
        dv_cache_0024 p1972
    have p1974 := @gNfv syntaxFormula0453 a dv_cache_0160
    have p1975 :=
      @gN1923 (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0453 a p1974
    have p1976 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all a syntaxFormula0454)
        (.imp (synWex a (.classEq (.cv a) (synCuni (.cv p)))) syntaxFormula0453) p1973
        p1975
    have p1977 :=
      @gSyl5bi (.classMem (synCuni (.cv p)) (synCvv))
        (synWex a (.classEq (.cv a) (synCuni (.cv p))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0453 p1121 p1976
    have p1979 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0453))
        syntaxFormula0141 p1977 p0677
    have p1980 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv p)) (synCvv))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k)))) syntaxFormula0452
        p1979
    have p1981 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0452 p1963 p1980
    have p1982 :=
      @gSyl5 syntaxFormula0451
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0452 p1943 p1981
    have p1983 :=
      @gEqeq2 (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (synCuni (.cv p))))
        (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p))
    have p1984 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0452 syntaxFormula0457 p1982 p1983
    have p1985 := @gBi1 syntaxFormula0455 syntaxFormula0456
    have p1986 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0457 (.imp syntaxFormula0455 syntaxFormula0456) p1984 p1985
    have p1987 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0455 syntaxFormula0456 p1958 p1986
    have p1988 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0456 syntaxFormula0448 p1987
    have p1989 :=
      @gEqcom (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p))
        (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
    have p1990 :=
      @gSyl6ib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0456
        (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
          (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p)))
        p1988 p1989
    have p1991 := @gSimpr syntaxFormula0451 syntaxFormula0448
    have p1992 :=
      @gEqeq2d syntaxFormula0458 (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
        (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k)))) p1991
    have p1993 :=
      @gMpbidi syntaxFormula0458
        (.classEq (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
          (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv p)))
        syntaxFormula0459 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p1990 p1992
    have p1994 :=
      @gSimpr (.classMem (.cv p) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k)))))
    have p1995 := @gHnwpw1argcl (synChwcn (synCrn (.cv k))) q
    have p1996 :=
      @gSimprd (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k))))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p1995
    have p1997 :=
      @gSyl syntaxFormula0451
        (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p1994 p1996
    have p1998 :=
      @gFveq2d syntaxFormula0451 (.cv q) (synCsn (synCuni (.cv q)))
        (synChnqmap1 (synCrn (.cv k))) p1997
    have p2001 :=
      @gSimpld (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k))))
        (.classEq (.cv q) (synCsn (synCuni (.cv q)))) p1995
    have p2002 :=
      @gSyl syntaxFormula0451
        (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))) p1994 p2001
    have p2003 := @gElex (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))
    have p2006 := @gEleq1 (.cv a) (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))
    have p2008 :=
      @gFveq2d (.classEq (.cv a) (synCuni (.cv q))) (synCsn (.cv a))
        (synCsn (synCuni (.cv q))) (synChnqmap1 (synCrn (.cv k))) p1163
    have p2009 := @gEceq1 (.cv a) (synCuni (.cv q)) (synChwniso (synCrn (.cv k)))
    have p2010 :=
      @gEqeq12d (.classEq (.cv a) (synCuni (.cv q)))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (synCuni (.cv q))))
        (synCec (.cv a) (synChwniso (synCrn (.cv k))))
        (synCec (synCuni (.cv q)) (synChwniso (synCrn (.cv k)))) p2008 p2009
    have p2011 :=
      @gImbi12d (.classEq (.cv a) (synCuni (.cv q)))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))) syntaxFormula0411
        syntaxFormula0460 p2006 p2010
    have p2012 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0416
        (.classEq (.cv a) (synCuni (.cv q))) syntaxFormula0461 p1789 p2011
    have p2013 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0462 a
        dv_cache_0024 p2012
    have p2014 := @gNfv syntaxFormula0461 a dv_cache_0161
    have p2015 :=
      @gN1923 (.classEq (.cv a) (synCuni (.cv q))) syntaxFormula0461 a p2014
    have p2016 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all a syntaxFormula0462)
        (.imp (synWex a (.classEq (.cv a) (synCuni (.cv q)))) syntaxFormula0461) p2013
        p2015
    have p2017 :=
      @gSyl5bi (.classMem (synCuni (.cv q)) (synCvv))
        (synWex a (.classEq (.cv a) (synCuni (.cv q))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0461 p1161 p2016
    have p2019 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (synCuni (.cv q)) (synCvv)) syntaxFormula0461))
        syntaxFormula0148 p2017 p0697
    have p2020 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv q)) (synCvv))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))) syntaxFormula0460
        p2019
    have p2021 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv q)) (synCvv)) syntaxFormula0460 p2003 p2020
    have p2022 :=
      @gSyl5 syntaxFormula0451
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0460 p2002 p2021
    have p2023 :=
      @gEqeq2 (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (synCuni (.cv q))))
        (synCec (synCuni (.cv q)) (synChwniso (synCrn (.cv k))))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
    have p2024 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0460 syntaxFormula0465 p2022 p2023
    have p2025 := @gBi1 syntaxFormula0463 syntaxFormula0464
    have p2026 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0465 (.imp syntaxFormula0463 syntaxFormula0464) p2024 p2025
    have p2027 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0463 syntaxFormula0464 p1998 p2026
    have p2028 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0464 syntaxFormula0448 p2027
    have p2029 :=
      @gEqeq2 (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
        (synCec (synCuni (.cv q)) (synChwniso (synCrn (.cv k))))
        (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
    have p2030 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0464 syntaxFormula0467 p2028 p2029
    have p2031 := @gBi1 syntaxFormula0459 syntaxFormula0466
    have p2032 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0467 (.imp syntaxFormula0459 syntaxFormula0466) p2030 p2031
    have p2033 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0459 syntaxFormula0466 p1993 p2032
    have p2042 :=
      @gJca syntaxFormula0451
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))) p1943 p2002
    have p2043 := @gAdantr syntaxFormula0451 syntaxFormula0468 syntaxFormula0448 p2042
    have p2044 :=
      @gSimpl (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k))))
    have p2046 :=
      @gSyl syntaxFormula0468
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv p)) (synCvv)) p2044 p1963
    have p2047 :=
      @gSimpr (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k))))
    have p2049 :=
      @gSyl syntaxFormula0468
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv q)) (synCvv)) p2047 p2003
    have p2050 :=
      @gJca syntaxFormula0468 (.classMem (synCuni (.cv p)) (synCvv))
        (.classMem (synCuni (.cv q)) (synCvv)) p2046 p2049
    have p2055 := @gId syntaxFormula0469
    have p2056 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCrn (.cv k)) (synCvv)) syntaxFormula0469 p1662
    have p2057 := @g_pm3_2 (.classMem (synCrn (.cv k)) (synCvv)) syntaxFormula0469
    have p2058 :=
      @gSyl56 syntaxFormula0469 syntaxFormula0469
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCrn (.cv k)) (synCvv)) (.imp syntaxFormula0469 syntaxFormula0470)
        p2055 p2056 p2057
    have p2059 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0469
        syntaxFormula0470 p2058
    have p2060 := @gHwnisoclasseqb v a (synCrn (.cv k))
    have p2061 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0469
        syntaxFormula0470 syntaxFormula0472 p2059 p2060
    have p2063 := @gBiid (.classMem (.cv v) (synChwcn (synCrn (.cv k))))
    have p2064 :=
      @gA1i
        (synWb (.classMem (.cv v) (synChwcn (synCrn (.cv k))))
          (.classMem (.cv v) (synChwcn (synCrn (.cv k)))))
        (.classEq (.cv a) (synCuni (.cv p))) p2063
    have p2065 :=
      @gAnbi12d (.classEq (.cv a) (synCuni (.cv p)))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv v) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv v) (synChwcn (synCrn (.cv k)))) p1966 p2064
    have p2067 :=
      @gEqeq1d (.classEq (.cv a) (synCuni (.cv p)))
        (synCec (.cv a) (synChwniso (synCrn (.cv k))))
        (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k))))
        (synCec (.cv v) (synChwniso (synCrn (.cv k)))) p1969
    have p2068 :=
      @gBreq1 (.cv a) (synCuni (.cv p)) (.cv v) (synChwniso (synCrn (.cv k)))
    have p2069 :=
      @gBibi12d (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0471 syntaxFormula0473
        (synWbr (.cv a) (synChwniso (synCrn (.cv k))) (.cv v))
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (.cv v)) p2067 p2068
    have p2070 :=
      @gImbi12d (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0469 syntaxFormula0474
        syntaxFormula0472 syntaxFormula0475 p2065 p2069
    have p2071 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0469 syntaxFormula0472) (.classEq (.cv a) (synCuni (.cv p)))
        syntaxFormula0476 p2061 p2070
    have p2072 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0477 a
        dv_cache_0024 p2071
    have p2073 := @gNfv syntaxFormula0476 a dv_cache_0162
    have p2074 :=
      @gN1923 (.classEq (.cv a) (synCuni (.cv p))) syntaxFormula0476 a p2073
    have p2075 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all a syntaxFormula0477)
        (.imp (synWex a (.classEq (.cv a) (synCuni (.cv p)))) syntaxFormula0476) p2072
        p2074
    have p2076 :=
      @gSyl5bi (.classMem (synCuni (.cv p)) (synCvv))
        (synWex a (.classEq (.cv a) (synCuni (.cv p))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0476 p1121 p2075
    have p2078 :=
      @gA1ii (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0478)
        syntaxFormula0141 p2076 p0677
    have p2079 := @gBiid (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
    have p2080 :=
      @gA1i
        (synWb (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
          (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k)))))
        (.classEq (.cv v) (synCuni (.cv q))) p2079
    have p2081 := @gEleq1 (.cv v) (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))
    have p2082 :=
      @gAnbi12d (.classEq (.cv v) (synCuni (.cv q)))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv v) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))) p2080 p2081
    have p2083 := @gEceq1 (.cv v) (synCuni (.cv q)) (synChwniso (synCrn (.cv k)))
    have p2084 :=
      @gEqeq2d (.classEq (.cv v) (synCuni (.cv q)))
        (synCec (.cv v) (synChwniso (synCrn (.cv k))))
        (synCec (synCuni (.cv q)) (synChwniso (synCrn (.cv k))))
        (synCec (synCuni (.cv p)) (synChwniso (synCrn (.cv k)))) p2083
    have p2085 :=
      @gBreq2 (.cv v) (synCuni (.cv q)) (synCuni (.cv p))
        (synChwniso (synCrn (.cv k)))
    have p2086 :=
      @gBibi12d (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0473 syntaxFormula0466
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (.cv v))
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (synCuni (.cv q)))
        p2084 p2085
    have p2087 :=
      @gImbi12d (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0474 syntaxFormula0468
        syntaxFormula0475 syntaxFormula0479 p2082 p2086
    have p2088 :=
      @gImbi2d (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0476 syntaxFormula0480
        (.classMem (synCuni (.cv p)) (synCvv)) p2087
    have p2089 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0478
        (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0481 p2078 p2088
    have p2090 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0482 v
        dv_cache_0103 p2089
    have p2093 := @gNfv syntaxFormula0480 v dv_cache_0163
    have p2094 :=
      @gNfim (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0480 v p1248 p2093
    have p2095 :=
      @gN1923 (.classEq (.cv v) (synCuni (.cv q))) syntaxFormula0481 v p2094
    have p2096 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all v syntaxFormula0482)
        (.imp (synWex v (.classEq (.cv v) (synCuni (.cv q)))) syntaxFormula0481) p2090
        p2095
    have p2097 :=
      @gSyl5bi (.classMem (synCuni (.cv q)) (synCvv))
        (synWex v (.classEq (.cv v) (synCuni (.cv q))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0481 p1208 p2096
    have p2099 := @gA1ii syntaxFormula0484 syntaxFormula0148 p2097 p0697
    have p2101 := @gA1ii syntaxFormula0484 syntaxFormula0141 p2099 p0677
    have p2102 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv q)) (synCvv)) (.classMem (synCuni (.cv p)) (synCvv))
        syntaxFormula0480 p2101
    have p2103 :=
      @gImp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv p)) (synCvv)) (.classMem (synCuni (.cv q)) (synCvv))
        syntaxFormula0480 p2102
    have p2104 :=
      @gSyl5 syntaxFormula0468 syntaxFormula0149
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0480 p2050 p2103
    have p2105 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0468
        syntaxFormula0479 p2104
    have p2106 :=
      @gSyl5 syntaxFormula0458 syntaxFormula0468
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0479 p2043 p2105
    have p2107 :=
      @gBi1 syntaxFormula0466
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (synCuni (.cv q)))
    have p2108 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0479
        (.imp syntaxFormula0466
          (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (synCuni (.cv q))))
        p2106 p2107
    have p2109 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0466
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (synCuni (.cv q)))
        p2033 p2108
    have p2131 :=
      @gSimpl (.classMem (.cv x) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv y) (synChwcn (synCrn (.cv k))))
    have p2132 :=
      @gSseld (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synChwcn (synCrn (.cv k))) (synChwcn (synCun P Y)) (.cv x) p1618
    have p2133 :=
      @gSyl5 syntaxFormula0485 (.classMem (.cv x) (synChwcn (synCrn (.cv k))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv x) (synChwcn (synCun P Y))) p2131 p2132
    have p2134 :=
      @gSimpr (.classMem (.cv x) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv y) (synChwcn (synCrn (.cv k))))
    have p2135 :=
      @gSseld (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synChwcn (synCrn (.cv k))) (synChwcn (synCun P Y)) (.cv y) p1618
    have p2136 :=
      @gSyl5 syntaxFormula0485 (.classMem (.cv y) (synChwcn (synCrn (.cv k))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv y) (synChwcn (synCun P Y))) p2134 p2135
    have p2137 :=
      @gJcad (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0485
        (.classMem (.cv x) (synChwcn (synCun P Y)))
        (.classMem (.cv y) (synChwcn (synCun P Y))) p2133 p2136
    have p2138 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0485
        syntaxFormula0130 (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y)) p2137
    have p2140 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0485
        (.classMem (.cv x) (synChwcn (synCun P Y)))
        (.classMem (.cv x) (synChwcodes (synCun P Y))) p2133 p0639
    have p2142 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0485
        (.classMem (.cv y) (synChwcn (synCun P Y)))
        (.classMem (.cv y) (synChwcodes (synCun P Y))) p2136 p0641
    have p2143 :=
      @gJcad (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0485
        (.classMem (.cv x) (synChwcodes (synCun P Y)))
        (.classMem (.cv y) (synChwcodes (synCun P Y))) p2140 p2142
    have p2144 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0485
        syntaxFormula0131 (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y)) p2143
    have p2145 :=
      @gSimpr syntaxFormula0485 (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y))
    have p2146 := @gHwnisohwisob y x (synCrn (.cv k)) dv_cache_0007
    have p2147 :=
      @gBiimpi (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y))
        (synWa syntaxFormula0485 (synWbr (.cv x) (synChwiso (synCrn (.cv k))) (.cv y)))
        p2146
    have p2148 :=
      @gSimprd (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y))
        syntaxFormula0485 (synWbr (.cv x) (synChwiso (synCrn (.cv k))) (.cv y)) p2147
    have p2149 :=
      @gSyl syntaxFormula0486 (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y))
        (synWbr (.cv x) (synChwiso (synCrn (.cv k))) (.cv y)) p2145 p2148
    have p2150 :=
      @gBrhwisoany y x (synCrn (.cv k)) h dv_cache_0164 dv_cache_0052 dv_cache_0053
    have p2151 :=
      @gSylib syntaxFormula0486 (synWbr (.cv x) (synChwiso (synCrn (.cv k))) (.cv y))
        (synWa (synWa (.classMem (.cv x) (synChwcodes (synCrn (.cv k))))
            (.classMem (.cv y) (synChwcodes (synCrn (.cv k))))) syntaxFormula0134)
        p2149 p2150
    have p2152 :=
      @gSimprd syntaxFormula0486
        (synWa (.classMem (.cv x) (synChwcodes (synCrn (.cv k))))
          (.classMem (.cv y) (synChwcodes (synCrn (.cv k)))))
        syntaxFormula0134 p2151
    have p2154 :=
      @gSyl5 syntaxFormula0486 syntaxFormula0134 syntaxFormula0131 syntaxFormula0135
        p2152 p0653
    have p2155 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0486
        syntaxFormula0131 (.imp syntaxFormula0486 syntaxFormula0135) p2144 p2154
    have p2156 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0486
        syntaxFormula0135 p2155
    have p2158 :=
      @gSyl6ibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0486
        syntaxFormula0135 (synWbr (.cv x) (synChwiso (synCun P Y)) (.cv y)) p2156 p0657
    have p2159 :=
      @gJcad (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0486
        syntaxFormula0130 (synWbr (.cv x) (synChwiso (synCun P Y)) (.cv y)) p2138 p2158
    have p2161 :=
      @gSyl6ibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0486
        (synWa syntaxFormula0130 (synWbr (.cv x) (synChwiso (synCun P Y)) (.cv y)))
        (synWbr (.cv x) (synChwniso (synCun P Y)) (.cv y)) p2159 p0660
    have p2162 :=
      @gExp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0485
        (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y))
        (synWbr (.cv x) (synChwniso (synCun P Y)) (.cv y)) p2161
    have p2163 := @gEleq1 (.cv x) (synCuni (.cv p)) (synChwcn (synCrn (.cv k)))
    have p2164 := @gBiid (.classMem (.cv y) (synChwcn (synCrn (.cv k))))
    have p2165 :=
      @gA1i
        (synWb (.classMem (.cv y) (synChwcn (synCrn (.cv k))))
          (.classMem (.cv y) (synChwcn (synCrn (.cv k)))))
        (.classEq (.cv x) (synCuni (.cv p))) p2164
    have p2166 :=
      @gAnbi12d (.classEq (.cv x) (synCuni (.cv p)))
        (.classMem (.cv x) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv y) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv y) (synChwcn (synCrn (.cv k)))) p2163 p2165
    have p2167 :=
      @gBreq1 (.cv x) (synCuni (.cv p)) (.cv y) (synChwniso (synCrn (.cv k)))
    have p2169 :=
      @gImbi12d (.classEq (.cv x) (synCuni (.cv p)))
        (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y))
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (.cv y))
        (synWbr (.cv x) (synChwniso (synCun P Y)) (.cv y))
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (.cv y)) p2167 p0668
    have p2170 :=
      @gImbi12d (.classEq (.cv x) (synCuni (.cv p))) syntaxFormula0485 syntaxFormula0487
        (.imp (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y))
          (synWbr (.cv x) (synChwniso (synCun P Y)) (.cv y)))
        syntaxFormula0488 p2166 p2169
    have p2171 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0485 (.imp (synWbr (.cv x) (synChwniso (synCrn (.cv k))) (.cv y))
            (synWbr (.cv x) (synChwniso (synCun P Y)) (.cv y))))
        (.classEq (.cv x) (synCuni (.cv p))) syntaxFormula0489 p2162 p2170
    have p2172 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0490 x
        dv_cache_0089 p2171
    have p2173 := @gNfv syntaxFormula0489 x dv_cache_0165
    have p2174 :=
      @gN1923 (.classEq (.cv x) (synCuni (.cv p))) syntaxFormula0489 x p2173
    have p2175 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all x syntaxFormula0490)
        (.imp (synWex x (.classEq (.cv x) (synCuni (.cv p)))) syntaxFormula0489) p2172
        p2174
    have p2176 :=
      @gSyl5bi (.classMem (synCuni (.cv p)) (synCvv))
        (synWex x (.classEq (.cv x) (synCuni (.cv p))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0489 p0630 p2175
    have p2178 :=
      @gA1ii (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0491)
        syntaxFormula0141 p2176 p0677
    have p2180 :=
      @gA1i
        (synWb (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
          (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k)))))
        (.classEq (.cv y) (synCuni (.cv q))) p2079
    have p2181 := @gEleq1 (.cv y) (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))
    have p2182 :=
      @gAnbi12d (.classEq (.cv y) (synCuni (.cv q)))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv p)) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv y) (synChwcn (synCrn (.cv k))))
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k)))) p2180 p2181
    have p2183 :=
      @gBreq2 (.cv y) (synCuni (.cv q)) (synCuni (.cv p))
        (synChwniso (synCrn (.cv k)))
    have p2185 :=
      @gImbi12d (.classEq (.cv y) (synCuni (.cv q)))
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (.cv y))
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (synCuni (.cv q)))
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (.cv y))
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))) p2183
        p0684
    have p2186 :=
      @gImbi12d (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0487 syntaxFormula0468
        syntaxFormula0488 syntaxFormula0492 p2182 p2185
    have p2187 :=
      @gImbi2d (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0489 syntaxFormula0493
        (.classMem (synCuni (.cv p)) (synCvv)) p2186
    have p2188 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0491
        (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0494 p2178 p2187
    have p2189 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0495 y
        dv_cache_0108 p2188
    have p2192 := @gNfv syntaxFormula0493 y dv_cache_0166
    have p2193 :=
      @gNfim (.classMem (synCuni (.cv p)) (synCvv)) syntaxFormula0493 y p0691 p2192
    have p2194 :=
      @gN1923 (.classEq (.cv y) (synCuni (.cv q))) syntaxFormula0494 y p2193
    have p2195 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all y syntaxFormula0495)
        (.imp (synWex y (.classEq (.cv y) (synCuni (.cv q)))) syntaxFormula0494) p2189
        p2194
    have p2196 :=
      @gSyl5bi (.classMem (synCuni (.cv q)) (synCvv))
        (synWex y (.classEq (.cv y) (synCuni (.cv q))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0494 p0628 p2195
    have p2198 := @gA1ii syntaxFormula0497 syntaxFormula0148 p2196 p0697
    have p2200 := @gA1ii syntaxFormula0497 syntaxFormula0141 p2198 p0677
    have p2201 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv q)) (synCvv)) (.classMem (synCuni (.cv p)) (synCvv))
        syntaxFormula0493 p2200
    have p2202 :=
      @gImp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv p)) (synCvv)) (.classMem (synCuni (.cv q)) (synCvv))
        syntaxFormula0493 p2201
    have p2203 :=
      @gSyl5 syntaxFormula0468 syntaxFormula0149
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0493 p2050 p2202
    have p2204 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0468
        syntaxFormula0492 p2203
    have p2205 :=
      @gSyl5 syntaxFormula0458 syntaxFormula0468
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0492 p2043 p2204
    have p2206 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        (synWbr (synCuni (.cv p)) (synChwniso (synCrn (.cv k))) (synCuni (.cv q)))
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))) p2109
        p2205
    have p2211 :=
      @gSseld (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synChwcn (synCrn (.cv k))) (synChwcn (synCun P Y)) (synCuni (.cv q)) p1618
    have p2212 :=
      @gSyl5 syntaxFormula0451
        (.classMem (synCuni (.cv q)) (synChwcn (synCrn (.cv k))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCuni (.cv q)) (synChwcn (synCun P Y))) p2002 p2211
    have p2213 :=
      @gJcad (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        (.classMem (synCuni (.cv p)) (synChwcn (synCun P Y)))
        (.classMem (synCuni (.cv q)) (synChwcn (synCun P Y))) p1945 p2212
    have p2214 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0150 syntaxFormula0448 p2213
    have p2216 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0150 syntaxFormula0152 p2214 p0715
    have p2218 :=
      @gSyl6ib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0152 syntaxFormula0153 p2216 p0717
    have p2220 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0153 syntaxFormula0154 p2218 p0719
    have p2222 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp syntaxFormula0458 syntaxFormula0154))
        (.imp (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q)))
          (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q))))
        p2220 p0721
    have p2223 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        (synWbr (synCuni (.cv p)) (synChwniso (synCun P Y)) (synCuni (.cv q)))
        syntaxFormula0151 p2206 p2222
    have p2225 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0151 syntaxFormula0156 p2223 p0724
    have p2227 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0156 syntaxFormula0157 p2225 p0726
    have p2228 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0114 syntaxFormula0155 p1953 p2227
    have p2233 :=
      @gFveq2d syntaxFormula0451 (.cv q) (synCsn (synCuni (.cv q)))
        (synChnqmap1 (synCun P Y)) p1997
    have p2235 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        (.classMem (synCuni (.cv q)) (synChwcn (synCun P Y))) syntaxFormula0158 p2212
        p0734
    have p2237 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0158 syntaxFormula0161 p2235 p0736
    have p2239 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0161 syntaxFormula0162 p2237 p0738
    have p2240 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0159 syntaxFormula0160 p2233 p2239
    have p2241 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0160 syntaxFormula0448 p2240
    have p2243 :=
      @gSyl6ib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0160 syntaxFormula0163 p2241 p0742
    have p2245 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0163 syntaxFormula0165 p2243 p0744
    have p2247 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0165 syntaxFormula0166 p2245 p0746
    have p2248 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0155 syntaxFormula0164 p2228 p2247
    have p2249 :=
      @gExp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0448 syntaxFormula0164 p2248
    have p2250 :=
      @gSyld (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0451 (.imp syntaxFormula0448 syntaxFormula0164) p1934 p2249
    have p2251 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0448 syntaxFormula0164 p1904 p2250
    have p2253 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0164 syntaxFormula0168 p2251 p0752
    have p2255 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0168 syntaxFormula0169 p2253 p0754
    have p2256 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0447
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv p)))
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q))) p1877 p2255
    have p2258 :=
      @gSimpr (synWbr (.cv x) (synCcnv (synChnqmap1 (synCrn (.cv k)))) (.cv q))
        (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z))
    have p2259 :=
      @gSyl syntaxFormula0447 syntaxFormula0444
        (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z)) p1890 p2258
    have p2265 :=
      @gSyl syntaxFormula0447 (synWbr (.cv q) (synChnqmap1 (synCun P Y)) (.cv z))
        (.classEq (synCfv (synChnqmap1 (synCun P Y)) (.cv q)) (.cv z)) p2259 p0764
    have p2266 :=
      @gEqeq2d syntaxFormula0447 (synCfv (synChnqmap1 (synCun P Y)) (.cv q)) (.cv z)
        (.cv y) p2265
    have p2267 :=
      @gMpbidi syntaxFormula0447
        (.classEq (.cv y) (synCfv (synChnqmap1 (synCun P Y)) (.cv q)))
        (.classEq (.cv y) (.cv z)) (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p2256
        p2266
    have p2268 :=
      @gExp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0446
        syntaxFormula0444 (.classEq (.cv y) (.cv z)) p2267
    have p2269 :=
      @gAlimdv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0446
        syntaxFormula0498 q dv_cache_0096 p2268
    have p2270 :=
      @gSyl5 syntaxFormula0446 (.all q syntaxFormula0446)
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0499 p1865 p2269
    have p2271 := @gExim syntaxFormula0444 (.classEq (.cv y) (.cv z)) q
    have p2272 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0446
        syntaxFormula0499 (.imp syntaxFormula0445 (synWex q (.classEq (.cv y) (.cv z))))
        p2270 p2271
    have p2274 :=
      @gSyl8 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0446
        syntaxFormula0445 (synWex q (.classEq (.cv y) (.cv z)))
        (.classEq (.cv y) (.cv z)) p2272 p0773
    have p2275 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0446
        syntaxFormula0445 (.classEq (.cv y) (.cv z)) p1864 p2274
    have p2276 :=
      @gExp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0441
        syntaxFormula0442 (.classEq (.cv y) (.cv z)) p2275
    have p2277 :=
      @gAlimdv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0441
        syntaxFormula0500 p dv_cache_0095 p2276
    have p2278 :=
      @gSyl5 syntaxFormula0441 (.all p syntaxFormula0441)
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0501 p1859 p2277
    have p2279 := @gExim syntaxFormula0442 (.classEq (.cv y) (.cv z)) p
    have p2280 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0441
        syntaxFormula0501 (.imp syntaxFormula0443 (synWex p (.classEq (.cv y) (.cv z))))
        p2278 p2279
    have p2282 :=
      @gSyl8 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0441
        syntaxFormula0443 (synWex p (.classEq (.cv y) (.cv z)))
        (.classEq (.cv y) (.cv z)) p2280 p0781
    have p2283 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0441
        syntaxFormula0443 (.classEq (.cv y) (.cv z)) p1858 p2282
    have p2284 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0502 z
        dv_cache_0107 p2283
    have p2285 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0503 y
        dv_cache_0108 p2284
    have p2286 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0504 x
        dv_cache_0089 p2285
    have p2287 :=
      @gDffun2 x y z syntaxClass0436 dv_cache_0167 dv_cache_0168 dv_cache_0169
        dv_cache_0007 dv_cache_0069 dv_cache_0070
    have p2288_e01_recanon :
      Nominal.NPrf (synWb (synWfun syntaxClass0436) syntaxFormula0505) :=
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
        p2287
    have p2288 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0505
        (synWfun syntaxClass0436) p2286 p2288_e01_recanon
    have p2290 := @gFuneq (synChnqinc (synCrn (.cv k)) (synCun P Y)) syntaxClass0436
    have p2291 := Nominal.mp p1853 p2290
    have p2292 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfun syntaxClass0436)
        (synWfun (synChnqinc (synCrn (.cv k)) (synCun P Y))) p2288 p2291
    have p2294 :=
      @gDmeqi (synChnqinc (synCrn (.cv k)) (synCun P Y)) syntaxClass0436 p1853
    have p2295 := @gPw1ss (synChwcn (synCrn (.cv k))) (synChwcn (synCun P Y))
    have p2296 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWss (synChwcn (synCrn (.cv k))) (synChwcn (synCun P Y)))
        (synWss (synCpw1 (synChwcn (synCrn (.cv k)))) (synCpw1 (synChwcn (synCun P Y))))
        p1618 p2295
    have p2297 := (Nominal.classEqRefl (synCdm (synChnqmap1 (synCrn (.cv k)))))
    have p2298 :=
      @gEqcomi (synCdm (synChnqmap1 (synCrn (.cv k))))
        (synCrn (synCcnv (synChnqmap1 (synCrn (.cv k))))) p2297
    have p2299 :=
      @gSyl5eq (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synCrn (synCcnv (synChnqmap1 (synCrn (.cv k)))))
        (synCdm (synChnqmap1 (synCrn (.cv k))))
        (synCpw1 (synChwcn (synCrn (.cv k)))) p2298 p1915
    have p2303 :=
      @gSseq12 (synCrn (synCcnv (synChnqmap1 (synCrn (.cv k)))))
        (synCpw1 (synChwcn (synCrn (.cv k)))) (synCdm (synChnqmap1 (synCun P Y)))
        (synCpw1 (synChwcn (synCun P Y)))
    have p2304 :=
      @gSylancl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (synCrn (synCcnv (synChnqmap1 (synCrn (.cv k)))))
          (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classEq (synCdm (synChnqmap1 (synCun P Y))) (synCpw1 (synChwcn (synCun P Y))))
        (synWb syntaxFormula0506 (synWss (synCpw1 (synChwcn (synCrn (.cv k))))
            (synCpw1 (synChwcn (synCun P Y)))))
        p2299 p0805 p2303
    have p2305 :=
      @gMpbird (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0506
        (synWss (synCpw1 (synChwcn (synCrn (.cv k)))) (synCpw1 (synChwcn (synCun P Y))))
        p2296 p2304
    have p2306 :=
      @gDmcosseq (synChnqmap1 (synCun P Y)) (synCcnv (synChnqmap1 (synCrn (.cv k))))
    have p2307 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0506
        (.classEq syntaxClass0507 (synCdm (synCcnv (synChnqmap1 (synCrn (.cv k))))))
        p2305 p2306
    have p2308 := @gDfrn4 (synChnqmap1 (synCrn (.cv k)))
    have p2309 :=
      @gSyl6eqr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxClass0507
        (synCdm (synCcnv (synChnqmap1 (synCrn (.cv k)))))
        (synCrn (synChnqmap1 (synCrn (.cv k)))) p2307 p2308
    have p2310 :=
      @gElpw1 a (.cv q) (synChwcn (synCrn (.cv k))) dv_cache_0109 dv_cache_0022
    have p2311 := @gId (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
    have p2312 :=
      @gA1d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synChwniso (synCrn (.cv k))) (synCvv))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) p1664
    have p2313 :=
      @gEcelqsg (synChwcn (synCrn (.cv k))) (.cv a) (synChwniso (synCrn (.cv k)))
        (synCvv)
    have p2314 :=
      @gEx (.classMem (synChwniso (synCrn (.cv k))) (synCvv))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0508 p2313
    exact continuation p2292 p2294 p2309 p2310 p2311 p2312 p2314

end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `ReplaySupport.CodeCover8`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_cfbhnqinjcodecoverddndv_stage8`. -/
@[expose]
noncomputable def gCfbhnqinjcodecoverddndvStage8 (u : Var) (P : Class) (k : Var)
    (Y : Class) (hyp_cfbhnqinjcodecoverddndv_2 : Nominal.NPrf (.classMem Y (synCvv)))
    (p0286 : _) (p0340 : _) (p0346 : _) (p0348 : _) (p0824 : _) (p1642 : _) (p1643 : _)
    (p1645 : _) (p1649 : _) (p1789 : _) (p1790 : _) (p1793 : _) (p1802 : _) (p1813 : _)
    (p1841 : _) (p1843 : _) (p1844 : _) (p1847 : _) (p1855 : _) (p2292 : _) (p2294 : _)
    (p2309 : _) (p2310 : _) (p2311 : _) (p2312 : _) (p2314 : _) {Result : Type}
    (continuation : _ → Result) :=
  show Result from
    by
    let proofSupport : Finset Var :=
      ({ u } : Finset Var) ∪ P.fv ∪ ({ k } : Finset Var) ∪ Y.fv
    let x : Var := freshVar proofSupport 2
    let a : Var := freshVar proofSupport 4
    let z : Var := freshVar proofSupport 5
    let q : Var := freshVar proofSupport 7
    let h : Var := freshVar proofSupport 8
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
    have dv_cache_0114 : a ∉ ((Class.cv z)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_z, not_false_eq_true])
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
    have dv_cache_0122 : q ≠ z := by exact (show q ≠ z from (by exact fresh_q_ne_z))
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
    have dv_cache_0170 :
      a ∉
        ((Wff.classMem (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
            (synChnord (synCrn (.cv k))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_q, fresh_a_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0171 : q ∉ ((synCpw1 (synChwcn (synCrn (.cv k))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_k,
            not_false_eq_true])
    have dv_cache_0172 : q ∉ ((synChnord (synCrn (.cv k)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_k,
            not_false_eq_true])
    have dv_cache_0173 : q ∉ ((synChnqmap1 (synCrn (.cv k)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_q_ne_k,
            not_false_eq_true])
    have dv_cache_0174 : a ∉ ((synChwniso (synCrn (.cv k)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_k,
            not_false_eq_true])
    have dv_cache_0175 :
      q ∉
        ((Wff.classEq (.cv z)
            (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
            Finset.mem_singleton, fresh_q_ne_z, fresh_q_ne_a, fresh_q_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0176 :
      a ∉
        ((synWrex q (synCpw1 (synChwcn (synCrn (.cv k))))
            (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            Finset.mem_union, Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_k,
            fresh_a_ne_z, fresh_a_ne_q, or_false, and_false, not_false_eq_true])
    have dv_cache_0177 : z ∉ ((synCpw1 (synChwcn (synCrn (.cv k))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwcn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_k,
            not_false_eq_true])
    have dv_cache_0178 : z ∉ ((synChnord (synCrn (.cv k)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_k,
            not_false_eq_true])
    have dv_cache_0179 : z ∉ ((synChnqmap1 (synCrn (.cv k)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_k,
            not_false_eq_true])
    have dv_cache_0180 :
      a ∉
        ((Wff.imp (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u))
              (synChwcn (synCrn (.cv k)))) (.classMem
              (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u))
                (synChwniso (synCrn (.cv k)))) (synChnord (synCrn (.cv k)))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cec,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnord, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_u, fresh_a_ne_k, or_false,
            not_false_eq_true])
    have dv_cache_0181 :
      x ∉
        ((synWa (synWbr (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
              (synCcnv (synChnqmap1 Y))
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_ne_k, fresh_x_not_Y,
            fresh_x_not_P, or_false, not_false_eq_true])
    have dv_cache_0182 :
      x ∉ ((synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))).fv :=
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
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_u, fresh_x_ne_k, fresh_x_not_Y, or_false,
            not_false_eq_true])
    have dv_cache_0183 : x ∉ ((synCcnv (synChnqmap1 Y))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chnqmap1, fresh_x_not_Y,
            not_false_eq_true])
    let syntaxFormula0060 : Wff :=
      (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn (synCrn (.cv k))))
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
    let syntaxClass0190 : Class :=
      (synCfv (synChnqinc (synCfv (synC2nd) (.cv u)) (synCun P Y))
        (synCec (.cv u) (synChwniso (synCfv (synC2nd) (.cv u)))))
    let syntaxFormula0193 : Wff :=
      (.classEq (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
        syntaxClass0190)
    let syntaxClass0360 : Class :=
      (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso (synCun P Y)))
    let syntaxFormula0365 : Wff := (.classEq syntaxClass0190 syntaxClass0360)
    let syntaxFormula0411 : Wff :=
      (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
    let syntaxClass0414 : Class :=
      (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso (synCrn (.cv k))))
    let syntaxFormula0419 : Wff :=
      (synWfn (synChnqmap1 (synCrn (.cv k))) (synCpw1 (synChwcn (synCrn (.cv k)))))
    let syntaxFormula0429 : Wff :=
      (synWbr (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synChnqmap1 (synCun P Y)) syntaxClass0360)
    let syntaxFormula0432 : Wff :=
      (synWbr (.cv x) (synChnqmap1 (synCun P Y)) syntaxClass0360)
    let syntaxClass0436 : Class :=
      (synCcom (synChnqmap1 (synCun P Y)) (synCcnv (synChnqmap1 (synCrn (.cv k)))))
    let syntaxFormula0438 : Wff :=
      (synWbr syntaxClass0414 (synChnqinc (synCrn (.cv k)) (synCun P Y)) syntaxClass0360)
    let syntaxClass0507 : Class := (synCdm syntaxClass0436)
    let syntaxFormula0508 : Wff :=
      (.classMem (synCec (.cv a) (synChwniso (synCrn (.cv k))))
        (synCqs (synChwcn (synCrn (.cv k))) (synChwniso (synCrn (.cv k)))))
    let syntaxFormula0509 : Wff :=
      (.classMem (synCec (.cv a) (synChwniso (synCrn (.cv k))))
        (synChnord (synCrn (.cv k))))
    let syntaxFormula0510 : Wff :=
      (.classMem (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synChnord (synCrn (.cv k))))
    let syntaxFormula0511 : Wff := (synWb syntaxFormula0510 syntaxFormula0509)
    let syntaxFormula0512 : Wff := (synWb syntaxFormula0509 syntaxFormula0510)
    let syntaxFormula0513 : Wff := (.imp syntaxFormula0509 syntaxFormula0510)
    let syntaxFormula0514 : Wff :=
      (synWa (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classEq (.cv q) (synCsn (.cv a))))
    let syntaxFormula0515 : Wff :=
      (.classMem (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
        (synChnord (synCrn (.cv k))))
    let syntaxFormula0516 : Wff :=
      (synWf (synChnqmap1 (synCrn (.cv k))) (synCpw1 (synChwcn (synCrn (.cv k))))
        (synChnord (synCrn (.cv k))))
    let syntaxFormula0517 : Wff :=
      (synWa (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k))))))
    let syntaxFormula0518 : Wff :=
      (synWa (.classMem (synCsn (.cv a)) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))))
    let syntaxFormula0519 : Wff :=
      (synWrex q (synCpw1 (synChwcn (synCrn (.cv k))))
        (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))))
    let syntaxFormula0520 : Wff :=
      (synWral z (synChnord (synCrn (.cv k))) syntaxFormula0519)
    let syntaxFormula0521 : Wff :=
      (synWfn (synChnqinc (synCrn (.cv k)) (synCun P Y)) (synChnord (synCrn (.cv k))))
    let syntaxFormula0522 : Wff :=
      (.classMem syntaxClass0414 (synChnord (synCrn (.cv k))))
    let syntaxFormula0523 : Wff := (.imp syntaxFormula0060 syntaxFormula0522)
    let syntaxFormula0524 : Wff :=
      (.imp (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) syntaxFormula0523)
    let syntaxFormula0525 : Wff := (synWa syntaxFormula0521 syntaxFormula0522)
    let syntaxClass0526 : Class :=
      (synCfv (synChnqinc (synCrn (.cv k)) (synCun P Y)) syntaxClass0414)
    let syntaxFormula0527 : Wff := (.classEq syntaxClass0526 syntaxClass0360)
    let syntaxFormula0528 : Wff := (synWb syntaxFormula0527 syntaxFormula0438)
    let syntaxFormula0529 : Wff := (synWb syntaxFormula0438 syntaxFormula0527)
    let syntaxFormula0530 : Wff := (.imp syntaxFormula0438 syntaxFormula0527)
    let syntaxFormula0531 : Wff := (.classEq syntaxClass0360 syntaxClass0526)
    let syntaxFormula0532 : Wff := (.classEq syntaxClass0190 syntaxClass0526)
    let syntaxFormula0533 : Wff := (synWb syntaxFormula0365 syntaxFormula0532)
    let syntaxFormula0534 : Wff :=
      (.classEq (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
        syntaxClass0526)
    let syntaxFormula0535 : Wff := (synWb syntaxFormula0193 syntaxFormula0534)
    let syntaxClass0536 : Class :=
      (synCfv (synChnqmap1 Y) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
    let syntaxFormula0537 : Wff :=
      (.classEq syntaxClass0536
        (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y)))
    let syntaxFormula0538 : Wff :=
      (.classMem (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synCpw1 (synChwcn Y)))
    let syntaxFormula0539 : Wff :=
      (synWa (synWfn (synChnqmap1 Y) (synCpw1 (synChwcn Y))) syntaxFormula0538)
    let syntaxFormula0540 : Wff :=
      (synWbr (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))) (synChnqmap1 Y)
        (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y)))
    let syntaxFormula0541 : Wff := (synWb syntaxFormula0537 syntaxFormula0540)
    let syntaxFormula0542 : Wff :=
      (synWbr (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        (synCcnv (synChnqmap1 Y)) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
    let syntaxFormula0543 : Wff :=
      (synWbr (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        (synCcnv (synChnqmap1 Y)) (.cv x))
    let syntaxFormula0544 : Wff := (synWa syntaxFormula0543 syntaxFormula0432)
    let syntaxFormula0545 : Wff := (synWa syntaxFormula0542 syntaxFormula0429)
    let syntaxFormula0546 : Wff := (synWex x syntaxFormula0544)
    let syntaxFormula0547 : Wff :=
      (synWbr (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        (synCcom (synChnqmap1 (synCun P Y)) (synCcnv (synChnqmap1 Y))) syntaxClass0360)
    let syntaxFormula0548 : Wff :=
      (synWbr (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        (synChnqinc Y (synCun P Y)) syntaxClass0360)
    let syntaxFormula0549 : Wff := (.classEq syntaxClass0069 syntaxClass0360)
    let syntaxFormula0550 : Wff := (synWb syntaxFormula0549 syntaxFormula0548)
    let syntaxFormula0551 : Wff := (synWb syntaxFormula0548 syntaxFormula0549)
    let syntaxFormula0552 : Wff := (.imp syntaxFormula0548 syntaxFormula0549)
    let syntaxFormula0553 : Wff := (.classEq syntaxClass0360 syntaxClass0069)
    let syntaxFormula0554 : Wff := (.classEq syntaxClass0526 syntaxClass0069)
    let syntaxFormula0555 : Wff := (synWb syntaxFormula0527 syntaxFormula0554)
    let syntaxFormula0556 : Wff :=
      (.classEq (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
        syntaxClass0069)
    let syntaxFormula0557 : Wff := (synWb syntaxFormula0534 syntaxFormula0556)
    let syntaxFormula0558 : Wff :=
      (.classMem (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
        (synCrn (synChnqinc Y (synCun P Y))))
    let syntaxFormula0559 : Wff := (synWb syntaxFormula0558 syntaxFormula0070)
    let syntaxFormula0560 : Wff := (synWb syntaxFormula0070 syntaxFormula0558)
    let syntaxFormula0561 : Wff := (.imp syntaxFormula0070 syntaxFormula0558)
    have p2315 :=
      @gSyl56 (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synChwniso (synCrn (.cv k))) (synCvv))
        (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0508) p2311
        p2312 p2314
    have p2316 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0508 p2315
    have p2317 := (Nominal.classEqRefl (synChnord (synCrn (.cv k))))
    have p2318 :=
      @gEleq2i (synChnord (synCrn (.cv k)))
        (synCqs (synChwcn (synCrn (.cv k))) (synChwniso (synCrn (.cv k))))
        (synCec (.cv a) (synChwniso (synCrn (.cv k)))) p2317
    have p2319 :=
      @gSyl6ibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0508
        syntaxFormula0509 p2316 p2318
    have p2320 :=
      @gEleq1 (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCrn (.cv k)))) (synChnord (synCrn (.cv k)))
    have p2321 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0411
        syntaxFormula0511 p1789 p2320
    have p2322 := @gBicom syntaxFormula0510 syntaxFormula0509
    have p2323 :=
      @gSyl6ib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0511
        syntaxFormula0512 p2321 p2322
    have p2324 := @gBi1 syntaxFormula0509 syntaxFormula0510
    have p2325 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0512
        syntaxFormula0513 p2323 p2324
    have p2326 := @gId syntaxFormula0509
    have p2327 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0513))
        (.imp syntaxFormula0509 syntaxFormula0509) p2325 p2326
    have p2328 :=
      @gMpdd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0509
        syntaxFormula0510 p2319 p2327
    have p2329 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0510
        (.classEq (.cv q) (synCsn (.cv a))) p2328
    have p2330 :=
      @gSimpr (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classEq (.cv q) (synCsn (.cv a)))
    have p2331 := @gFveq2 (.cv q) (synCsn (.cv a)) (synChnqmap1 (synCrn (.cv k)))
    have p2332 :=
      @gSyl syntaxFormula0514 (.classEq (.cv q) (synCsn (.cv a)))
        (.classEq (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
          (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))))
        p2330 p2331
    have p2333 :=
      @gEleq1d syntaxFormula0514 (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synChnord (synCrn (.cv k))) p2332
    have p2334 := @gBiimprd syntaxFormula0514 syntaxFormula0515 syntaxFormula0510 p2333
    have p2335 :=
      @gSylcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0514
        syntaxFormula0510 syntaxFormula0515 p2329 p2334
    have p2336 :=
      @gExp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classEq (.cv q) (synCsn (.cv a))) syntaxFormula0515 p2335
    have p2337 :=
      @gRexlimdv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (.cv q) (synCsn (.cv a))) syntaxFormula0515 a
        (synChwcn (synCrn (.cv k))) dv_cache_0170 dv_cache_0024 p2336
    have p2338 :=
      @gSyl5bi (.classMem (.cv q) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (synWrex a (synChwcn (synCrn (.cv k))) (.classEq (.cv q) (synCsn (.cv a))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0515 p2310 p2337
    have p2339 :=
      @gRalrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0515 q
        (synCpw1 (synChwcn (synCrn (.cv k)))) dv_cache_0096 p2338
    have p2340 :=
      @gJca (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0419
        (synWral q (synCpw1 (synChwcn (synCrn (.cv k)))) syntaxFormula0515) p1813
        p2339
    have p2341 :=
      @gFnfvrnss q (synCpw1 (synChwcn (synCrn (.cv k))))
        (synChnord (synCrn (.cv k))) (synChnqmap1 (synCrn (.cv k))) dv_cache_0171
        dv_cache_0172 dv_cache_0173
    have p2342 :=
      @gSyl (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa syntaxFormula0419
          (synWral q (synCpw1 (synChwcn (synCrn (.cv k)))) syntaxFormula0515))
        (synWss (synCrn (synChnqmap1 (synCrn (.cv k)))) (synChnord (synCrn (.cv k))))
        p2340 p2341
    have p2343 :=
      @gJca (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0419
        (synWss (synCrn (synChnqmap1 (synCrn (.cv k)))) (synChnord (synCrn (.cv k))))
        p1813 p2342
    have p2344 := (Nominal.biimpRefl syntaxFormula0516)
    have p2345 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa syntaxFormula0419 (synWss (synCrn (synChnqmap1 (synCrn (.cv k))))
            (synChnord (synCrn (.cv k)))))
        syntaxFormula0516 p2343 p2344
    have p2347 :=
      @gEleq2i (synChnord (synCrn (.cv k)))
        (synCqs (synChwcn (synCrn (.cv k))) (synChwniso (synCrn (.cv k)))) (.cv z)
        p2317
    have p2348 :=
      @gBiimpi (.classMem (.cv z) (synChnord (synCrn (.cv k))))
        (.classMem (.cv z)
          (synCqs (synChwcn (synCrn (.cv k))) (synChwniso (synCrn (.cv k)))))
        p2347
    have p2349 :=
      @gElqsi a (synChwcn (synCrn (.cv k))) (.cv z) (synChwniso (synCrn (.cv k)))
        dv_cache_0022 dv_cache_0114 dv_cache_0174
    have p2350 :=
      @gSyl (.classMem (.cv z) (synChnord (synCrn (.cv k))))
        (.classMem (.cv z)
          (synCqs (synChwcn (synCrn (.cv k))) (synChwniso (synCrn (.cv k)))))
        (synWrex a (synChwcn (synCrn (.cv k)))
          (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k))))))
        p2348 p2349
    have p2353 :=
      @gAdantr (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classMem (synCsn (.cv a)) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k))))) p1649
    have p2354 :=
      @gSimpr (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
    have p2355 :=
      @gAdantrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0411
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k))))) p1789
    have p2356 :=
      @gEqcom (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))
        (synCec (.cv a) (synChwniso (synCrn (.cv k))))
    have p2357 :=
      @gSyl6ib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0517
        syntaxFormula0411
        (.classEq (synCec (.cv a) (synChwniso (synCrn (.cv k))))
          (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))))
        p2355 p2356
    have p2358 :=
      @gEqeq2 (synCec (.cv a) (synChwniso (synCrn (.cv k))))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))) (.cv z)
    have p2359 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0517
        (.classEq (synCec (.cv a) (synChwniso (synCrn (.cv k))))
          (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))))
        (synWb (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
          (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))))
        p2357 p2358
    have p2360 :=
      @gBi1 (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
        (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))))
    have p2361 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0517
        (synWb (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
          (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))))
        (.imp (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
          (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))))
        p2359 p2360
    have p2362 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0517
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
        (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))))
        p2354 p2361
    have p2363 :=
      @g_pm3_2 (.classMem (synCsn (.cv a)) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))))
    have p2364 :=
      @gSyl9 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0517
        (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))))
        (.classMem (synCsn (.cv a)) (synCpw1 (synChwcn (synCrn (.cv k)))))
        syntaxFormula0518 p2362 p2363
    have p2365 :=
      @gSyl5 syntaxFormula0517
        (.classMem (synCsn (.cv a)) (synCpw1 (synChwcn (synCrn (.cv k)))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp syntaxFormula0517 syntaxFormula0518) p2353 p2364
    have p2366 :=
      @gPm243d (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0517
        syntaxFormula0518 p2365
    have p2368 :=
      @gEqeq2d (.classEq (.cv q) (synCsn (.cv a)))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q))
        (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a))) (.cv z) p2331
    have p2369 :=
      @gRspcev (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (.cv q)))
        (.classEq (.cv z) (synCfv (synChnqmap1 (synCrn (.cv k))) (synCsn (.cv a)))) q
        (synCsn (.cv a)) (synCpw1 (synChwcn (synCrn (.cv k)))) dv_cache_0116
        dv_cache_0171 dv_cache_0175 p2368
    have p2370 :=
      @gSyl6 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0517
        syntaxFormula0518 syntaxFormula0519 p2366 p2369
    have p2371 :=
      @gExp3a (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (.cv a) (synChwcn (synCrn (.cv k))))
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
        syntaxFormula0519 p2370
    have p2372 :=
      @gRexlimdv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k)))))
        syntaxFormula0519 a (synChwcn (synCrn (.cv k))) dv_cache_0176 dv_cache_0024
        p2371
    have p2373 :=
      @gSyl5 (.classMem (.cv z) (synChnord (synCrn (.cv k))))
        (synWrex a (synChwcn (synCrn (.cv k)))
          (.classEq (.cv z) (synCec (.cv a) (synChwniso (synCrn (.cv k))))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0519 p2350 p2372
    have p2374 :=
      @gRalrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0519 z
        (synChnord (synCrn (.cv k))) dv_cache_0107 p2373
    have p2375 :=
      @gJca (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0516
        syntaxFormula0520 p2345 p2374
    have p2376 :=
      @gDffo3 q z (synCpw1 (synChwcn (synCrn (.cv k)))) (synChnord (synCrn (.cv k)))
        (synChnqmap1 (synCrn (.cv k))) dv_cache_0171 dv_cache_0177 dv_cache_0172
        dv_cache_0178 dv_cache_0173 dv_cache_0179 dv_cache_0122
    have p2377 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa syntaxFormula0516 syntaxFormula0520)
        (synWfo (synChnqmap1 (synCrn (.cv k))) (synCpw1 (synChwcn (synCrn (.cv k))))
          (synChnord (synCrn (.cv k))))
        p2375 p2376
    have p2378 :=
      @gDffo2 (synCpw1 (synChwcn (synCrn (.cv k)))) (synChnord (synCrn (.cv k)))
        (synChnqmap1 (synCrn (.cv k)))
    have p2379 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfo (synChnqmap1 (synCrn (.cv k))) (synCpw1 (synChwcn (synCrn (.cv k))))
          (synChnord (synCrn (.cv k))))
        (synWa syntaxFormula0516 (.classEq (synCrn (synChnqmap1 (synCrn (.cv k))))
            (synChnord (synCrn (.cv k)))))
        p2377 p2378
    have p2380 :=
      @gSimprd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0516
        (.classEq (synCrn (synChnqmap1 (synCrn (.cv k)))) (synChnord (synCrn (.cv k))))
        p2379
    have p2381 :=
      @gEqtrd (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxClass0507
        (synCrn (synChnqmap1 (synCrn (.cv k)))) (synChnord (synCrn (.cv k))) p2309
        p2380
    have p2382 :=
      @gSyl5eq (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synCdm (synChnqinc (synCrn (.cv k)) (synCun P Y))) syntaxClass0507
        (synChnord (synCrn (.cv k))) p2294 p2381
    have p2383 :=
      @gJca (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfun (synChnqinc (synCrn (.cv k)) (synCun P Y)))
        (.classEq (synCdm (synChnqinc (synCrn (.cv k)) (synCun P Y)))
          (synChnord (synCrn (.cv k))))
        p2292 p2382
    have p2384 := (Nominal.biimpRefl syntaxFormula0521)
    have p2385 :=
      @gSylibr (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWa (synWfun (synChnqinc (synCrn (.cv k)) (synCun P Y)))
          (.classEq (synCdm (synChnqinc (synCrn (.cv k)) (synCun P Y)))
            (synChnord (synCrn (.cv k)))))
        syntaxFormula0521 p2383 p2384
    have p2391 :=
      @gEleq1d (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synCec (.cv a) (synChwniso (synCrn (.cv k)))) syntaxClass0414
        (synChnord (synCrn (.cv k))) p1793
    have p2392 :=
      @gImbi12d (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0060
        syntaxFormula0509 syntaxFormula0522 p1790 p2391
    have p2393 :=
      @gSyl5ibcom (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.imp (.classMem (.cv a) (synChwcn (synCrn (.cv k)))) syntaxFormula0509)
        (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))) syntaxFormula0523
        p2319 p2392
    have p2394 :=
      @gAlrimiv (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0524 a
        dv_cache_0024 p2393
    have p2395 := @gNfv syntaxFormula0523 a dv_cache_0180
    have p2396 :=
      @gN1923 (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        syntaxFormula0523 a p2395
    have p2397 :=
      @gSylib (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) (.all a syntaxFormula0524)
        (.imp (synWex a (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
          syntaxFormula0523)
        p2394 p2396
    have p2398 :=
      @gSyl5bi (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
        (synWex a (.classEq (.cv a) (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0523 p1645 p2397
    have p2400 :=
      @gA1ii
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
          (.imp (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
            syntaxFormula0523))
        (.imp (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
          (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv)))
        p2398 p1802
    have p2401 :=
      @gCom23 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
        syntaxFormula0060 syntaxFormula0522 p2400
    have p2402 :=
      @gMpdi (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0060
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synCvv))
        syntaxFormula0522 p1643 p2401
    have p2403 :=
      @gSylcom (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0060
        syntaxFormula0522 p0286 p2402
    have p2404 := @g_pm3_2 syntaxFormula0521 syntaxFormula0522
    have p2405 :=
      @gSyl9 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0522
        syntaxFormula0521 syntaxFormula0525 p2403 p2404
    have p2406 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0521
        (.classMem (.cv u) (synChwcn P))
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0525) p2385
        p2405
    have p2407 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0525 p2406
    have p2408 :=
      @gFnbrfvb (synChnord (synCrn (.cv k))) syntaxClass0414 syntaxClass0360
        (synChnqinc (synCrn (.cv k)) (synCun P Y))
    have p2409 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0525
        syntaxFormula0528 p2407 p2408
    have p2410 := @gBicom syntaxFormula0527 syntaxFormula0438
    have p2411 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0528
        syntaxFormula0529 p2409 p2410
    have p2412 := @gBi1 syntaxFormula0438 syntaxFormula0527
    have p2413 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0529
        syntaxFormula0530 p2411 p2412
    have p2414 := @gId syntaxFormula0438
    have p2415 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0530))
        (.imp syntaxFormula0438 syntaxFormula0438) p2413 p2414
    have p2416 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0438
        syntaxFormula0527 p1855 p2415
    have p2417 := @gEqcom syntaxClass0526 syntaxClass0360
    have p2418 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0527
        syntaxFormula0531 p2416 p2417
    have p2419 := @gEqeq2 syntaxClass0360 syntaxClass0526 syntaxClass0190
    have p2420 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0531
        syntaxFormula0533 p2418 p2419
    have p2421 := @gBi1 syntaxFormula0365 syntaxFormula0532
    have p2422 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0533
        (.imp syntaxFormula0365 syntaxFormula0532) p2420 p2421
    have p2423 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0365
        syntaxFormula0532 p1642 p2422
    have p2424 :=
      @gEqeq2 syntaxClass0190 syntaxClass0526
        (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
    have p2425 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0532
        syntaxFormula0535 p2423 p2424
    have p2426 := @gBi1 syntaxFormula0193 syntaxFormula0534
    have p2427 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0535
        (.imp syntaxFormula0193 syntaxFormula0534) p2425 p2426
    have p2428 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0193
        syntaxFormula0534 p0824 p2427
    have p2429 :=
      @gHnqmap1valcl Y (synCfv (synChncodetrnfn (.cv k)) (.cv u))
        hyp_cfbhnqinjcodecoverddndv_2
    have p2430 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn Y))
        syntaxFormula0537 p0340 p2429
    have p2431 := @gHnqmap1fn Y hyp_cfbhnqinjcodecoverddndv_2
    have p2432 :=
      @gA1i (synWfn (synChnqmap1 Y) (synCpw1 (synChwcn Y)))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) p2431
    have p2433 := @gSnelpw1 (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn Y)
    have p2434 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (.classMem (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwcn Y))
        syntaxFormula0538 p0340 p2433
    have p2435 :=
      @g_pm3_2 (synWfn (synChnqmap1 Y) (synCpw1 (synChwcn Y))) syntaxFormula0538
    have p2436 :=
      @gSyl9 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0538
        (synWfn (synChnqmap1 Y) (synCpw1 (synChwcn Y))) syntaxFormula0539 p2434 p2435
    have p2437 :=
      @gSyl5 (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y)
        (synWfn (synChnqmap1 Y) (synCpw1 (synChwcn Y)))
        (.classMem (.cv u) (synChwcn P))
        (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0539) p2432
        p2436
    have p2438 :=
      @gPm243d (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0539 p2437
    have p2439 :=
      @gFnbrfvb (synCpw1 (synChwcn Y))
        (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        (synChnqmap1 Y)
    have p2440 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0539
        syntaxFormula0541 p2438 p2439
    have p2441 := @gBi1 syntaxFormula0537 syntaxFormula0540
    have p2442 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0541
        (.imp syntaxFormula0537 syntaxFormula0540) p2440 p2441
    have p2443 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0537
        syntaxFormula0540 p2430 p2442
    have p2444 :=
      @gBrcnv (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))) (synChnqmap1 Y)
    have p2445 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0540
        syntaxFormula0542 p2443 p2444
    have p2446 :=
      @gJcad (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0542
        syntaxFormula0429 p2445 p1841
    have p2449 :=
      @gBreq2d (.classEq (.cv x) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
        (.cv x) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u)))
        (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        (synCcnv (synChnqmap1 Y)) p1844
    have p2452 :=
      @gAnbi12d (.classEq (.cv x) (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))))
        syntaxFormula0543 syntaxFormula0542 syntaxFormula0432 syntaxFormula0429 p2449
        p1847
    have p2453 :=
      @gSpcev syntaxFormula0544 syntaxFormula0545 x
        (synCsn (synCfv (synChncodetrnfn (.cv k)) (.cv u))) dv_cache_0151 dv_cache_0181
        p1843 p2452
    have p2454 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0545
        syntaxFormula0546 p2446 p2453
    have p2455 :=
      @gBrco x (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        syntaxClass0360 (synChnqmap1 (synCun P Y)) (synCcnv (synChnqmap1 Y))
        dv_cache_0182 dv_cache_0154 dv_cache_0029 dv_cache_0183
    have p2456 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0546
        syntaxFormula0547 p2454 p2455
    have p2457 := (Nominal.classEqRefl (synChnqinc Y (synCun P Y)))
    have p2458 :=
      @gBreqi (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        syntaxClass0360 (synChnqinc Y (synCun P Y))
        (synCcom (synChnqmap1 (synCun P Y)) (synCcnv (synChnqmap1 Y))) p2457
    have p2459 :=
      @gSyl6ibr (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0547
        syntaxFormula0548 p2456 p2458
    have p2460 :=
      @gFnbrfvb (synChnord Y)
        (synCec (synCfv (synChncodetrnfn (.cv k)) (.cv u)) (synChwniso Y))
        syntaxClass0360 (synChnqinc Y (synCun P Y))
    have p2461 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0068
        syntaxFormula0550 p0346 p2460
    have p2462 := @gBicom syntaxFormula0549 syntaxFormula0548
    have p2463 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0550
        syntaxFormula0551 p2461 p2462
    have p2464 := @gBi1 syntaxFormula0548 syntaxFormula0549
    have p2465 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0551
        syntaxFormula0552 p2463 p2464
    have p2466 := @gId syntaxFormula0548
    have p2467 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0552))
        (.imp syntaxFormula0548 syntaxFormula0548) p2465 p2466
    have p2468 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0548
        syntaxFormula0549 p2459 p2467
    have p2469 := @gEqcom syntaxClass0069 syntaxClass0360
    have p2470 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0549
        syntaxFormula0553 p2468 p2469
    have p2471 := @gEqeq2 syntaxClass0360 syntaxClass0069 syntaxClass0526
    have p2472 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0553
        syntaxFormula0555 p2470 p2471
    have p2473 := @gBi1 syntaxFormula0527 syntaxFormula0554
    have p2474 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0555
        (.imp syntaxFormula0527 syntaxFormula0554) p2472 p2473
    have p2475 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0527
        syntaxFormula0554 p2416 p2474
    have p2476 :=
      @gEqeq2 syntaxClass0526 syntaxClass0069
        (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
    have p2477 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0554
        syntaxFormula0557 p2475 p2476
    have p2478 := @gBi1 syntaxFormula0534 syntaxFormula0556
    have p2479 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0557
        (.imp syntaxFormula0534 syntaxFormula0556) p2477 p2478
    have p2480 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0534
        syntaxFormula0556 p2428 p2479
    have p2481 :=
      @gEleq1 (synCfv (synChnqinc P (synCun P Y)) (synCec (.cv u) (synChwniso P)))
        syntaxClass0069 (synCrn (synChnqinc Y (synCun P Y)))
    have p2482 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0556
        syntaxFormula0559 p2480 p2481
    have p2483 := @gBicom syntaxFormula0558 syntaxFormula0070
    have p2484 :=
      @gSyl6ib (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0559
        syntaxFormula0560 p2482 p2483
    have p2485 := @gBi1 syntaxFormula0070 syntaxFormula0558
    have p2486 :=
      @gSyl6 (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0560
        syntaxFormula0561 p2484 p2485
    have p2487 := @gId syntaxFormula0070
    have p2488 :=
      @gA1ii
        (.imp (.classMem (.cv u) (synChwcn P))
          (.imp (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0561))
        (.imp syntaxFormula0070 syntaxFormula0070) p2486 p2487
    have p2489 :=
      @gMpdd (.classMem (.cv u) (synChwcn P))
        (synWf1 (.cv k) (synCfv (synC2nd) (.cv u)) Y) syntaxFormula0070
        syntaxFormula0558 p0348 p2488
    exact continuation p2489

end NFChoice.DirectNominalPrf.WPPReplay

end
