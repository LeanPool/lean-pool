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

@[expose]
noncomputable def g_cfbhnqinjcodecoverddndv_stage7 (u : Var) (P : Class) (k : Var)
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
    have dv_cache_0052 : h ≠ x := by exact (show h ≠ x from (by exact fresh_h_ne_x))
    have dv_cache_0053 : h ≠ y := by exact (show h ≠ y from (by exact fresh_h_ne_y))
    have dv_cache_0069 : x ≠ z := by exact (show x ≠ z from (by exact fresh_x_ne_z))
    have dv_cache_0070 : y ≠ z := by exact (show y ≠ z from (by exact fresh_y_ne_z))
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
    have dv_cache_0095 : p ∉ ((syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)).fv := by
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
    have dv_cache_0096 : q ∉ ((syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)).fv := by
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
    have dv_cache_0103 : v ∉ ((syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)).fv := by
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
    have dv_cache_0107 : z ∉ ((syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)).fv := by
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
    have dv_cache_0108 : y ∉ ((syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)).fv := by
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
        ((Wff.imp (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k)))) (.classEq
              (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (syn_cuni (.cv p))))
              (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))))).fv :=
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
        ((Wff.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))) (.classEq
              (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (syn_cuni (.cv q))))
              (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k))))))).fv :=
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
        ((Wff.imp (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
              (.classMem (.cv v) (syn_chwcn (syn_crn (.cv k))))) (syn_wb
              (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
                (syn_cec (.cv v) (syn_chwniso (syn_crn (.cv k)))))
              (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (.cv v))))).fv :=
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
        ((Wff.imp (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
              (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k))))) (syn_wb
              (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
                (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k)))))
              (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k)))
                (syn_cuni (.cv q)))))).fv :=
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
    have dv_cache_0164 : h ∉ ((syn_crn (.cv k))).fv := by
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
        ((Wff.imp (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
              (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k)))))
            (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (.cv y))
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_x_ne_p, fresh_x_ne_k, fresh_x_ne_y, fresh_x_not_P,
            fresh_x_not_Y, or_false, not_false_eq_true])
    have dv_cache_0166 :
      y ∉
        ((Wff.imp (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
              (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k))))) (.imp
              (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (syn_cuni (.cv q)))
              (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y))
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_chwniso,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
            Finset.mem_singleton, fresh_y_ne_p, fresh_y_ne_k, fresh_y_ne_q, fresh_y_not_P,
            fresh_y_not_Y, or_false, not_false_eq_true])
    have dv_cache_0167 :
      x ∉
        ((syn_ccom (syn_chnqmap1 (syn_cun P Y))
            (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))))).fv :=
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
        ((syn_ccom (syn_chnqmap1 (syn_cun P Y))
            (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))))).fv :=
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
        ((syn_ccom (syn_chnqmap1 (syn_cun P Y))
            (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))))).fv :=
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
      (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y))))
    let syntaxFormula0130 : Wff :=
      (syn_wa (.classMem (.cv x) (syn_chwcn (syn_cun P Y)))
        (.classMem (.cv y) (syn_chwcn (syn_cun P Y))))
    let syntaxFormula0131 : Wff :=
      (syn_wa (.classMem (.cv x) (syn_chwcodes (syn_cun P Y)))
        (.classMem (.cv y) (syn_chwcodes (syn_cun P Y))))
    let syntaxFormula0133 : Wff :=
      (syn_wiso (.cv h) (syn_cfv (syn_c1st) (.cv x)) (syn_cfv (syn_c1st) (.cv y))
        (syn_cfv (syn_c2nd) (.cv x)) (syn_cfv (syn_c2nd) (.cv y)))
    let syntaxFormula0134 : Wff := (syn_wex h syntaxFormula0133)
    let syntaxFormula0135 : Wff := (syn_wa syntaxFormula0131 syntaxFormula0134)
    let syntaxFormula0141 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv)))
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
    let syntaxFormula0168 : Wff :=
      (syn_wb (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p)))
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))))
    let syntaxFormula0169 : Wff :=
      (.imp (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p)))
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))))
    let syntaxFormula0411 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))
        (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))))
    let syntaxFormula0416 : Wff :=
      (.imp (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0411)
    let syntaxClass0436 : Class :=
      (syn_ccom (syn_chnqmap1 (syn_cun P Y)) (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))))
    let syntaxFormula0439 : Wff := (syn_wbr (.cv x) syntaxClass0436 (.cv y))
    let syntaxFormula0440 : Wff := (syn_wbr (.cv x) syntaxClass0436 (.cv z))
    let syntaxFormula0441 : Wff := (syn_wa syntaxFormula0439 syntaxFormula0440)
    let syntaxFormula0442 : Wff :=
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))) (.cv p))
        (syn_wbr (.cv p) (syn_chnqmap1 (syn_cun P Y)) (.cv y)))
    let syntaxFormula0443 : Wff := (syn_wex p syntaxFormula0442)
    let syntaxFormula0444 : Wff :=
      (syn_wa (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 (syn_cun P Y)) (.cv z)))
    let syntaxFormula0445 : Wff := (syn_wex q syntaxFormula0444)
    let syntaxFormula0446 : Wff := (syn_wa syntaxFormula0441 syntaxFormula0442)
    let syntaxFormula0447 : Wff := (syn_wa syntaxFormula0446 syntaxFormula0444)
    let syntaxFormula0448 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv p))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q)))
    let syntaxFormula0451 : Wff :=
      (syn_wa (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_crn (.cv k))))))
    let syntaxFormula0452 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (syn_cuni (.cv p))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k)))))
    let syntaxFormula0453 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0452)
    let syntaxFormula0454 : Wff :=
      (.imp (.classEq (.cv a) (syn_cuni (.cv p))) syntaxFormula0453)
    let syntaxFormula0455 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv p))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (syn_cuni (.cv p)))))
    let syntaxFormula0456 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv p))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k)))))
    let syntaxFormula0457 : Wff := (syn_wb syntaxFormula0455 syntaxFormula0456)
    let syntaxFormula0458 : Wff := (syn_wa syntaxFormula0451 syntaxFormula0448)
    let syntaxFormula0459 : Wff :=
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q)))
    let syntaxFormula0460 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (syn_cuni (.cv q))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k)))))
    let syntaxFormula0461 : Wff :=
      (.imp (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0460)
    let syntaxFormula0462 : Wff :=
      (.imp (.classEq (.cv a) (syn_cuni (.cv q))) syntaxFormula0461)
    let syntaxFormula0463 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (syn_cuni (.cv q)))))
    let syntaxFormula0464 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k)))))
    let syntaxFormula0465 : Wff := (syn_wb syntaxFormula0463 syntaxFormula0464)
    let syntaxFormula0466 : Wff :=
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k)))))
    let syntaxFormula0467 : Wff := (syn_wb syntaxFormula0459 syntaxFormula0466)
    let syntaxFormula0468 : Wff :=
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))))
    let syntaxFormula0469 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv v) (syn_chwcn (syn_crn (.cv k)))))
    let syntaxFormula0470 : Wff :=
      (syn_wa (.classMem (syn_crn (.cv k)) (syn_cvv)) syntaxFormula0469)
    let syntaxFormula0471 : Wff :=
      (.classEq (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (.cv v) (syn_chwniso (syn_crn (.cv k)))))
    let syntaxFormula0472 : Wff :=
      (syn_wb syntaxFormula0471 (syn_wbr (.cv a) (syn_chwniso (syn_crn (.cv k))) (.cv v)))
    let syntaxFormula0473 : Wff :=
      (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (.cv v) (syn_chwniso (syn_crn (.cv k)))))
    let syntaxFormula0474 : Wff :=
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv v) (syn_chwcn (syn_crn (.cv k)))))
    let syntaxFormula0475 : Wff :=
      (syn_wb syntaxFormula0473
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (.cv v)))
    let syntaxFormula0476 : Wff := (.imp syntaxFormula0474 syntaxFormula0475)
    let syntaxFormula0477 : Wff :=
      (.imp (.classEq (.cv a) (syn_cuni (.cv p))) syntaxFormula0476)
    let syntaxFormula0478 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0476)
    let syntaxFormula0479 : Wff :=
      (syn_wb syntaxFormula0466
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (syn_cuni (.cv q))))
    let syntaxFormula0480 : Wff := (.imp syntaxFormula0468 syntaxFormula0479)
    let syntaxFormula0481 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0480)
    let syntaxFormula0482 : Wff :=
      (.imp (.classEq (.cv v) (syn_cuni (.cv q))) syntaxFormula0481)
    let syntaxFormula0483 : Wff :=
      (.imp (.classMem (syn_cuni (.cv q)) (syn_cvv)) syntaxFormula0481)
    let syntaxFormula0484 : Wff :=
      (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0483)
    let syntaxFormula0485 : Wff :=
      (syn_wa (.classMem (.cv x) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k)))))
    let syntaxFormula0486 : Wff :=
      (syn_wa syntaxFormula0485 (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y)))
    let syntaxFormula0487 : Wff :=
      (syn_wa (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k)))))
    let syntaxFormula0488 : Wff :=
      (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (.cv y))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (.cv y)))
    let syntaxFormula0489 : Wff := (.imp syntaxFormula0487 syntaxFormula0488)
    let syntaxFormula0490 : Wff :=
      (.imp (.classEq (.cv x) (syn_cuni (.cv p))) syntaxFormula0489)
    let syntaxFormula0491 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0489)
    let syntaxFormula0492 : Wff :=
      (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (syn_cuni (.cv q)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q))))
    let syntaxFormula0493 : Wff := (.imp syntaxFormula0468 syntaxFormula0492)
    let syntaxFormula0494 : Wff :=
      (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0493)
    let syntaxFormula0495 : Wff :=
      (.imp (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0494)
    let syntaxFormula0496 : Wff :=
      (.imp (.classMem (syn_cuni (.cv q)) (syn_cvv)) syntaxFormula0494)
    let syntaxFormula0497 : Wff :=
      (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0496)
    let syntaxFormula0498 : Wff := (.imp syntaxFormula0444 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0499 : Wff := (.all q syntaxFormula0498)
    let syntaxFormula0500 : Wff := (.imp syntaxFormula0442 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0501 : Wff := (.all p syntaxFormula0500)
    let syntaxFormula0502 : Wff := (.imp syntaxFormula0441 (.classEq (.cv y) (.cv z)))
    let syntaxFormula0503 : Wff := (.all z syntaxFormula0502)
    let syntaxFormula0504 : Wff := (.all y syntaxFormula0503)
    let syntaxFormula0505 : Wff := (.all x syntaxFormula0504)
    let syntaxFormula0506 : Wff :=
      (syn_wss (syn_crn (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))))
        (syn_cdm (syn_chnqmap1 (syn_cun P Y))))
    let syntaxClass0507 : Class := (syn_cdm syntaxClass0436)
    let syntaxFormula0508 : Wff :=
      (.classMem (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
        (syn_cqs (syn_chwcn (syn_crn (.cv k))) (syn_chwniso (syn_crn (.cv k)))))
    have p1969 := @g_eceq1 (.cv a) (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k)))
    have p1970 :=
      @g_eqeq12d (.classEq (.cv a) (syn_cuni (.cv p)))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (syn_cuni (.cv p))))
        (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k)))) p1968 p1969
    have p1971 :=
      @g_imbi12d (.classEq (.cv a) (syn_cuni (.cv p)))
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0411
        syntaxFormula0452 p1966 p1970
    have p1972 :=
      @g_syl5ibcom (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0416
        (.classEq (.cv a) (syn_cuni (.cv p))) syntaxFormula0453 p1789 p1971
    have p1973 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0454 a
        dv_cache_0024 p1972
    have p1974 := @g_nfv syntaxFormula0453 a dv_cache_0160
    have p1975 :=
      @g_n_19_23 (.classEq (.cv a) (syn_cuni (.cv p))) syntaxFormula0453 a p1974
    have p1976 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.all a syntaxFormula0454)
        (.imp (syn_wex a (.classEq (.cv a) (syn_cuni (.cv p)))) syntaxFormula0453) p1973
        p1975
    have p1977 :=
      @g_syl5bi (.classMem (syn_cuni (.cv p)) (syn_cvv))
        (syn_wex a (.classEq (.cv a) (syn_cuni (.cv p))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0453 p1121 p1976
    have p1979 :=
      @g_a1ii
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
          (.imp (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0453))
        syntaxFormula0141 p1977 p0677
    have p1980 :=
      @g_com23 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cuni (.cv p)) (syn_cvv))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0452
        p1979
    have p1981 :=
      @g_mpdi (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0452 p1963 p1980
    have p1982 :=
      @g_syl5 syntaxFormula0451
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0452 p1943 p1981
    have p1983 :=
      @g_eqeq2 (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (syn_cuni (.cv p))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv p))
    have p1984 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0452 syntaxFormula0457 p1982 p1983
    have p1985 := @g_bi1 syntaxFormula0455 syntaxFormula0456
    have p1986 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0457 (.imp syntaxFormula0455 syntaxFormula0456) p1984 p1985
    have p1987 :=
      @g_mpdi (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0455 syntaxFormula0456 p1958 p1986
    have p1988 :=
      @g_adantrd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0456 syntaxFormula0448 p1987
    have p1989 :=
      @g_eqcom (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv p))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
    have p1990 :=
      @g_syl6ib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0456
        (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
          (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv p)))
        p1988 p1989
    have p1991 := @g_simpr syntaxFormula0451 syntaxFormula0448
    have p1992 :=
      @g_eqeq2d syntaxFormula0458 (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv p))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k)))) p1991
    have p1993 :=
      @g_mpbidi syntaxFormula0458
        (.classEq (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
          (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv p)))
        syntaxFormula0459 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) p1990 p1992
    have p1994 :=
      @g_simpr (.classMem (.cv p) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
    have p1995 := @g_hnwpw1argcl (syn_chwcn (syn_crn (.cv k))) q
    have p1996 :=
      @g_simprd (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k))))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p1995
    have p1997 :=
      @g_syl syntaxFormula0451
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p1994 p1996
    have p1998 :=
      @g_fveq2d syntaxFormula0451 (.cv q) (syn_csn (syn_cuni (.cv q)))
        (syn_chnqmap1 (syn_crn (.cv k))) p1997
    have p2001 :=
      @g_simpld (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k))))
        (.classEq (.cv q) (syn_csn (syn_cuni (.cv q)))) p1995
    have p2002 :=
      @g_syl syntaxFormula0451
        (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))) p1994 p2001
    have p2003 := @g_elex (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))
    have p2006 := @g_eleq1 (.cv a) (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))
    have p2008 :=
      @g_fveq2d (.classEq (.cv a) (syn_cuni (.cv q))) (syn_csn (.cv a))
        (syn_csn (syn_cuni (.cv q))) (syn_chnqmap1 (syn_crn (.cv k))) p1163
    have p2009 := @g_eceq1 (.cv a) (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k)))
    have p2010 :=
      @g_eqeq12d (.classEq (.cv a) (syn_cuni (.cv q)))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (syn_cuni (.cv q))))
        (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k)))) p2008 p2009
    have p2011 :=
      @g_imbi12d (.classEq (.cv a) (syn_cuni (.cv q)))
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0411
        syntaxFormula0460 p2006 p2010
    have p2012 :=
      @g_syl5ibcom (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0416
        (.classEq (.cv a) (syn_cuni (.cv q))) syntaxFormula0461 p1789 p2011
    have p2013 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0462 a
        dv_cache_0024 p2012
    have p2014 := @g_nfv syntaxFormula0461 a dv_cache_0161
    have p2015 :=
      @g_n_19_23 (.classEq (.cv a) (syn_cuni (.cv q))) syntaxFormula0461 a p2014
    have p2016 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.all a syntaxFormula0462)
        (.imp (syn_wex a (.classEq (.cv a) (syn_cuni (.cv q)))) syntaxFormula0461) p2013
        p2015
    have p2017 :=
      @g_syl5bi (.classMem (syn_cuni (.cv q)) (syn_cvv))
        (syn_wex a (.classEq (.cv a) (syn_cuni (.cv q))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0461 p1161 p2016
    have p2019 :=
      @g_a1ii
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
          (.imp (.classMem (syn_cuni (.cv q)) (syn_cvv)) syntaxFormula0461))
        syntaxFormula0148 p2017 p0697
    have p2020 :=
      @g_com23 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cuni (.cv q)) (syn_cvv))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0460
        p2019
    have p2021 :=
      @g_mpdi (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv q)) (syn_cvv)) syntaxFormula0460 p2003 p2020
    have p2022 :=
      @g_syl5 syntaxFormula0451
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0460 p2002 p2021
    have p2023 :=
      @g_eqeq2 (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (syn_cuni (.cv q))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k))))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))
    have p2024 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0460 syntaxFormula0465 p2022 p2023
    have p2025 := @g_bi1 syntaxFormula0463 syntaxFormula0464
    have p2026 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0465 (.imp syntaxFormula0463 syntaxFormula0464) p2024 p2025
    have p2027 :=
      @g_mpdi (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0463 syntaxFormula0464 p1998 p2026
    have p2028 :=
      @g_adantrd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0464 syntaxFormula0448 p2027
    have p2029 :=
      @g_eqeq2 (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
    have p2030 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0464 syntaxFormula0467 p2028 p2029
    have p2031 := @g_bi1 syntaxFormula0459 syntaxFormula0466
    have p2032 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0467 (.imp syntaxFormula0459 syntaxFormula0466) p2030 p2031
    have p2033 :=
      @g_mpdd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0459 syntaxFormula0466 p1993 p2032
    have p2042 :=
      @g_jca syntaxFormula0451
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))) p1943 p2002
    have p2043 := @g_adantr syntaxFormula0451 syntaxFormula0468 syntaxFormula0448 p2042
    have p2044 :=
      @g_simpl (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k))))
    have p2046 :=
      @g_syl syntaxFormula0468
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv p)) (syn_cvv)) p2044 p1963
    have p2047 :=
      @g_simpr (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k))))
    have p2049 :=
      @g_syl syntaxFormula0468
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv q)) (syn_cvv)) p2047 p2003
    have p2050 :=
      @g_jca syntaxFormula0468 (.classMem (syn_cuni (.cv p)) (syn_cvv))
        (.classMem (syn_cuni (.cv q)) (syn_cvv)) p2046 p2049
    have p2055 := @g_id syntaxFormula0469
    have p2056 :=
      @g_a1d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_crn (.cv k)) (syn_cvv)) syntaxFormula0469 p1662
    have p2057 := @g_pm3_2 (.classMem (syn_crn (.cv k)) (syn_cvv)) syntaxFormula0469
    have p2058 :=
      @g_syl56 syntaxFormula0469 syntaxFormula0469
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_crn (.cv k)) (syn_cvv)) (.imp syntaxFormula0469 syntaxFormula0470)
        p2055 p2056 p2057
    have p2059 :=
      @g_pm2_43d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0469
        syntaxFormula0470 p2058
    have p2060 := @g_hwnisoclasseqb v a (syn_crn (.cv k))
    have p2061 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0469
        syntaxFormula0470 syntaxFormula0472 p2059 p2060
    have p2063 := @g_biid (.classMem (.cv v) (syn_chwcn (syn_crn (.cv k))))
    have p2064 :=
      @g_a1i
        (syn_wb (.classMem (.cv v) (syn_chwcn (syn_crn (.cv k))))
          (.classMem (.cv v) (syn_chwcn (syn_crn (.cv k)))))
        (.classEq (.cv a) (syn_cuni (.cv p))) p2063
    have p2065 :=
      @g_anbi12d (.classEq (.cv a) (syn_cuni (.cv p)))
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv v) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv v) (syn_chwcn (syn_crn (.cv k)))) p1966 p2064
    have p2067 :=
      @g_eqeq1d (.classEq (.cv a) (syn_cuni (.cv p)))
        (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (.cv v) (syn_chwniso (syn_crn (.cv k)))) p1969
    have p2068 :=
      @g_breq1 (.cv a) (syn_cuni (.cv p)) (.cv v) (syn_chwniso (syn_crn (.cv k)))
    have p2069 :=
      @g_bibi12d (.classEq (.cv a) (syn_cuni (.cv p))) syntaxFormula0471 syntaxFormula0473
        (syn_wbr (.cv a) (syn_chwniso (syn_crn (.cv k))) (.cv v))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (.cv v)) p2067 p2068
    have p2070 :=
      @g_imbi12d (.classEq (.cv a) (syn_cuni (.cv p))) syntaxFormula0469 syntaxFormula0474
        syntaxFormula0472 syntaxFormula0475 p2065 p2069
    have p2071 :=
      @g_syl5ibcom (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.imp syntaxFormula0469 syntaxFormula0472) (.classEq (.cv a) (syn_cuni (.cv p)))
        syntaxFormula0476 p2061 p2070
    have p2072 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0477 a
        dv_cache_0024 p2071
    have p2073 := @g_nfv syntaxFormula0476 a dv_cache_0162
    have p2074 :=
      @g_n_19_23 (.classEq (.cv a) (syn_cuni (.cv p))) syntaxFormula0476 a p2073
    have p2075 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.all a syntaxFormula0477)
        (.imp (syn_wex a (.classEq (.cv a) (syn_cuni (.cv p)))) syntaxFormula0476) p2072
        p2074
    have p2076 :=
      @g_syl5bi (.classMem (syn_cuni (.cv p)) (syn_cvv))
        (syn_wex a (.classEq (.cv a) (syn_cuni (.cv p))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0476 p1121 p2075
    have p2078 :=
      @g_a1ii (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0478)
        syntaxFormula0141 p2076 p0677
    have p2079 := @g_biid (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
    have p2080 :=
      @g_a1i
        (syn_wb (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
          (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k)))))
        (.classEq (.cv v) (syn_cuni (.cv q))) p2079
    have p2081 := @g_eleq1 (.cv v) (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))
    have p2082 :=
      @g_anbi12d (.classEq (.cv v) (syn_cuni (.cv q)))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv v) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))) p2080 p2081
    have p2083 := @g_eceq1 (.cv v) (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k)))
    have p2084 :=
      @g_eqeq2d (.classEq (.cv v) (syn_cuni (.cv q)))
        (syn_cec (.cv v) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (syn_cuni (.cv q)) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k)))) p2083
    have p2085 :=
      @g_breq2 (.cv v) (syn_cuni (.cv q)) (syn_cuni (.cv p))
        (syn_chwniso (syn_crn (.cv k)))
    have p2086 :=
      @g_bibi12d (.classEq (.cv v) (syn_cuni (.cv q))) syntaxFormula0473 syntaxFormula0466
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (.cv v))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (syn_cuni (.cv q)))
        p2084 p2085
    have p2087 :=
      @g_imbi12d (.classEq (.cv v) (syn_cuni (.cv q))) syntaxFormula0474 syntaxFormula0468
        syntaxFormula0475 syntaxFormula0479 p2082 p2086
    have p2088 :=
      @g_imbi2d (.classEq (.cv v) (syn_cuni (.cv q))) syntaxFormula0476 syntaxFormula0480
        (.classMem (syn_cuni (.cv p)) (syn_cvv)) p2087
    have p2089 :=
      @g_syl5ibcom (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0478
        (.classEq (.cv v) (syn_cuni (.cv q))) syntaxFormula0481 p2078 p2088
    have p2090 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0482 v
        dv_cache_0103 p2089
    have p2093 := @g_nfv syntaxFormula0480 v dv_cache_0163
    have p2094 :=
      @g_nfim (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0480 v p1248 p2093
    have p2095 :=
      @g_n_19_23 (.classEq (.cv v) (syn_cuni (.cv q))) syntaxFormula0481 v p2094
    have p2096 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.all v syntaxFormula0482)
        (.imp (syn_wex v (.classEq (.cv v) (syn_cuni (.cv q)))) syntaxFormula0481) p2090
        p2095
    have p2097 :=
      @g_syl5bi (.classMem (syn_cuni (.cv q)) (syn_cvv))
        (syn_wex v (.classEq (.cv v) (syn_cuni (.cv q))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0481 p1208 p2096
    have p2099 := @g_a1ii syntaxFormula0484 syntaxFormula0148 p2097 p0697
    have p2101 := @g_a1ii syntaxFormula0484 syntaxFormula0141 p2099 p0677
    have p2102 :=
      @g_com23 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv))
        syntaxFormula0480 p2101
    have p2103 :=
      @g_imp3a (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cuni (.cv p)) (syn_cvv)) (.classMem (syn_cuni (.cv q)) (syn_cvv))
        syntaxFormula0480 p2102
    have p2104 :=
      @g_syl5 syntaxFormula0468 syntaxFormula0149
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0480 p2050 p2103
    have p2105 :=
      @g_pm2_43d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0468
        syntaxFormula0479 p2104
    have p2106 :=
      @g_syl5 syntaxFormula0458 syntaxFormula0468
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0479 p2043 p2105
    have p2107 :=
      @g_bi1 syntaxFormula0466
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (syn_cuni (.cv q)))
    have p2108 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0479
        (.imp syntaxFormula0466
          (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (syn_cuni (.cv q))))
        p2106 p2107
    have p2109 :=
      @g_mpdd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0466
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (syn_cuni (.cv q)))
        p2033 p2108
    have p2131 :=
      @g_simpl (.classMem (.cv x) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k))))
    have p2132 :=
      @g_sseld (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_chwcn (syn_crn (.cv k))) (syn_chwcn (syn_cun P Y)) (.cv x) p1618
    have p2133 :=
      @g_syl5 syntaxFormula0485 (.classMem (.cv x) (syn_chwcn (syn_crn (.cv k))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv x) (syn_chwcn (syn_cun P Y))) p2131 p2132
    have p2134 :=
      @g_simpr (.classMem (.cv x) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k))))
    have p2135 :=
      @g_sseld (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_chwcn (syn_crn (.cv k))) (syn_chwcn (syn_cun P Y)) (.cv y) p1618
    have p2136 :=
      @g_syl5 syntaxFormula0485 (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv y) (syn_chwcn (syn_cun P Y))) p2134 p2135
    have p2137 :=
      @g_jcad (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0485
        (.classMem (.cv x) (syn_chwcn (syn_cun P Y)))
        (.classMem (.cv y) (syn_chwcn (syn_cun P Y))) p2133 p2136
    have p2138 :=
      @g_adantrd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0485
        syntaxFormula0130 (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y)) p2137
    have p2140 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0485
        (.classMem (.cv x) (syn_chwcn (syn_cun P Y)))
        (.classMem (.cv x) (syn_chwcodes (syn_cun P Y))) p2133 p0639
    have p2142 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0485
        (.classMem (.cv y) (syn_chwcn (syn_cun P Y)))
        (.classMem (.cv y) (syn_chwcodes (syn_cun P Y))) p2136 p0641
    have p2143 :=
      @g_jcad (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0485
        (.classMem (.cv x) (syn_chwcodes (syn_cun P Y)))
        (.classMem (.cv y) (syn_chwcodes (syn_cun P Y))) p2140 p2142
    have p2144 :=
      @g_adantrd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0485
        syntaxFormula0131 (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y)) p2143
    have p2145 :=
      @g_simpr syntaxFormula0485 (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y))
    have p2146 := @g_hwnisohwisob y x (syn_crn (.cv k)) dv_cache_0007
    have p2147 :=
      @g_biimpi (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y))
        (syn_wa syntaxFormula0485 (syn_wbr (.cv x) (syn_chwiso (syn_crn (.cv k))) (.cv y)))
        p2146
    have p2148 :=
      @g_simprd (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y))
        syntaxFormula0485 (syn_wbr (.cv x) (syn_chwiso (syn_crn (.cv k))) (.cv y)) p2147
    have p2149 :=
      @g_syl syntaxFormula0486 (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y))
        (syn_wbr (.cv x) (syn_chwiso (syn_crn (.cv k))) (.cv y)) p2145 p2148
    have p2150 :=
      @g_brhwisoany y x (syn_crn (.cv k)) h dv_cache_0164 dv_cache_0052 dv_cache_0053
    have p2151 :=
      @g_sylib syntaxFormula0486 (syn_wbr (.cv x) (syn_chwiso (syn_crn (.cv k))) (.cv y))
        (syn_wa (syn_wa (.classMem (.cv x) (syn_chwcodes (syn_crn (.cv k))))
            (.classMem (.cv y) (syn_chwcodes (syn_crn (.cv k))))) syntaxFormula0134)
        p2149 p2150
    have p2152 :=
      @g_simprd syntaxFormula0486
        (syn_wa (.classMem (.cv x) (syn_chwcodes (syn_crn (.cv k))))
          (.classMem (.cv y) (syn_chwcodes (syn_crn (.cv k)))))
        syntaxFormula0134 p2151
    have p2154 :=
      @g_syl5 syntaxFormula0486 syntaxFormula0134 syntaxFormula0131 syntaxFormula0135
        p2152 p0653
    have p2155 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0486
        syntaxFormula0131 (.imp syntaxFormula0486 syntaxFormula0135) p2144 p2154
    have p2156 :=
      @g_pm2_43d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0486
        syntaxFormula0135 p2155
    have p2158 :=
      @g_syl6ibr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0486
        syntaxFormula0135 (syn_wbr (.cv x) (syn_chwiso (syn_cun P Y)) (.cv y)) p2156 p0657
    have p2159 :=
      @g_jcad (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0486
        syntaxFormula0130 (syn_wbr (.cv x) (syn_chwiso (syn_cun P Y)) (.cv y)) p2138 p2158
    have p2161 :=
      @g_syl6ibr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0486
        (syn_wa syntaxFormula0130 (syn_wbr (.cv x) (syn_chwiso (syn_cun P Y)) (.cv y)))
        (syn_wbr (.cv x) (syn_chwniso (syn_cun P Y)) (.cv y)) p2159 p0660
    have p2162 :=
      @g_exp3a (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0485
        (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y))
        (syn_wbr (.cv x) (syn_chwniso (syn_cun P Y)) (.cv y)) p2161
    have p2163 := @g_eleq1 (.cv x) (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k)))
    have p2164 := @g_biid (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k))))
    have p2165 :=
      @g_a1i
        (syn_wb (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k))))
          (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k)))))
        (.classEq (.cv x) (syn_cuni (.cv p))) p2164
    have p2166 :=
      @g_anbi12d (.classEq (.cv x) (syn_cuni (.cv p)))
        (.classMem (.cv x) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k)))) p2163 p2165
    have p2167 :=
      @g_breq1 (.cv x) (syn_cuni (.cv p)) (.cv y) (syn_chwniso (syn_crn (.cv k)))
    have p2169 :=
      @g_imbi12d (.classEq (.cv x) (syn_cuni (.cv p)))
        (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (.cv y))
        (syn_wbr (.cv x) (syn_chwniso (syn_cun P Y)) (.cv y))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (.cv y)) p2167 p0668
    have p2170 :=
      @g_imbi12d (.classEq (.cv x) (syn_cuni (.cv p))) syntaxFormula0485 syntaxFormula0487
        (.imp (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y))
          (syn_wbr (.cv x) (syn_chwniso (syn_cun P Y)) (.cv y)))
        syntaxFormula0488 p2166 p2169
    have p2171 :=
      @g_syl5ibcom (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.imp syntaxFormula0485 (.imp (syn_wbr (.cv x) (syn_chwniso (syn_crn (.cv k))) (.cv y))
            (syn_wbr (.cv x) (syn_chwniso (syn_cun P Y)) (.cv y))))
        (.classEq (.cv x) (syn_cuni (.cv p))) syntaxFormula0489 p2162 p2170
    have p2172 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0490 x
        dv_cache_0089 p2171
    have p2173 := @g_nfv syntaxFormula0489 x dv_cache_0165
    have p2174 :=
      @g_n_19_23 (.classEq (.cv x) (syn_cuni (.cv p))) syntaxFormula0489 x p2173
    have p2175 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.all x syntaxFormula0490)
        (.imp (syn_wex x (.classEq (.cv x) (syn_cuni (.cv p)))) syntaxFormula0489) p2172
        p2174
    have p2176 :=
      @g_syl5bi (.classMem (syn_cuni (.cv p)) (syn_cvv))
        (syn_wex x (.classEq (.cv x) (syn_cuni (.cv p))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0489 p0630 p2175
    have p2178 :=
      @g_a1ii (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0491)
        syntaxFormula0141 p2176 p0677
    have p2180 :=
      @g_a1i
        (syn_wb (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
          (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k)))))
        (.classEq (.cv y) (syn_cuni (.cv q))) p2079
    have p2181 := @g_eleq1 (.cv y) (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))
    have p2182 :=
      @g_anbi12d (.classEq (.cv y) (syn_cuni (.cv q)))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv y) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k)))) p2180 p2181
    have p2183 :=
      @g_breq2 (.cv y) (syn_cuni (.cv q)) (syn_cuni (.cv p))
        (syn_chwniso (syn_crn (.cv k)))
    have p2185 :=
      @g_imbi12d (.classEq (.cv y) (syn_cuni (.cv q)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (.cv y))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (syn_cuni (.cv q)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (.cv y))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q))) p2183
        p0684
    have p2186 :=
      @g_imbi12d (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0487 syntaxFormula0468
        syntaxFormula0488 syntaxFormula0492 p2182 p2185
    have p2187 :=
      @g_imbi2d (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0489 syntaxFormula0493
        (.classMem (syn_cuni (.cv p)) (syn_cvv)) p2186
    have p2188 :=
      @g_syl5ibcom (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0491
        (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0494 p2178 p2187
    have p2189 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0495 y
        dv_cache_0108 p2188
    have p2192 := @g_nfv syntaxFormula0493 y dv_cache_0166
    have p2193 :=
      @g_nfim (.classMem (syn_cuni (.cv p)) (syn_cvv)) syntaxFormula0493 y p0691 p2192
    have p2194 :=
      @g_n_19_23 (.classEq (.cv y) (syn_cuni (.cv q))) syntaxFormula0494 y p2193
    have p2195 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.all y syntaxFormula0495)
        (.imp (syn_wex y (.classEq (.cv y) (syn_cuni (.cv q)))) syntaxFormula0494) p2189
        p2194
    have p2196 :=
      @g_syl5bi (.classMem (syn_cuni (.cv q)) (syn_cvv))
        (syn_wex y (.classEq (.cv y) (syn_cuni (.cv q))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0494 p0628 p2195
    have p2198 := @g_a1ii syntaxFormula0497 syntaxFormula0148 p2196 p0697
    have p2200 := @g_a1ii syntaxFormula0497 syntaxFormula0141 p2198 p0677
    have p2201 :=
      @g_com23 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cuni (.cv q)) (syn_cvv)) (.classMem (syn_cuni (.cv p)) (syn_cvv))
        syntaxFormula0493 p2200
    have p2202 :=
      @g_imp3a (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cuni (.cv p)) (syn_cvv)) (.classMem (syn_cuni (.cv q)) (syn_cvv))
        syntaxFormula0493 p2201
    have p2203 :=
      @g_syl5 syntaxFormula0468 syntaxFormula0149
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0493 p2050 p2202
    have p2204 :=
      @g_pm2_43d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0468
        syntaxFormula0492 p2203
    have p2205 :=
      @g_syl5 syntaxFormula0458 syntaxFormula0468
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0492 p2043 p2204
    have p2206 :=
      @g_mpdd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_crn (.cv k))) (syn_cuni (.cv q)))
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q))) p2109
        p2205
    have p2211 :=
      @g_sseld (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_chwcn (syn_crn (.cv k))) (syn_chwcn (syn_cun P Y)) (syn_cuni (.cv q)) p1618
    have p2212 :=
      @g_syl5 syntaxFormula0451
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_crn (.cv k))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cun P Y))) p2002 p2211
    have p2213 :=
      @g_jcad (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        (.classMem (syn_cuni (.cv p)) (syn_chwcn (syn_cun P Y)))
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cun P Y))) p1945 p2212
    have p2214 :=
      @g_adantrd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0150 syntaxFormula0448 p2213
    have p2216 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0150 syntaxFormula0152 p2214 p0715
    have p2218 :=
      @g_syl6ib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0152 syntaxFormula0153 p2216 p0717
    have p2220 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0153 syntaxFormula0154 p2218 p0719
    have p2222 :=
      @g_a1ii
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
          (.imp syntaxFormula0458 syntaxFormula0154))
        (.imp (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q)))
          (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q))))
        p2220 p0721
    have p2223 :=
      @g_mpdd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        (syn_wbr (syn_cuni (.cv p)) (syn_chwniso (syn_cun P Y)) (syn_cuni (.cv q)))
        syntaxFormula0151 p2206 p2222
    have p2225 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0151 syntaxFormula0156 p2223 p0724
    have p2227 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0156 syntaxFormula0157 p2225 p0726
    have p2228 :=
      @g_mpdd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0114 syntaxFormula0155 p1953 p2227
    have p2233 :=
      @g_fveq2d syntaxFormula0451 (.cv q) (syn_csn (syn_cuni (.cv q)))
        (syn_chnqmap1 (syn_cun P Y)) p1997
    have p2235 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        (.classMem (syn_cuni (.cv q)) (syn_chwcn (syn_cun P Y))) syntaxFormula0158 p2212
        p0734
    have p2237 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0158 syntaxFormula0161 p2235 p0736
    have p2239 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0161 syntaxFormula0162 p2237 p0738
    have p2240 :=
      @g_mpdi (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0159 syntaxFormula0160 p2233 p2239
    have p2241 :=
      @g_adantrd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0160 syntaxFormula0448 p2240
    have p2243 :=
      @g_syl6ib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0160 syntaxFormula0163 p2241 p0742
    have p2245 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0163 syntaxFormula0165 p2243 p0744
    have p2247 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0165 syntaxFormula0166 p2245 p0746
    have p2248 :=
      @g_mpdd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0458
        syntaxFormula0155 syntaxFormula0164 p2228 p2247
    have p2249 :=
      @g_exp3a (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0451
        syntaxFormula0448 syntaxFormula0164 p2248
    have p2250 :=
      @g_syld (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0451 (.imp syntaxFormula0448 syntaxFormula0164) p1934 p2249
    have p2251 :=
      @g_mpdd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0448 syntaxFormula0164 p1904 p2250
    have p2253 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0164 syntaxFormula0168 p2251 p0752
    have p2255 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0447
        syntaxFormula0168 syntaxFormula0169 p2253 p0754
    have p2256 :=
      @g_mpdi (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0447
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv p)))
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q))) p1877 p2255
    have p2258 :=
      @g_simpr (syn_wbr (.cv x) (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))) (.cv q))
        (syn_wbr (.cv q) (syn_chnqmap1 (syn_cun P Y)) (.cv z))
    have p2259 :=
      @g_syl syntaxFormula0447 syntaxFormula0444
        (syn_wbr (.cv q) (syn_chnqmap1 (syn_cun P Y)) (.cv z)) p1890 p2258
    have p2265 :=
      @g_syl syntaxFormula0447 (syn_wbr (.cv q) (syn_chnqmap1 (syn_cun P Y)) (.cv z))
        (.classEq (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q)) (.cv z)) p2259 p0764
    have p2266 :=
      @g_eqeq2d syntaxFormula0447 (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q)) (.cv z)
        (.cv y) p2265
    have p2267 :=
      @g_mpbidi syntaxFormula0447
        (.classEq (.cv y) (syn_cfv (syn_chnqmap1 (syn_cun P Y)) (.cv q)))
        (.classEq (.cv y) (.cv z)) (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) p2256
        p2266
    have p2268 :=
      @g_exp3a (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0446
        syntaxFormula0444 (.classEq (.cv y) (.cv z)) p2267
    have p2269 :=
      @g_alimdv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0446
        syntaxFormula0498 q dv_cache_0096 p2268
    have p2270 :=
      @g_syl5 syntaxFormula0446 (.all q syntaxFormula0446)
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0499 p1865 p2269
    have p2271 := @g_exim syntaxFormula0444 (.classEq (.cv y) (.cv z)) q
    have p2272 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0446
        syntaxFormula0499 (.imp syntaxFormula0445 (syn_wex q (.classEq (.cv y) (.cv z))))
        p2270 p2271
    have p2274 :=
      @g_syl8 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0446
        syntaxFormula0445 (syn_wex q (.classEq (.cv y) (.cv z)))
        (.classEq (.cv y) (.cv z)) p2272 p0773
    have p2275 :=
      @g_mpdi (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0446
        syntaxFormula0445 (.classEq (.cv y) (.cv z)) p1864 p2274
    have p2276 :=
      @g_exp3a (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0441
        syntaxFormula0442 (.classEq (.cv y) (.cv z)) p2275
    have p2277 :=
      @g_alimdv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0441
        syntaxFormula0500 p dv_cache_0095 p2276
    have p2278 :=
      @g_syl5 syntaxFormula0441 (.all p syntaxFormula0441)
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0501 p1859 p2277
    have p2279 := @g_exim syntaxFormula0442 (.classEq (.cv y) (.cv z)) p
    have p2280 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0441
        syntaxFormula0501 (.imp syntaxFormula0443 (syn_wex p (.classEq (.cv y) (.cv z))))
        p2278 p2279
    have p2282 :=
      @g_syl8 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0441
        syntaxFormula0443 (syn_wex p (.classEq (.cv y) (.cv z)))
        (.classEq (.cv y) (.cv z)) p2280 p0781
    have p2283 :=
      @g_mpdi (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0441
        syntaxFormula0443 (.classEq (.cv y) (.cv z)) p1858 p2282
    have p2284 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0502 z
        dv_cache_0107 p2283
    have p2285 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0503 y
        dv_cache_0108 p2284
    have p2286 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0504 x
        dv_cache_0089 p2285
    have p2287 :=
      @g_dffun2 x y z syntaxClass0436 dv_cache_0167 dv_cache_0168 dv_cache_0169
        dv_cache_0007 dv_cache_0069 dv_cache_0070
    have p2288_e01_recanon :
      Nominal.NPrf (syn_wb (syn_wfun syntaxClass0436) syntaxFormula0505) :=
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
        p2287
    have p2288 :=
      @g_sylibr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0505
        (syn_wfun syntaxClass0436) p2286 p2288_e01_recanon
    have p2290 := @g_funeq (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y)) syntaxClass0436
    have p2291 := Nominal.mp p1853 p2290
    have p2292 :=
      @g_sylibr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wfun syntaxClass0436)
        (syn_wfun (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y))) p2288 p2291
    have p2294 :=
      @g_dmeqi (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y)) syntaxClass0436 p1853
    have p2295 := @g_pw1ss (syn_chwcn (syn_crn (.cv k))) (syn_chwcn (syn_cun P Y))
    have p2296 :=
      @g_syl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wss (syn_chwcn (syn_crn (.cv k))) (syn_chwcn (syn_cun P Y)))
        (syn_wss (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))) (syn_cpw1 (syn_chwcn (syn_cun P Y))))
        p1618 p2295
    have p2297 := (Nominal.classEqRefl (syn_cdm (syn_chnqmap1 (syn_crn (.cv k)))))
    have p2298 :=
      @g_eqcomi (syn_cdm (syn_chnqmap1 (syn_crn (.cv k))))
        (syn_crn (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k))))) p2297
    have p2299 :=
      @g_syl5eq (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_crn (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))))
        (syn_cdm (syn_chnqmap1 (syn_crn (.cv k))))
        (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))) p2298 p1915
    have p2303 :=
      @g_sseq12 (syn_crn (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))))
        (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))) (syn_cdm (syn_chnqmap1 (syn_cun P Y)))
        (syn_cpw1 (syn_chwcn (syn_cun P Y)))
    have p2304 :=
      @g_sylancl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classEq (syn_crn (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))))
          (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (.classEq (syn_cdm (syn_chnqmap1 (syn_cun P Y))) (syn_cpw1 (syn_chwcn (syn_cun P Y))))
        (syn_wb syntaxFormula0506 (syn_wss (syn_cpw1 (syn_chwcn (syn_crn (.cv k))))
            (syn_cpw1 (syn_chwcn (syn_cun P Y)))))
        p2299 p0805 p2303
    have p2305 :=
      @g_mpbird (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0506
        (syn_wss (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))) (syn_cpw1 (syn_chwcn (syn_cun P Y))))
        p2296 p2304
    have p2306 :=
      @g_dmcosseq (syn_chnqmap1 (syn_cun P Y)) (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k))))
    have p2307 :=
      @g_syl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0506
        (.classEq syntaxClass0507 (syn_cdm (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k))))))
        p2305 p2306
    have p2308 := @g_dfrn4 (syn_chnqmap1 (syn_crn (.cv k)))
    have p2309 :=
      @g_syl6eqr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxClass0507
        (syn_cdm (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))))
        (syn_crn (syn_chnqmap1 (syn_crn (.cv k)))) p2307 p2308
    have p2310 :=
      @g_elpw1 a (.cv q) (syn_chwcn (syn_crn (.cv k))) dv_cache_0109 dv_cache_0022
    have p2311 := @g_id (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
    have p2312 :=
      @g_a1d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_chwniso (syn_crn (.cv k))) (syn_cvv))
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) p1664
    have p2313 :=
      @g_ecelqsg (syn_chwcn (syn_crn (.cv k))) (.cv a) (syn_chwniso (syn_crn (.cv k)))
        (syn_cvv)
    have p2314 :=
      @g_ex (.classMem (syn_chwniso (syn_crn (.cv k))) (syn_cvv))
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0508 p2313
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

@[expose]
noncomputable def g_cfbhnqinjcodecoverddndv_stage8 (u : Var) (P : Class) (k : Var)
    (Y : Class) (hyp_cfbhnqinjcodecoverddndv_2 : Nominal.NPrf (.classMem Y (syn_cvv)))
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
    have dv_cache_0096 : q ∉ ((syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)).fv := by
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
    have dv_cache_0107 : z ∉ ((syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)).fv := by
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
    have dv_cache_0116 : q ∉ ((syn_csn (.cv a))).fv := by
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
      x ∉ ((syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)))).fv := by
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
        ((syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))
            (syn_chwniso (syn_cun P Y)))).fv :=
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
        ((Wff.classMem (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))
            (syn_chnord (syn_crn (.cv k))))).fv :=
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
    have dv_cache_0171 : q ∉ ((syn_cpw1 (syn_chwcn (syn_crn (.cv k))))).fv := by
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
    have dv_cache_0172 : q ∉ ((syn_chnord (syn_crn (.cv k)))).fv := by
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
    have dv_cache_0173 : q ∉ ((syn_chnqmap1 (syn_crn (.cv k)))).fv := by
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
    have dv_cache_0174 : a ∉ ((syn_chwniso (syn_crn (.cv k)))).fv := by
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
            (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a))))).fv :=
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
        ((syn_wrex q (syn_cpw1 (syn_chwcn (syn_crn (.cv k))))
            (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))))).fv :=
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
    have dv_cache_0177 : z ∉ ((syn_cpw1 (syn_chwcn (syn_crn (.cv k))))).fv := by
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
    have dv_cache_0178 : z ∉ ((syn_chnord (syn_crn (.cv k)))).fv := by
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
    have dv_cache_0179 : z ∉ ((syn_chnqmap1 (syn_crn (.cv k)))).fv := by
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
        ((Wff.imp (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))
              (syn_chwcn (syn_crn (.cv k)))) (.classMem
              (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))
                (syn_chwniso (syn_crn (.cv k)))) (syn_chnord (syn_crn (.cv k)))))).fv :=
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
        ((syn_wa (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
              (syn_ccnv (syn_chnqmap1 Y))
              (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))))
            (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)))
              (syn_chnqmap1 (syn_cun P Y)) (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))
                (syn_chwniso (syn_cun P Y)))))).fv :=
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
      x ∉ ((syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))).fv :=
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
    have dv_cache_0183 : x ∉ ((syn_ccnv (syn_chnqmap1 Y))).fv := by
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
      (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwcn (syn_crn (.cv k))))
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
    let syntaxClass0190 : Class :=
      (syn_cfv (syn_chnqinc (syn_cfv (syn_c2nd) (.cv u)) (syn_cun P Y))
        (syn_cec (.cv u) (syn_chwniso (syn_cfv (syn_c2nd) (.cv u)))))
    let syntaxFormula0193 : Wff :=
      (.classEq (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
        syntaxClass0190)
    let syntaxClass0360 : Class :=
      (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso (syn_cun P Y)))
    let syntaxFormula0365 : Wff := (.classEq syntaxClass0190 syntaxClass0360)
    let syntaxFormula0411 : Wff :=
      (.classEq (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))
        (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))))
    let syntaxClass0414 : Class :=
      (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso (syn_crn (.cv k))))
    let syntaxFormula0419 : Wff :=
      (syn_wfn (syn_chnqmap1 (syn_crn (.cv k))) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
    let syntaxFormula0429 : Wff :=
      (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)))
        (syn_chnqmap1 (syn_cun P Y)) syntaxClass0360)
    let syntaxFormula0432 : Wff :=
      (syn_wbr (.cv x) (syn_chnqmap1 (syn_cun P Y)) syntaxClass0360)
    let syntaxClass0436 : Class :=
      (syn_ccom (syn_chnqmap1 (syn_cun P Y)) (syn_ccnv (syn_chnqmap1 (syn_crn (.cv k)))))
    let syntaxFormula0438 : Wff :=
      (syn_wbr syntaxClass0414 (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y)) syntaxClass0360)
    let syntaxClass0507 : Class := (syn_cdm syntaxClass0436)
    let syntaxFormula0508 : Wff :=
      (.classMem (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
        (syn_cqs (syn_chwcn (syn_crn (.cv k))) (syn_chwniso (syn_crn (.cv k)))))
    let syntaxFormula0509 : Wff :=
      (.classMem (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
        (syn_chnord (syn_crn (.cv k))))
    let syntaxFormula0510 : Wff :=
      (.classMem (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))
        (syn_chnord (syn_crn (.cv k))))
    let syntaxFormula0511 : Wff := (syn_wb syntaxFormula0510 syntaxFormula0509)
    let syntaxFormula0512 : Wff := (syn_wb syntaxFormula0509 syntaxFormula0510)
    let syntaxFormula0513 : Wff := (.imp syntaxFormula0509 syntaxFormula0510)
    let syntaxFormula0514 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classEq (.cv q) (syn_csn (.cv a))))
    let syntaxFormula0515 : Wff :=
      (.classMem (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))
        (syn_chnord (syn_crn (.cv k))))
    let syntaxFormula0516 : Wff :=
      (syn_wf (syn_chnqmap1 (syn_crn (.cv k))) (syn_cpw1 (syn_chwcn (syn_crn (.cv k))))
        (syn_chnord (syn_crn (.cv k))))
    let syntaxFormula0517 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))))
    let syntaxFormula0518 : Wff :=
      (syn_wa (.classMem (syn_csn (.cv a)) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))))
    let syntaxFormula0519 : Wff :=
      (syn_wrex q (syn_cpw1 (syn_chwcn (syn_crn (.cv k))))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))))
    let syntaxFormula0520 : Wff :=
      (syn_wral z (syn_chnord (syn_crn (.cv k))) syntaxFormula0519)
    let syntaxFormula0521 : Wff :=
      (syn_wfn (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y)) (syn_chnord (syn_crn (.cv k))))
    let syntaxFormula0522 : Wff :=
      (.classMem syntaxClass0414 (syn_chnord (syn_crn (.cv k))))
    let syntaxFormula0523 : Wff := (.imp syntaxFormula0060 syntaxFormula0522)
    let syntaxFormula0524 : Wff :=
      (.imp (.classEq (.cv a) (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))) syntaxFormula0523)
    let syntaxFormula0525 : Wff := (syn_wa syntaxFormula0521 syntaxFormula0522)
    let syntaxClass0526 : Class :=
      (syn_cfv (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y)) syntaxClass0414)
    let syntaxFormula0527 : Wff := (.classEq syntaxClass0526 syntaxClass0360)
    let syntaxFormula0528 : Wff := (syn_wb syntaxFormula0527 syntaxFormula0438)
    let syntaxFormula0529 : Wff := (syn_wb syntaxFormula0438 syntaxFormula0527)
    let syntaxFormula0530 : Wff := (.imp syntaxFormula0438 syntaxFormula0527)
    let syntaxFormula0531 : Wff := (.classEq syntaxClass0360 syntaxClass0526)
    let syntaxFormula0532 : Wff := (.classEq syntaxClass0190 syntaxClass0526)
    let syntaxFormula0533 : Wff := (syn_wb syntaxFormula0365 syntaxFormula0532)
    let syntaxFormula0534 : Wff :=
      (.classEq (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
        syntaxClass0526)
    let syntaxFormula0535 : Wff := (syn_wb syntaxFormula0193 syntaxFormula0534)
    let syntaxClass0536 : Class :=
      (syn_cfv (syn_chnqmap1 Y) (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))))
    let syntaxFormula0537 : Wff :=
      (.classEq syntaxClass0536
        (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y)))
    let syntaxFormula0538 : Wff :=
      (.classMem (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)))
        (syn_cpw1 (syn_chwcn Y)))
    let syntaxFormula0539 : Wff :=
      (syn_wa (syn_wfn (syn_chnqmap1 Y) (syn_cpw1 (syn_chwcn Y))) syntaxFormula0538)
    let syntaxFormula0540 : Wff :=
      (syn_wbr (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))) (syn_chnqmap1 Y)
        (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y)))
    let syntaxFormula0541 : Wff := (syn_wb syntaxFormula0537 syntaxFormula0540)
    let syntaxFormula0542 : Wff :=
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        (syn_ccnv (syn_chnqmap1 Y)) (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))))
    let syntaxFormula0543 : Wff :=
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        (syn_ccnv (syn_chnqmap1 Y)) (.cv x))
    let syntaxFormula0544 : Wff := (syn_wa syntaxFormula0543 syntaxFormula0432)
    let syntaxFormula0545 : Wff := (syn_wa syntaxFormula0542 syntaxFormula0429)
    let syntaxFormula0546 : Wff := (syn_wex x syntaxFormula0544)
    let syntaxFormula0547 : Wff :=
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        (syn_ccom (syn_chnqmap1 (syn_cun P Y)) (syn_ccnv (syn_chnqmap1 Y))) syntaxClass0360)
    let syntaxFormula0548 : Wff :=
      (syn_wbr (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        (syn_chnqinc Y (syn_cun P Y)) syntaxClass0360)
    let syntaxFormula0549 : Wff := (.classEq syntaxClass0069 syntaxClass0360)
    let syntaxFormula0550 : Wff := (syn_wb syntaxFormula0549 syntaxFormula0548)
    let syntaxFormula0551 : Wff := (syn_wb syntaxFormula0548 syntaxFormula0549)
    let syntaxFormula0552 : Wff := (.imp syntaxFormula0548 syntaxFormula0549)
    let syntaxFormula0553 : Wff := (.classEq syntaxClass0360 syntaxClass0069)
    let syntaxFormula0554 : Wff := (.classEq syntaxClass0526 syntaxClass0069)
    let syntaxFormula0555 : Wff := (syn_wb syntaxFormula0527 syntaxFormula0554)
    let syntaxFormula0556 : Wff :=
      (.classEq (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
        syntaxClass0069)
    let syntaxFormula0557 : Wff := (syn_wb syntaxFormula0534 syntaxFormula0556)
    let syntaxFormula0558 : Wff :=
      (.classMem (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
        (syn_crn (syn_chnqinc Y (syn_cun P Y))))
    let syntaxFormula0559 : Wff := (syn_wb syntaxFormula0558 syntaxFormula0070)
    let syntaxFormula0560 : Wff := (syn_wb syntaxFormula0070 syntaxFormula0558)
    let syntaxFormula0561 : Wff := (.imp syntaxFormula0070 syntaxFormula0558)
    have p2315 :=
      @g_syl56 (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_chwniso (syn_crn (.cv k))) (syn_cvv))
        (.imp (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0508) p2311
        p2312 p2314
    have p2316 :=
      @g_pm2_43d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0508 p2315
    have p2317 := (Nominal.classEqRefl (syn_chnord (syn_crn (.cv k))))
    have p2318 :=
      @g_eleq2i (syn_chnord (syn_crn (.cv k)))
        (syn_cqs (syn_chwcn (syn_crn (.cv k))) (syn_chwniso (syn_crn (.cv k))))
        (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))) p2317
    have p2319 :=
      @g_syl6ibr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0508
        syntaxFormula0509 p2316 p2318
    have p2320 :=
      @g_eleq1 (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))
        (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))) (syn_chnord (syn_crn (.cv k)))
    have p2321 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0411
        syntaxFormula0511 p1789 p2320
    have p2322 := @g_bicom syntaxFormula0510 syntaxFormula0509
    have p2323 :=
      @g_syl6ib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0511
        syntaxFormula0512 p2321 p2322
    have p2324 := @g_bi1 syntaxFormula0509 syntaxFormula0510
    have p2325 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0512
        syntaxFormula0513 p2323 p2324
    have p2326 := @g_id syntaxFormula0509
    have p2327 :=
      @g_a1ii
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
          (.imp (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0513))
        (.imp syntaxFormula0509 syntaxFormula0509) p2325 p2326
    have p2328 :=
      @g_mpdd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0509
        syntaxFormula0510 p2319 p2327
    have p2329 :=
      @g_adantrd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0510
        (.classEq (.cv q) (syn_csn (.cv a))) p2328
    have p2330 :=
      @g_simpr (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classEq (.cv q) (syn_csn (.cv a)))
    have p2331 := @g_fveq2 (.cv q) (syn_csn (.cv a)) (syn_chnqmap1 (syn_crn (.cv k)))
    have p2332 :=
      @g_syl syntaxFormula0514 (.classEq (.cv q) (syn_csn (.cv a)))
        (.classEq (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))
          (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a))))
        p2330 p2331
    have p2333 :=
      @g_eleq1d syntaxFormula0514 (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))
        (syn_chnord (syn_crn (.cv k))) p2332
    have p2334 := @g_biimprd syntaxFormula0514 syntaxFormula0515 syntaxFormula0510 p2333
    have p2335 :=
      @g_sylcom (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0514
        syntaxFormula0510 syntaxFormula0515 p2329 p2334
    have p2336 :=
      @g_exp3a (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classEq (.cv q) (syn_csn (.cv a))) syntaxFormula0515 p2335
    have p2337 :=
      @g_rexlimdv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classEq (.cv q) (syn_csn (.cv a))) syntaxFormula0515 a
        (syn_chwcn (syn_crn (.cv k))) dv_cache_0170 dv_cache_0024 p2336
    have p2338 :=
      @g_syl5bi (.classMem (.cv q) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (syn_wrex a (syn_chwcn (syn_crn (.cv k))) (.classEq (.cv q) (syn_csn (.cv a))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0515 p2310 p2337
    have p2339 :=
      @g_ralrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0515 q
        (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))) dv_cache_0096 p2338
    have p2340 :=
      @g_jca (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0419
        (syn_wral q (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0515) p1813
        p2339
    have p2341 :=
      @g_fnfvrnss q (syn_cpw1 (syn_chwcn (syn_crn (.cv k))))
        (syn_chnord (syn_crn (.cv k))) (syn_chnqmap1 (syn_crn (.cv k))) dv_cache_0171
        dv_cache_0172 dv_cache_0173
    have p2342 :=
      @g_syl (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wa syntaxFormula0419
          (syn_wral q (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0515))
        (syn_wss (syn_crn (syn_chnqmap1 (syn_crn (.cv k)))) (syn_chnord (syn_crn (.cv k))))
        p2340 p2341
    have p2343 :=
      @g_jca (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0419
        (syn_wss (syn_crn (syn_chnqmap1 (syn_crn (.cv k)))) (syn_chnord (syn_crn (.cv k))))
        p1813 p2342
    have p2344 := (Nominal.biimpRefl syntaxFormula0516)
    have p2345 :=
      @g_sylibr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wa syntaxFormula0419 (syn_wss (syn_crn (syn_chnqmap1 (syn_crn (.cv k))))
            (syn_chnord (syn_crn (.cv k)))))
        syntaxFormula0516 p2343 p2344
    have p2347 :=
      @g_eleq2i (syn_chnord (syn_crn (.cv k)))
        (syn_cqs (syn_chwcn (syn_crn (.cv k))) (syn_chwniso (syn_crn (.cv k)))) (.cv z)
        p2317
    have p2348 :=
      @g_biimpi (.classMem (.cv z) (syn_chnord (syn_crn (.cv k))))
        (.classMem (.cv z)
          (syn_cqs (syn_chwcn (syn_crn (.cv k))) (syn_chwniso (syn_crn (.cv k)))))
        p2347
    have p2349 :=
      @g_elqsi a (syn_chwcn (syn_crn (.cv k))) (.cv z) (syn_chwniso (syn_crn (.cv k)))
        dv_cache_0022 dv_cache_0114 dv_cache_0174
    have p2350 :=
      @g_syl (.classMem (.cv z) (syn_chnord (syn_crn (.cv k))))
        (.classMem (.cv z)
          (syn_cqs (syn_chwcn (syn_crn (.cv k))) (syn_chwniso (syn_crn (.cv k)))))
        (syn_wrex a (syn_chwcn (syn_crn (.cv k)))
          (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))))
        p2348 p2349
    have p2353 :=
      @g_adantr (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classMem (syn_csn (.cv a)) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))) p1649
    have p2354 :=
      @g_simpr (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))))
    have p2355 :=
      @g_adantrd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0411
        (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))) p1789
    have p2356 :=
      @g_eqcom (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))
        (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
    have p2357 :=
      @g_syl6ib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0517
        syntaxFormula0411
        (.classEq (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
          (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a))))
        p2355 p2356
    have p2358 :=
      @g_eqeq2 (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a))) (.cv z)
    have p2359 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0517
        (.classEq (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))
          (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a))))
        (syn_wb (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))))
          (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))))
        p2357 p2358
    have p2360 :=
      @g_bi1 (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a))))
    have p2361 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0517
        (syn_wb (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))))
          (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))))
        (.imp (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))))
          (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))))
        p2359 p2360
    have p2362 :=
      @g_mpdi (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0517
        (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a))))
        p2354 p2361
    have p2363 :=
      @g_pm3_2 (.classMem (syn_csn (.cv a)) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a))))
    have p2364 :=
      @g_syl9 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0517
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a))))
        (.classMem (syn_csn (.cv a)) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        syntaxFormula0518 p2362 p2363
    have p2365 :=
      @g_syl5 syntaxFormula0517
        (.classMem (syn_csn (.cv a)) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.imp syntaxFormula0517 syntaxFormula0518) p2353 p2364
    have p2366 :=
      @g_pm2_43d (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0517
        syntaxFormula0518 p2365
    have p2368 :=
      @g_eqeq2d (.classEq (.cv q) (syn_csn (.cv a)))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q))
        (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a))) (.cv z) p2331
    have p2369 :=
      @g_rspcev (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (.cv q)))
        (.classEq (.cv z) (syn_cfv (syn_chnqmap1 (syn_crn (.cv k))) (syn_csn (.cv a)))) q
        (syn_csn (.cv a)) (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))) dv_cache_0116
        dv_cache_0171 dv_cache_0175 p2368
    have p2370 :=
      @g_syl6 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0517
        syntaxFormula0518 syntaxFormula0519 p2366 p2369
    have p2371 :=
      @g_exp3a (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k))))
        (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))))
        syntaxFormula0519 p2370
    have p2372 :=
      @g_rexlimdv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))))
        syntaxFormula0519 a (syn_chwcn (syn_crn (.cv k))) dv_cache_0176 dv_cache_0024
        p2371
    have p2373 :=
      @g_syl5 (.classMem (.cv z) (syn_chnord (syn_crn (.cv k))))
        (syn_wrex a (syn_chwcn (syn_crn (.cv k)))
          (.classEq (.cv z) (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k))))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0519 p2350 p2372
    have p2374 :=
      @g_ralrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0519 z
        (syn_chnord (syn_crn (.cv k))) dv_cache_0107 p2373
    have p2375 :=
      @g_jca (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0516
        syntaxFormula0520 p2345 p2374
    have p2376 :=
      @g_dffo3 q z (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))) (syn_chnord (syn_crn (.cv k)))
        (syn_chnqmap1 (syn_crn (.cv k))) dv_cache_0171 dv_cache_0177 dv_cache_0172
        dv_cache_0178 dv_cache_0173 dv_cache_0179 dv_cache_0122
    have p2377 :=
      @g_sylibr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wa syntaxFormula0516 syntaxFormula0520)
        (syn_wfo (syn_chnqmap1 (syn_crn (.cv k))) (syn_cpw1 (syn_chwcn (syn_crn (.cv k))))
          (syn_chnord (syn_crn (.cv k))))
        p2375 p2376
    have p2378 :=
      @g_dffo2 (syn_cpw1 (syn_chwcn (syn_crn (.cv k)))) (syn_chnord (syn_crn (.cv k)))
        (syn_chnqmap1 (syn_crn (.cv k)))
    have p2379 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wfo (syn_chnqmap1 (syn_crn (.cv k))) (syn_cpw1 (syn_chwcn (syn_crn (.cv k))))
          (syn_chnord (syn_crn (.cv k))))
        (syn_wa syntaxFormula0516 (.classEq (syn_crn (syn_chnqmap1 (syn_crn (.cv k))))
            (syn_chnord (syn_crn (.cv k)))))
        p2377 p2378
    have p2380 :=
      @g_simprd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0516
        (.classEq (syn_crn (syn_chnqmap1 (syn_crn (.cv k)))) (syn_chnord (syn_crn (.cv k))))
        p2379
    have p2381 :=
      @g_eqtrd (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxClass0507
        (syn_crn (syn_chnqmap1 (syn_crn (.cv k)))) (syn_chnord (syn_crn (.cv k))) p2309
        p2380
    have p2382 :=
      @g_syl5eq (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_cdm (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y))) syntaxClass0507
        (syn_chnord (syn_crn (.cv k))) p2294 p2381
    have p2383 :=
      @g_jca (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wfun (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y)))
        (.classEq (syn_cdm (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y)))
          (syn_chnord (syn_crn (.cv k))))
        p2292 p2382
    have p2384 := (Nominal.biimpRefl syntaxFormula0521)
    have p2385 :=
      @g_sylibr (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wa (syn_wfun (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y)))
          (.classEq (syn_cdm (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y)))
            (syn_chnord (syn_crn (.cv k)))))
        syntaxFormula0521 p2383 p2384
    have p2391 :=
      @g_eleq1d (.classEq (.cv a) (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)))
        (syn_cec (.cv a) (syn_chwniso (syn_crn (.cv k)))) syntaxClass0414
        (syn_chnord (syn_crn (.cv k))) p1793
    have p2392 :=
      @g_imbi12d (.classEq (.cv a) (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)))
        (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0060
        syntaxFormula0509 syntaxFormula0522 p1790 p2391
    have p2393 :=
      @g_syl5ibcom (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.imp (.classMem (.cv a) (syn_chwcn (syn_crn (.cv k)))) syntaxFormula0509)
        (.classEq (.cv a) (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))) syntaxFormula0523
        p2319 p2392
    have p2394 :=
      @g_alrimiv (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0524 a
        dv_cache_0024 p2393
    have p2395 := @g_nfv syntaxFormula0523 a dv_cache_0180
    have p2396 :=
      @g_n_19_23 (.classEq (.cv a) (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)))
        syntaxFormula0523 a p2395
    have p2397 :=
      @g_sylib (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) (.all a syntaxFormula0524)
        (.imp (syn_wex a (.classEq (.cv a) (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))))
          syntaxFormula0523)
        p2394 p2396
    have p2398 :=
      @g_syl5bi (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_cvv))
        (syn_wex a (.classEq (.cv a) (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0523 p1645 p2397
    have p2400 :=
      @g_a1ii
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
          (.imp (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_cvv))
            syntaxFormula0523))
        (.imp (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_cvv))
          (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_cvv)))
        p2398 p1802
    have p2401 :=
      @g_com23 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_cvv))
        syntaxFormula0060 syntaxFormula0522 p2400
    have p2402 :=
      @g_mpdi (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0060
        (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_cvv))
        syntaxFormula0522 p1643 p2401
    have p2403 :=
      @g_sylcom (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0060
        syntaxFormula0522 p0286 p2402
    have p2404 := @g_pm3_2 syntaxFormula0521 syntaxFormula0522
    have p2405 :=
      @g_syl9 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0522
        syntaxFormula0521 syntaxFormula0525 p2403 p2404
    have p2406 :=
      @g_syl5 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0521
        (.classMem (.cv u) (syn_chwcn P))
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0525) p2385
        p2405
    have p2407 :=
      @g_pm2_43d (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0525 p2406
    have p2408 :=
      @g_fnbrfvb (syn_chnord (syn_crn (.cv k))) syntaxClass0414 syntaxClass0360
        (syn_chnqinc (syn_crn (.cv k)) (syn_cun P Y))
    have p2409 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0525
        syntaxFormula0528 p2407 p2408
    have p2410 := @g_bicom syntaxFormula0527 syntaxFormula0438
    have p2411 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0528
        syntaxFormula0529 p2409 p2410
    have p2412 := @g_bi1 syntaxFormula0438 syntaxFormula0527
    have p2413 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0529
        syntaxFormula0530 p2411 p2412
    have p2414 := @g_id syntaxFormula0438
    have p2415 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P))
          (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0530))
        (.imp syntaxFormula0438 syntaxFormula0438) p2413 p2414
    have p2416 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0438
        syntaxFormula0527 p1855 p2415
    have p2417 := @g_eqcom syntaxClass0526 syntaxClass0360
    have p2418 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0527
        syntaxFormula0531 p2416 p2417
    have p2419 := @g_eqeq2 syntaxClass0360 syntaxClass0526 syntaxClass0190
    have p2420 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0531
        syntaxFormula0533 p2418 p2419
    have p2421 := @g_bi1 syntaxFormula0365 syntaxFormula0532
    have p2422 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0533
        (.imp syntaxFormula0365 syntaxFormula0532) p2420 p2421
    have p2423 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0365
        syntaxFormula0532 p1642 p2422
    have p2424 :=
      @g_eqeq2 syntaxClass0190 syntaxClass0526
        (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
    have p2425 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0532
        syntaxFormula0535 p2423 p2424
    have p2426 := @g_bi1 syntaxFormula0193 syntaxFormula0534
    have p2427 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0535
        (.imp syntaxFormula0193 syntaxFormula0534) p2425 p2426
    have p2428 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0193
        syntaxFormula0534 p0824 p2427
    have p2429 :=
      @g_hnqmap1valcl Y (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))
        hyp_cfbhnqinjcodecoverddndv_2
    have p2430 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwcn Y))
        syntaxFormula0537 p0340 p2429
    have p2431 := @g_hnqmap1fn Y hyp_cfbhnqinjcodecoverddndv_2
    have p2432 :=
      @g_a1i (syn_wfn (syn_chnqmap1 Y) (syn_cpw1 (syn_chwcn Y)))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) p2431
    have p2433 := @g_snelpw1 (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwcn Y)
    have p2434 :=
      @g_syl6ibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (.classMem (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwcn Y))
        syntaxFormula0538 p0340 p2433
    have p2435 :=
      @g_pm3_2 (syn_wfn (syn_chnqmap1 Y) (syn_cpw1 (syn_chwcn Y))) syntaxFormula0538
    have p2436 :=
      @g_syl9 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0538
        (syn_wfn (syn_chnqmap1 Y) (syn_cpw1 (syn_chwcn Y))) syntaxFormula0539 p2434 p2435
    have p2437 :=
      @g_syl5 (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y)
        (syn_wfn (syn_chnqmap1 Y) (syn_cpw1 (syn_chwcn Y)))
        (.classMem (.cv u) (syn_chwcn P))
        (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0539) p2432
        p2436
    have p2438 :=
      @g_pm2_43d (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0539 p2437
    have p2439 :=
      @g_fnbrfvb (syn_cpw1 (syn_chwcn Y))
        (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)))
        (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        (syn_chnqmap1 Y)
    have p2440 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0539
        syntaxFormula0541 p2438 p2439
    have p2441 := @g_bi1 syntaxFormula0537 syntaxFormula0540
    have p2442 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0541
        (.imp syntaxFormula0537 syntaxFormula0540) p2440 p2441
    have p2443 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0537
        syntaxFormula0540 p2430 p2442
    have p2444 :=
      @g_brcnv (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))) (syn_chnqmap1 Y)
    have p2445 :=
      @g_syl6ibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0540
        syntaxFormula0542 p2443 p2444
    have p2446 :=
      @g_jcad (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0542
        syntaxFormula0429 p2445 p1841
    have p2449 :=
      @g_breq2d (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))))
        (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)))
        (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        (syn_ccnv (syn_chnqmap1 Y)) p1844
    have p2452 :=
      @g_anbi12d (.classEq (.cv x) (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))))
        syntaxFormula0543 syntaxFormula0542 syntaxFormula0432 syntaxFormula0429 p2449
        p1847
    have p2453 :=
      @g_spcev syntaxFormula0544 syntaxFormula0545 x
        (syn_csn (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u))) dv_cache_0151 dv_cache_0181
        p1843 p2452
    have p2454 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0545
        syntaxFormula0546 p2446 p2453
    have p2455 :=
      @g_brco x (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        syntaxClass0360 (syn_chnqmap1 (syn_cun P Y)) (syn_ccnv (syn_chnqmap1 Y))
        dv_cache_0182 dv_cache_0154 dv_cache_0029 dv_cache_0183
    have p2456 :=
      @g_syl6ibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0546
        syntaxFormula0547 p2454 p2455
    have p2457 := (Nominal.classEqRefl (syn_chnqinc Y (syn_cun P Y)))
    have p2458 :=
      @g_breqi (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        syntaxClass0360 (syn_chnqinc Y (syn_cun P Y))
        (syn_ccom (syn_chnqmap1 (syn_cun P Y)) (syn_ccnv (syn_chnqmap1 Y))) p2457
    have p2459 :=
      @g_syl6ibr (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0547
        syntaxFormula0548 p2456 p2458
    have p2460 :=
      @g_fnbrfvb (syn_chnord Y)
        (syn_cec (syn_cfv (syn_chncodetrnfn (.cv k)) (.cv u)) (syn_chwniso Y))
        syntaxClass0360 (syn_chnqinc Y (syn_cun P Y))
    have p2461 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0068
        syntaxFormula0550 p0346 p2460
    have p2462 := @g_bicom syntaxFormula0549 syntaxFormula0548
    have p2463 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0550
        syntaxFormula0551 p2461 p2462
    have p2464 := @g_bi1 syntaxFormula0548 syntaxFormula0549
    have p2465 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0551
        syntaxFormula0552 p2463 p2464
    have p2466 := @g_id syntaxFormula0548
    have p2467 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P))
          (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0552))
        (.imp syntaxFormula0548 syntaxFormula0548) p2465 p2466
    have p2468 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0548
        syntaxFormula0549 p2459 p2467
    have p2469 := @g_eqcom syntaxClass0069 syntaxClass0360
    have p2470 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0549
        syntaxFormula0553 p2468 p2469
    have p2471 := @g_eqeq2 syntaxClass0360 syntaxClass0069 syntaxClass0526
    have p2472 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0553
        syntaxFormula0555 p2470 p2471
    have p2473 := @g_bi1 syntaxFormula0527 syntaxFormula0554
    have p2474 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0555
        (.imp syntaxFormula0527 syntaxFormula0554) p2472 p2473
    have p2475 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0527
        syntaxFormula0554 p2416 p2474
    have p2476 :=
      @g_eqeq2 syntaxClass0526 syntaxClass0069
        (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
    have p2477 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0554
        syntaxFormula0557 p2475 p2476
    have p2478 := @g_bi1 syntaxFormula0534 syntaxFormula0556
    have p2479 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0557
        (.imp syntaxFormula0534 syntaxFormula0556) p2477 p2478
    have p2480 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0534
        syntaxFormula0556 p2428 p2479
    have p2481 :=
      @g_eleq1 (syn_cfv (syn_chnqinc P (syn_cun P Y)) (syn_cec (.cv u) (syn_chwniso P)))
        syntaxClass0069 (syn_crn (syn_chnqinc Y (syn_cun P Y)))
    have p2482 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0556
        syntaxFormula0559 p2480 p2481
    have p2483 := @g_bicom syntaxFormula0558 syntaxFormula0070
    have p2484 :=
      @g_syl6ib (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0559
        syntaxFormula0560 p2482 p2483
    have p2485 := @g_bi1 syntaxFormula0070 syntaxFormula0558
    have p2486 :=
      @g_syl6 (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0560
        syntaxFormula0561 p2484 p2485
    have p2487 := @g_id syntaxFormula0070
    have p2488 :=
      @g_a1ii
        (.imp (.classMem (.cv u) (syn_chwcn P))
          (.imp (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0561))
        (.imp syntaxFormula0070 syntaxFormula0070) p2486 p2487
    have p2489 :=
      @g_mpdd (.classMem (.cv u) (syn_chwcn P))
        (syn_wf1 (.cv k) (syn_cfv (syn_c2nd) (.cv u)) Y) syntaxFormula0070
        syntaxFormula0558 p0348 p2488
    exact continuation p2489

end NFChoice.DirectNominalPrf.WPPReplay

end
