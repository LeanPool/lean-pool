/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `ReplaySupport.WellOrderPullback4`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_pwpullwesetimpndv_stage4`. -/
@[expose]
noncomputable def gPwpullwesetimpndvStage4 (x : Var) (y : Var) (f : Var) (r : Var)
    (p0015 : _) (p0042 : _) (p0286 : _) (p0615 : _) (p0766 : _) (p0769 : _) (p0770 : _)
    (p0776 : _) (p0780 : _) (p0782 : _) (p0801 : _) (p0802 : _) (p0807 : _) (p0811 : _)
    (p0812 : _) {Result : Type} (continuation : _ → _ → _ → _ → _ → _ → _ → _ → Result) :=
  show Result from
    by
    let proofSupport : Finset Var :=
      ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ f } : Finset Var) ∪
        ({ r } : Finset Var)
    let a : Var := freshVar proofSupport 0
    let b : Var := freshVar proofSupport 1
    let c : Var := freshVar proofSupport 2
    let d : Var := freshVar proofSupport 3
    let e : Var := freshVar proofSupport 6
    let h : Var := freshVar proofSupport 7
    let u : Var := freshVar proofSupport 8
    let v : Var := freshVar proofSupport 9
    let w : Var := freshVar proofSupport 10
    let t : Var := freshVar proofSupport 11
    have fresh_b : b ∉ proofSupport :=
      by
      change freshVar proofSupport 1 ∉ proofSupport
      exact freshVar_not_mem proofSupport 1
    have fresh_b_ne_y : b ≠ y := by
      intro h
      exact
        fresh_b
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_b_ne_f : b ≠ f := by
      intro h
      exact
        fresh_b
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_b_ne_r : b ≠ r := by
      intro h
      exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_c : c ∉ proofSupport :=
      by
      change freshVar proofSupport 2 ∉ proofSupport
      exact freshVar_not_mem proofSupport 2
    have fresh_c_ne_y : c ≠ y := by
      intro h
      exact
        fresh_c
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_c_ne_r : c ≠ r := by
      intro h
      exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_d : d ∉ proofSupport :=
      by
      change freshVar proofSupport 3 ∉ proofSupport
      exact freshVar_not_mem proofSupport 3
    have fresh_d_ne_y : d ≠ y := by
      intro h
      exact
        fresh_d
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_d_ne_r : d ≠ r := by
      intro h
      exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_e : e ∉ proofSupport :=
      by
      change freshVar proofSupport 6 ∉ proofSupport
      exact freshVar_not_mem proofSupport 6
    have fresh_e_ne_y : e ≠ y := by
      intro h
      exact
        fresh_e
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_e_ne_r : e ≠ r := by
      intro h
      exact fresh_e (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_u : u ∉ proofSupport :=
      by
      change freshVar proofSupport 8 ∉ proofSupport
      exact freshVar_not_mem proofSupport 8
    have fresh_u_ne_y : u ≠ y := by
      intro h
      exact
        fresh_u
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_u_ne_f : u ≠ f := by
      intro h
      exact
        fresh_u
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_v : v ∉ proofSupport :=
      by
      change freshVar proofSupport 9 ∉ proofSupport
      exact freshVar_not_mem proofSupport 9
    have fresh_v_ne_x : v ≠ x := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_v_ne_y : v ≠ y := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_v_ne_f : v ≠ f := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_v_ne_r : v ≠ r := by
      intro h
      exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_w : w ∉ proofSupport :=
      by
      change freshVar proofSupport 10 ∉ proofSupport
      exact freshVar_not_mem proofSupport 10
    have fresh_w_ne_x : w ≠ x := by
      intro h
      exact
        fresh_w
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_w_ne_y : w ≠ y := by
      intro h
      exact
        fresh_w
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_w_ne_f : w ≠ f := by
      intro h
      exact
        fresh_w
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_w_ne_r : w ≠ r := by
      intro h
      exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_t : t ∉ proofSupport :=
      by
      change freshVar proofSupport 11 ∉ proofSupport
      exact freshVar_not_mem proofSupport 11
    have fresh_t_ne_x : t ≠ x := by
      intro h
      exact
        fresh_t
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_t_ne_y : t ≠ y := by
      intro h
      exact
        fresh_t
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_t_ne_f : t ≠ f := by
      intro h
      exact
        fresh_t
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_t_ne_r : t ≠ r := by
      intro h
      exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_a_ne_b : a ≠ b :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 1
      exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
    have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
    have fresh_a_ne_u : a ≠ u :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 8
      exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
    have fresh_u_ne_a : u ≠ a := Ne.symm fresh_a_ne_u
    have fresh_a_ne_v : a ≠ v :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 0) (j := 9) (by decide)
    have fresh_v_ne_a : v ≠ a := Ne.symm fresh_a_ne_v
    have fresh_a_ne_w : a ≠ w :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 0) (j := 10) (by decide)
    have fresh_w_ne_a : w ≠ a := Ne.symm fresh_a_ne_w
    have fresh_a_ne_t : a ≠ t :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 0) (j := 11) (by decide)
    have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
    have fresh_b_ne_c : b ≠ c :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 2
      exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
    have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
    have fresh_b_ne_d : b ≠ d :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
    have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
    have fresh_b_ne_e : b ≠ e :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
    have fresh_e_ne_b : e ≠ b := Ne.symm fresh_b_ne_e
    have fresh_b_ne_u : b ≠ u :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 8
      exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
    have fresh_b_ne_v : b ≠ v :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
    have fresh_v_ne_b : v ≠ b := Ne.symm fresh_b_ne_v
    have fresh_b_ne_w : b ≠ w :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 1) (j := 10) (by decide)
    have fresh_w_ne_b : w ≠ b := Ne.symm fresh_b_ne_w
    have fresh_c_ne_d : c ≠ d :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
    have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
    have fresh_c_ne_e : c ≠ e :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
    have fresh_e_ne_c : e ≠ c := Ne.symm fresh_c_ne_e
    have fresh_c_ne_v : c ≠ v :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 2) (j := 9) (by decide)
    have fresh_c_ne_w : c ≠ w :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 2) (j := 10) (by decide)
    have fresh_d_ne_e : d ≠ e :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
    have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
    have fresh_d_ne_v : d ≠ v :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
    have fresh_d_ne_w : d ≠ w :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 3) (j := 10) (by decide)
    have fresh_u_ne_v : u ≠ v :=
      by
      change freshVar proofSupport 8 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
    have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
    have fresh_u_ne_w : u ≠ w :=
      by
      change freshVar proofSupport 8 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 8) (j := 10) (by decide)
    have fresh_w_ne_u : w ≠ u := Ne.symm fresh_u_ne_w
    have fresh_v_ne_w : v ≠ w :=
      by
      change freshVar proofSupport 9 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 9) (j := 10) (by decide)
    have fresh_w_ne_v : w ≠ v := Ne.symm fresh_v_ne_w
    have fresh_v_ne_t : v ≠ t :=
      by
      change freshVar proofSupport 9 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 9) (j := 11) (by decide)
    have fresh_t_ne_v : t ≠ v := Ne.symm fresh_v_ne_t
    have fresh_w_ne_t : w ≠ t :=
      by
      change freshVar proofSupport 10 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 10) (j := 11) (by decide)
    have fresh_t_ne_w : t ≠ w := Ne.symm fresh_w_ne_t
    have dv_cache_0003 : b ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_y, not_false_eq_true])
    have dv_cache_0004 : d ≠ c := by exact (show d ≠ c from (by exact fresh_d_ne_c))
    have dv_cache_0005 : d ≠ b := by exact (show d ≠ b from (by exact fresh_d_ne_b))
    have dv_cache_0007 : c ∉ ((Class.cv r)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_r, not_false_eq_true])
    have dv_cache_0008 : d ∉ ((Class.cv r)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_d_ne_r, not_false_eq_true])
    have dv_cache_0009 : c ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_y, not_false_eq_true])
    have dv_cache_0010 : d ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_d_ne_y, not_false_eq_true])
    have dv_cache_0032 : b ≠ c := by exact (show b ≠ c from (by exact fresh_b_ne_c))
    have dv_cache_0043 : e ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_e_ne_y, not_false_eq_true])
    have dv_cache_0054 : d ≠ e := by exact (show d ≠ e from (by exact fresh_d_ne_e))
    have dv_cache_0096 : e ≠ c := by exact (show e ≠ c from (by exact fresh_e_ne_c))
    have dv_cache_0097 : e ≠ d := by exact (show e ≠ d from (by exact fresh_e_ne_d))
    have dv_cache_0098 : e ∉ ((Class.cv r)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_e_ne_r, not_false_eq_true])
    have dv_cache_0122 : b ∉ ((Wff.classEq (.cv d) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_d, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0131 :
      d ∉
        ((Wff.all b (.imp (synWa (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0)))
              (synWrex v (.cv b) (synWral w (.cv b)
                  (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_b, fresh_d_ne_y,
            fresh_d_ne_w, fresh_d_ne_v, fresh_d_ne_r, compact_fv_not_mem_empty, or_false,
            and_false, not_false_eq_true])
    have dv_cache_0132 :
      c ∉
        ((Wff.all b (.imp (synWa (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0)))
              (synWrex v (.cv b) (synWral w (.cv b)
                  (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_y,
            fresh_c_ne_w, fresh_c_ne_v, fresh_c_ne_r, compact_fv_not_mem_empty, or_false,
            and_false, not_false_eq_true])
    have dv_cache_0133 : w ∉ ((Class.cv b)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_w_ne_b, not_false_eq_true])
    have dv_cache_0134 :
      w ∉
        ((Class.cab u (synWa (.classMem (.cv u) (.cv y))
              (.classMem (.cv u) (synCima (.cv f) (.cv a)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_u, fresh_w_ne_y,
            fresh_w_ne_f, fresh_w_ne_a, or_false, and_false, not_false_eq_true])
    have dv_cache_0135 : v ∉ ((Class.cv b)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_v_ne_b, not_false_eq_true])
    have dv_cache_0136 :
      v ∉
        ((Class.cab u (synWa (.classMem (.cv u) (.cv y))
              (.classMem (.cv u) (synCima (.cv f) (.cv a)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_u, fresh_v_ne_y,
            fresh_v_ne_f, fresh_v_ne_a, or_false, and_false, not_false_eq_true])
    have dv_cache_0137 :
      b ∉
        ((Class.cab u (synWa (.classMem (.cv u) (.cv y))
              (.classMem (.cv u) (synCima (.cv f) (.cv a)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_u, fresh_b_ne_y,
            fresh_b_ne_f, fresh_b_ne_a, or_false, and_false, not_false_eq_true])
    have dv_cache_0138 :
      b ∉
        ((Wff.imp (synWa (synWss (.cab u (synWa (.classMem (.cv u) (.cv y))
                    (.classMem (.cv u) (synCima (.cv f) (.cv a))))) (.cv y)) (synWne (.cab u
                  (synWa (.classMem (.cv u) (.cv y))
                    (.classMem (.cv u) (synCima (.cv f) (.cv a))))) (synC0))) (synWrex v
              (.cab u (synWa (.classMem (.cv u) (.cv y))
                  (.classMem (.cv u) (synCima (.cv f) (.cv a))))) (synWral w (.cab u
                  (synWa (.classMem (.cv u) (.cv y))
                    (.classMem (.cv u) (synCima (.cv f) (.cv a)))))
                (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cab,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_u, fresh_b_ne_y,
            fresh_b_ne_f, fresh_b_ne_a, fresh_b_ne_w, fresh_b_ne_v, fresh_b_ne_r,
            compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
    have dv_cache_0139 :
      u ∉
        ((synWa (.classMem (.cv v) (.cv y))
            (.classMem (.cv v) (synCima (.cv f) (.cv a))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
            Finset.mem_singleton, fresh_u_ne_v, fresh_u_ne_y, fresh_u_ne_f, fresh_u_ne_a,
            or_false, not_false_eq_true])
    have dv_cache_0140 : v ≠ u := by exact (show v ≠ u from (by exact fresh_v_ne_u))
    have dv_cache_0141 :
      u ∉
        ((synWa (.classMem (.cv w) (.cv y))
            (.classMem (.cv w) (synCima (.cv f) (.cv a))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
            Finset.mem_singleton, fresh_u_ne_w, fresh_u_ne_y, fresh_u_ne_f, fresh_u_ne_a,
            or_false, not_false_eq_true])
    have dv_cache_0142 : w ≠ u := by exact (show w ≠ u from (by exact fresh_w_ne_u))
    have dv_cache_0143 :
      v ∉
        ((synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
            Finset.mem_singleton, fresh_v_ne_a, fresh_v_ne_x, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0144 :
      w ∉
        ((synWa (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
            (.classMem (.cv v) (.cv y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem, Finset.mem_union,
            Finset.mem_singleton, fresh_w_ne_a, fresh_w_ne_x, fresh_w_ne_v, fresh_w_ne_y,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0145 : c ∉ ((Wff.classEq (.cv d) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_d, fresh_c_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0146 : c ∉ ((Class.cv e)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_e, not_false_eq_true])
    have dv_cache_0147 : b ∉ ((Class.cv e)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_e, not_false_eq_true])
    have dv_cache_0148 : e ≠ b := by exact (show e ≠ b from (by exact fresh_e_ne_b))
    have dv_cache_0149 :
      d ∉
        ((synWral b (.cv y) (synWral c (.cv y) (synWo (synWbr (.cv b) (.cv r) (.cv c))
                (synWbr (.cv c) (.cv r) (.cv b)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_y, fresh_d_ne_b,
            fresh_d_ne_c, fresh_d_ne_r, or_false, and_false, not_false_eq_true])
    have dv_cache_0150 :
      e ∉
        ((synWral b (.cv y) (synWral c (.cv y) (synWo (synWbr (.cv b) (.cv r) (.cv c))
                (synWbr (.cv c) (.cv r) (.cv b)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_e_ne_y, fresh_e_ne_b,
            fresh_e_ne_c, fresh_e_ne_r, or_false, and_false, not_false_eq_true])
    have dv_cache_0151 : b ∉ ((Class.cv v)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_v, not_false_eq_true])
    have dv_cache_0152 : c ∉ ((Class.cv v)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_v, not_false_eq_true])
    have dv_cache_0153 : c ∉ ((Class.cv w)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_w, not_false_eq_true])
    have dv_cache_0154 :
      b ∉
        ((synWo (synWbr (.cv v) (.cv r) (.cv c)) (synWbr (.cv c) (.cv r) (.cv v)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_v, fresh_b_ne_c, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0155 :
      c ∉
        ((synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_v, fresh_c_ne_w, fresh_c_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0156 : b ∉ ((Class.cv w)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_w, not_false_eq_true])
    have dv_cache_0157 : b ∉ ((synWbr (.cv w) (.cv r) (.cv w))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_w, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0158 :
      w ∉
        ((synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
            Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, fresh_w_ne_f, fresh_w_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0159 :
      v ∉
        ((synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
            Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_ne_f, fresh_v_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0160 : t ∉ ((Class.cv v)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_t_ne_v, not_false_eq_true])
    have dv_cache_0161 : t ∉ ((Class.cv a)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_t_ne_a, not_false_eq_true])
    have dv_cache_0162 : t ∉ ((Class.cv f)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_t_ne_f, not_false_eq_true])
    have dv_cache_0163 :
      t ∉
        ((synWa (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
            (synWa (.classMem (.cv v) (.cv y))
              (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a))) (synWral w (.cv y)
                  (.imp (.classMem (.cv w) (synCima (.cv f) (.cv a)))
                    (synWbr (.cv v) (.cv r) (.cv w)))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_x,
            fresh_t_ne_v, fresh_t_ne_y, fresh_t_ne_f, fresh_t_ne_w, fresh_t_ne_r,
            compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
    let syntaxFormula0113 : Wff :=
      (synWa (.classMem (.cv u) (.cv y)) (.classMem (.cv u) (synCima (.cv f) (.cv a))))
    let syntaxClass0114 : Class := (.cab u syntaxFormula0113)
    let syntaxFormula0115 : Wff := (synWne syntaxClass0114 (synC0))
    let syntaxFormula0116 : Wff := (synWss syntaxClass0114 (.cv y))
    let syntaxFormula0118 : Wff := (.classMem syntaxClass0114 (synCvv))
    let syntaxFormula0119 : Wff :=
      (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.classEq (.cv w) (.cv v))))
    let syntaxFormula0120 : Wff := (synWrex v (.cv b) syntaxFormula0119)
    let syntaxFormula0121 : Wff :=
      (.imp (synWa (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0))) syntaxFormula0120)
    let syntaxFormula0122 : Wff := (.all b syntaxFormula0121)
    let syntaxFormula0123 : Wff := (synWa syntaxFormula0116 syntaxFormula0115)
    let syntaxFormula0124 : Wff :=
      (synWral w syntaxClass0114
        (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.classEq (.cv w) (.cv v))))
    let syntaxFormula0125 : Wff := (synWrex v syntaxClass0114 syntaxFormula0124)
    let syntaxFormula0126 : Wff := (.imp syntaxFormula0123 syntaxFormula0125)
    let syntaxFormula0127 : Wff := (.imp syntaxFormula0116 syntaxFormula0125)
    let syntaxFormula0128 : Wff := (.imp syntaxFormula0115 syntaxFormula0127)
    let syntaxFormula0129 : Wff := (.imp syntaxFormula0115 syntaxFormula0116)
    let syntaxFormula0130 : Wff := (.imp syntaxFormula0115 syntaxFormula0125)
    let syntaxFormula0131 : Wff := (.imp syntaxFormula0129 syntaxFormula0130)
    let syntaxFormula0132 : Wff :=
      (synWa (.classMem (.cv w) (synCima (.cv f) (.cv a))) (synWbr (.cv w) (.cv r) (.cv v)))
    let syntaxFormula0133 : Wff :=
      (synWa (.classMem (.cv w) (.cv y)) (.classMem (.cv w) (synCima (.cv f) (.cv a))))
    let syntaxFormula0134 : Wff := (.imp syntaxFormula0132 (.classEq (.cv w) (.cv v)))
    let syntaxFormula0135 : Wff := (synWral w (.cv y) syntaxFormula0134)
    let syntaxFormula0136 : Wff :=
      (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a))) syntaxFormula0135)
    let syntaxFormula0137 : Wff := (synWrex v (.cv y) syntaxFormula0136)
    let syntaxFormula0138 : Wff :=
      (synWa (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv v) (.cv y)))
    let syntaxFormula0139 : Wff :=
      (synWral c (.cv y)
        (synWo (synWbr (.cv b) (.cv r) (.cv c)) (synWbr (.cv c) (.cv r) (.cv b))))
    let syntaxFormula0140 : Wff := (synWral b (.cv y) syntaxFormula0139)
    let syntaxFormula0141 : Wff :=
      (synWa (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWa (.classMem (.cv v) (.cv y)) (.classMem (.cv w) (.cv y))))
    let syntaxFormula0142 : Wff :=
      (synWa (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv w) (.cv y)))
    let syntaxFormula0143 : Wff :=
      (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.classEq (.cv w) (.cv v)))
        (.classEq (.cv w) (.cv v)))
    let syntaxFormula0144 : Wff :=
      (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.classEq (.cv w) (.cv v)))
        (synWbr (.cv v) (.cv r) (.cv w)))
    let syntaxFormula0145 : Wff := (.imp syntaxFormula0143 syntaxFormula0144)
    let syntaxFormula0146 : Wff := (.imp syntaxFormula0141 syntaxFormula0145)
    let syntaxFormula0147 : Wff := (.imp syntaxFormula0141 syntaxFormula0143)
    let syntaxFormula0148 : Wff := (.imp syntaxFormula0141 syntaxFormula0144)
    let syntaxFormula0149 : Wff := (.imp syntaxFormula0147 syntaxFormula0148)
    let syntaxFormula0150 : Wff := (.neg syntaxFormula0148)
    let syntaxFormula0151 : Wff := (.neg syntaxFormula0150)
    let syntaxFormula0152 : Wff :=
      (.imp (.neg (synWbr (.cv v) (.cv r) (.cv w))) syntaxFormula0151)
    let syntaxFormula0153 : Wff :=
      (.imp syntaxFormula0150 (synWbr (.cv v) (.cv r) (.cv w)))
    let syntaxFormula0154 : Wff := (.imp syntaxFormula0150 syntaxFormula0148)
    let syntaxFormula0155 : Wff :=
      (.imp (.classMem (.cv w) (synCima (.cv f) (.cv a)))
        (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.classEq (.cv w) (.cv v))))
    let syntaxFormula0156 : Wff :=
      (.imp (.classMem (.cv w) (synCima (.cv f) (.cv a))) (synWbr (.cv v) (.cv r) (.cv w)))
    let syntaxFormula0157 : Wff := (.imp syntaxFormula0155 syntaxFormula0156)
    let syntaxFormula0158 : Wff := (.imp syntaxFormula0134 syntaxFormula0156)
    let syntaxFormula0159 : Wff := (.imp (.classMem (.cv w) (.cv y)) syntaxFormula0158)
    let syntaxFormula0160 : Wff := (.imp (.classMem (.cv w) (.cv y)) syntaxFormula0134)
    let syntaxFormula0161 : Wff := (.imp (.classMem (.cv w) (.cv y)) syntaxFormula0156)
    let syntaxFormula0162 : Wff := (.imp syntaxFormula0160 syntaxFormula0161)
    let syntaxFormula0163 : Wff := (.all w syntaxFormula0162)
    let syntaxFormula0164 : Wff := (.all w syntaxFormula0160)
    let syntaxFormula0165 : Wff := (.all w syntaxFormula0161)
    let syntaxFormula0166 : Wff := (.imp syntaxFormula0164 syntaxFormula0165)
    let syntaxFormula0167 : Wff := (synWral w (.cv y) syntaxFormula0156)
    let syntaxFormula0168 : Wff :=
      (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a))) syntaxFormula0167)
    let syntaxFormula0169 : Wff :=
      (.imp (.classMem (.cv v) (synCima (.cv f) (.cv a))) syntaxFormula0168)
    let syntaxFormula0170 : Wff := (.imp syntaxFormula0135 syntaxFormula0167)
    let syntaxFormula0171 : Wff := (.imp syntaxFormula0135 syntaxFormula0169)
    let syntaxFormula0172 : Wff :=
      (synWa syntaxFormula0135 (.classMem (.cv v) (synCima (.cv f) (.cv a))))
    let syntaxFormula0173 : Wff := (.imp syntaxFormula0136 syntaxFormula0168)
    let syntaxFormula0174 : Wff := (.imp (.classMem (.cv v) (.cv y)) syntaxFormula0173)
    let syntaxFormula0175 : Wff := (.all v syntaxFormula0174)
    let syntaxFormula0176 : Wff := (synWral v (.cv y) syntaxFormula0173)
    let syntaxFormula0177 : Wff := (synWrex v (.cv y) syntaxFormula0168)
    let syntaxFormula0178 : Wff := (.imp syntaxFormula0137 syntaxFormula0177)
    let syntaxFormula0179 : Wff := (synWa (.classMem (.cv v) (.cv y)) syntaxFormula0168)
    let syntaxFormula0180 : Wff :=
      (synWa (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0179)
    let syntaxFormula0181 : Wff :=
      (synWa (.classMem (.cv t) (.cv a)) (.classEq (synCfv (.cv f) (.cv t)) (.cv v)))
    let syntaxFormula0182 : Wff := (synWa syntaxFormula0180 syntaxFormula0181)
    let syntaxClass0183 : Class :=
      (synCdif (synCpwpull (.cv f) (.cv r)) (synCcnv (synCpwpull (.cv f) (.cv r))))
    let syntaxFormula0184 : Wff := (synWbr (.cv b) syntaxClass0183 (.cv t))
    let syntaxFormula0185 : Wff := (.neg syntaxFormula0184)
    let syntaxFormula0186 : Wff := (synWa syntaxFormula0182 (.classMem (.cv b) (.cv a)))
    have p0813 :=
      @gBrabg
        (.all b (.imp (synWa (synWss (.cv b) (.cv c)) (synWne (.cv b) (synC0)))
            (synWrex v (.cv b) (synWral w (.cv b)
                (.imp (synWbr (.cv w) (.cv d) (.cv v)) (.objEq w v))))))
        (.all b (.imp (synWa (synWss (.cv b) (.cv c)) (synWne (.cv b) (synC0)))
            (synWrex v (.cv b) (synWral w (.cv b)
                (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))))
        (.all b (.imp (synWa (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0)))
            (synWrex v (.cv b) (synWral w (.cv b)
                (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))))
        d c (.cv r) (.cv y) (synCvv) (synCvv) (synCfound) dv_cache_0008 dv_cache_0007
        dv_cache_0010 dv_cache_0009 dv_cache_0131 dv_cache_0132 dv_cache_0004 p0807 p0811
        p0812
    have p0814 :=
      @gSyl (synWbr (.cv r) (synCfound) (.cv y))
        (synWa (.classMem (.cv r) (synCvv)) (.classMem (.cv y) (synCvv)))
        (synWb (synWbr (.cv r) (synCfound) (.cv y)) (.all b
            (.imp (synWa (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0)))
              (synWrex v (.cv b) (synWral w (.cv b)
                  (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))))))
        p0802 p0813
    have p0815 :=
      @gIbi (synWbr (.cv r) (synCfound) (.cv y))
        (.all b (.imp (synWa (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0)))
            (synWrex v (.cv b) (synWral w (.cv b)
                (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))))
        p0814
    have p0816_e01_recanon :
      Nominal.NPrf (.imp (synWbr (.cv r) (synCfound) (.cv y)) syntaxFormula0122) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWbr, synCop, synCun, synCnin, synWnan, synWa, synCcompl,
            synWrex, synWex, synCphi, synCfound, synCopab]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_all]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
        p0815
    have p0816 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWbr (.cv r) (synCfound) (.cv y)) syntaxFormula0122 p0782 p0816_e01_recanon
    have p0817 := @gSseq1 (.cv b) syntaxClass0114 (.cv y)
    have p0818 := @gNeeq1 (.cv b) syntaxClass0114 (synC0)
    have p0819 :=
      @gAnbi12d (.classEq (.cv b) syntaxClass0114) (synWss (.cv b) (.cv y))
        syntaxFormula0116 (synWne (.cv b) (synC0)) syntaxFormula0115 p0817 p0818
    have p0820 :=
      @gRaleq (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)) w (.cv b)
        syntaxClass0114 dv_cache_0133 dv_cache_0134
    have p0821 :=
      @gRexeqbi1dv
        (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))
        (synWral w syntaxClass0114 (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))
        v (.cv b) syntaxClass0114 dv_cache_0135 dv_cache_0136 p0820
    have p0822 :=
      @gImbi12d (.classEq (.cv b) syntaxClass0114)
        (synWa (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0))) syntaxFormula0123
        (synWrex v (.cv b)
          (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))
        (synWrex v syntaxClass0114 (synWral w syntaxClass0114
            (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))
        p0819 p0821
    have p0823 :=
      @gSpcgv
        (.imp (synWa (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0))) (synWrex v (.cv b)
            (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))))
        (.imp syntaxFormula0123 (synWrex v syntaxClass0114 (synWral w syntaxClass0114
              (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))))
        b syntaxClass0114 (synCvv) dv_cache_0137 dv_cache_0138 p0822
    have p0824_e02_recanon :
      Nominal.NPrf (.imp syntaxFormula0118 (.imp syntaxFormula0122 syntaxFormula0126)) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWa, synWrex, synWex, synWbr, synCop, synCun, synCnin,
            synWnan, synCcompl, synCvv]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.all
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.all
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
        p0823
    have p0824 :=
      @gSyl6c
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0118 syntaxFormula0122 syntaxFormula0126 p0801 p0816
        p0824_e02_recanon
    have p0825 :=
      @gSyl7bi (synWa syntaxFormula0115 syntaxFormula0116) syntaxFormula0123
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0125 p0770 p0824
    have p0826 :=
      @gExp4a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0115 syntaxFormula0116 syntaxFormula0125 p0825
    have p0827 :=
      Nominal.ax2 syntaxFormula0115 syntaxFormula0116
        (synWrex v syntaxClass0114 (synWral w syntaxClass0114
            (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))
    have p0828_e01_recanon : Nominal.NPrf (.imp syntaxFormula0128 syntaxFormula0131) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWa, synWrex, synWex, synWbr, synCop, synCun, synCnin,
            synWnan, synCcompl]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.all
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.all
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
        p0827
    have p0828 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0128 syntaxFormula0131 p0826 p0828_e01_recanon
    have p0829 :=
      @gMpdi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0129 syntaxFormula0130 p0769 p0828
    have p0830 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0115 syntaxFormula0125 p0766 p0829
    have p0831 := @gEleq1 (.cv u) (.cv v) (.cv y)
    have p0832 := @gEleq1 (.cv u) (.cv v) (synCima (.cv f) (.cv a))
    have p0833_e00_recanon :
      Nominal.NPrf
        (.imp (.objEq u v) (synWb (.classMem (.cv u) (.cv y)) (.classMem (.cv v) (.cv y)))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0831
    have p0833_e01_recanon :
      Nominal.NPrf
        (.imp (.objEq u v) (synWb (.classMem (.cv u) (synCima (.cv f) (.cv a)))
            (.classMem (.cv v) (synCima (.cv f) (.cv a))))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb, synCima, synWrex, synWex, synWa, synWbr, synCop,
            synCun, synCnin, synWnan, synCcompl]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0832
    have p0833 :=
      @gAnbi12d (.objEq u v) (.classMem (.cv u) (.cv y)) (.classMem (.cv v) (.cv y))
        (.classMem (.cv u) (synCima (.cv f) (.cv a)))
        (.classMem (.cv v) (synCima (.cv f) (.cv a))) p0833_e00_recanon p0833_e01_recanon
    have p0834 :=
      @gRexab syntaxFormula0113
        (synWa (.classMem (.cv v) (.cv y)) (.classMem (.cv v) (synCima (.cv f) (.cv a))))
        (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))) v u dv_cache_0139
        dv_cache_0140 p0833
    have p0835 :=
      @gAnass (.classMem (.cv v) (.cv y)) (.classMem (.cv v) (synCima (.cv f) (.cv a)))
        (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v)))
    have p0836 :=
      @gExbii
        (synWa (synWa (.classMem (.cv v) (.cv y))
            (.classMem (.cv v) (synCima (.cv f) (.cv a))))
          (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))))
        (synWa (.classMem (.cv v) (.cv y))
          (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a)))
            (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v)))))
        v p0835
    have p0837 :=
      @gBitri
        (synWrex v syntaxClass0114 (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))))
        (synWex v (synWa (synWa (.classMem (.cv v) (.cv y))
              (.classMem (.cv v) (synCima (.cv f) (.cv a))))
            (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v)))))
        (synWex v (synWa (.classMem (.cv v) (.cv y))
            (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a)))
              (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))))))
        p0834 p0836
    have p0838 :=
      @gImpexp (.classMem (.cv w) (.cv y)) (.classMem (.cv w) (synCima (.cv f) (.cv a)))
        (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
    have p0839 :=
      @gImpexp (.classMem (.cv w) (synCima (.cv f) (.cv a)))
        (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)
    have p0840 :=
      @gImbi2i (.imp syntaxFormula0132 (.objEq w v))
        (.imp (.classMem (.cv w) (synCima (.cv f) (.cv a)))
          (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))
        (.classMem (.cv w) (.cv y)) p0839
    have p0841 :=
      @gBitr4i
        (.imp syntaxFormula0133 (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))
        (.imp (.classMem (.cv w) (.cv y)) (.imp (.classMem (.cv w) (synCima (.cv f) (.cv a)))
            (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))
        (.imp (.classMem (.cv w) (.cv y)) (.imp syntaxFormula0132 (.objEq w v))) p0838
        p0840
    have p0842 :=
      @gAlbii
        (.imp syntaxFormula0133 (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))
        (.imp (.classMem (.cv w) (.cv y)) (.imp syntaxFormula0132 (.objEq w v))) w p0841
    have p0843 := @gEleq1 (.cv u) (.cv w) (.cv y)
    have p0844 := @gEleq1 (.cv u) (.cv w) (synCima (.cv f) (.cv a))
    have p0845_e00_recanon :
      Nominal.NPrf
        (.imp (.objEq u w) (synWb (.classMem (.cv u) (.cv y)) (.classMem (.cv w) (.cv y)))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0843
    have p0845_e01_recanon :
      Nominal.NPrf
        (.imp (.objEq u w) (synWb (.classMem (.cv u) (synCima (.cv f) (.cv a)))
            (.classMem (.cv w) (synCima (.cv f) (.cv a))))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb, synCima, synWrex, synWex, synWa, synWbr, synCop,
            synCun, synCnin, synWnan, synCcompl]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0844
    have p0845 :=
      @gAnbi12d (.objEq u w) (.classMem (.cv u) (.cv y)) (.classMem (.cv w) (.cv y))
        (.classMem (.cv u) (synCima (.cv f) (.cv a)))
        (.classMem (.cv w) (synCima (.cv f) (.cv a))) p0845_e00_recanon p0845_e01_recanon
    have p0846 :=
      @gRalab syntaxFormula0113 syntaxFormula0133
        (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)) w u dv_cache_0141
        dv_cache_0142 p0845
    have p0847 :=
      (Nominal.biimpRefl (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))))
    have p0848 :=
      @gN3bitr4i
        (.all w (.imp syntaxFormula0133 (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))
        (.all w (.imp (.classMem (.cv w) (.cv y)) (.imp syntaxFormula0132 (.objEq w v))))
        (synWral w syntaxClass0114 (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))
        (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))) p0842 p0846 p0847
    have p0849 :=
      @gRexbii
        (synWral w syntaxClass0114 (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))
        (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))) v syntaxClass0114 p0848
    have p0850 :=
      (Nominal.biimpRefl (synWrex v (.cv y)
          (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a)))
            (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))))))
    have p0851 :=
      @gN3bitr4i
        (synWrex v syntaxClass0114 (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))))
        (synWex v (synWa (.classMem (.cv v) (.cv y))
            (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a)))
              (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))))))
        (synWrex v syntaxClass0114 (synWral w syntaxClass0114
            (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))
        (synWrex v (.cv y) (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a)))
            (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v)))))
        p0837 p0849 p0850
    have p0852_e01_recanon : Nominal.NPrf (synWb syntaxFormula0125 syntaxFormula0137) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb, synWrex, synWex, synWa, synWral, synWbr, synCop,
            synCun, synCnin, synWnan, synCcompl]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.all
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.all
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
        p0851
    have p0852 :=
      @gSyl6ib
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0125 syntaxFormula0137 p0830 p0852_e01_recanon
    have p0853 :=
      @gNfv
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))) v
        dv_cache_0143
    have p0854 :=
      @gNfri
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))) v
        p0853
    have p0855 :=
      @gAncom (.classMem (.cv v) (synCima (.cv f) (.cv a)))
        (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v)))
    have p0857 := @gNfv syntaxFormula0138 w dv_cache_0144
    have p0858 := @gNfri syntaxFormula0138 w p0857
    have p0860 :=
      @gSimplbi (synWbr (.cv r) (synCwe) (.cv y))
        (synWbr (.cv r) (synCstrict) (.cv y)) (synWbr (.cv r) (synCfound) (.cv y))
        p0780
    have p0861 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCstrict) (.cv y)) p0776
        p0860
    have p0862 := @gSopc (.cv y) (.cv r)
    have p0863 :=
      @gSimprbi (synWbr (.cv r) (synCstrict) (.cv y))
        (synWbr (.cv r) (synCpartial) (.cv y)) (synWbr (.cv r) (synCconnex) (.cv y))
        p0862
    have p0864 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWbr (.cv r) (synCstrict) (.cv y)) (synWbr (.cv r) (synCconnex) (.cv y))
        p0861 p0863
    have p0865 :=
      @gAdantrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWbr (.cv r) (synCconnex) (.cv y))
        (synWa (.classMem (.cv v) (.cv y)) (.classMem (.cv w) (.cv y))) p0864
    have p0867 := @gBreq (.cv b) (.cv c) (.cv d) (.cv r)
    have p0868 := @gBreq (.cv c) (.cv b) (.cv d) (.cv r)
    have p0869 :=
      @gOrbi12d (.classEq (.cv d) (.cv r)) (synWbr (.cv b) (.cv d) (.cv c))
        (synWbr (.cv b) (.cv r) (.cv c)) (synWbr (.cv c) (.cv d) (.cv b))
        (synWbr (.cv c) (.cv r) (.cv b)) p0867 p0868
    have p0870 :=
      @gN2ralbidv (.classEq (.cv d) (.cv r))
        (synWo (synWbr (.cv b) (.cv d) (.cv c)) (synWbr (.cv c) (.cv d) (.cv b)))
        (synWo (synWbr (.cv b) (.cv r) (.cv c)) (synWbr (.cv c) (.cv r) (.cv b))) b c
        (.cv e) (.cv e) dv_cache_0122 dv_cache_0145 p0869
    have p0871 :=
      @gRaleq
        (synWo (synWbr (.cv b) (.cv r) (.cv c)) (synWbr (.cv c) (.cv r) (.cv b))) c
        (.cv e) (.cv y) dv_cache_0146 dv_cache_0009
    have p0872 :=
      @gRaleqbi1dv
        (synWral c (.cv e)
          (synWo (synWbr (.cv b) (.cv r) (.cv c)) (synWbr (.cv c) (.cv r) (.cv b))))
        syntaxFormula0139 b (.cv e) (.cv y) dv_cache_0147 dv_cache_0003 p0871
    have p0873 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfConnex b c d e
        dv_cache_0097 dv_cache_0148 dv_cache_0096 dv_cache_0005 dv_cache_0004
        dv_cache_0032
    have p0874 :=
      @gBrabg
        (synWral b (.cv e) (synWral c (.cv e)
            (synWo (synWbr (.cv b) (.cv d) (.cv c)) (synWbr (.cv c) (.cv d) (.cv b)))))
        (synWral b (.cv e) (synWral c (.cv e)
            (synWo (synWbr (.cv b) (.cv r) (.cv c)) (synWbr (.cv c) (.cv r) (.cv b)))))
        syntaxFormula0140 d e (.cv r) (.cv y) (synCvv) (synCvv) (synCconnex)
        dv_cache_0008 dv_cache_0098 dv_cache_0010 dv_cache_0043 dv_cache_0149
        dv_cache_0150 dv_cache_0054 p0870 p0872 p0873
    have p0875 :=
      @gSyl (synWbr (.cv r) (synCconnex) (.cv y))
        (synWa (.classMem (.cv r) (synCvv)) (.classMem (.cv y) (synCvv)))
        (synWb (synWbr (.cv r) (synCconnex) (.cv y)) syntaxFormula0140) p0615 p0874
    have p0876 := @gIbi (synWbr (.cv r) (synCconnex) (.cv y)) syntaxFormula0140 p0875
    have p0877 :=
      @gSimprl
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv v) (.cv y)) (.classMem (.cv w) (.cv y))
    have p0878 :=
      @gSimprr
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv v) (.cv y)) (.classMem (.cv w) (.cv y))
    have p0879 := @gBreq1 (.cv b) (.cv v) (.cv c) (.cv r)
    have p0880 := @gBreq2 (.cv b) (.cv v) (.cv c) (.cv r)
    have p0881 :=
      @gOrbi12d (.classEq (.cv b) (.cv v)) (synWbr (.cv b) (.cv r) (.cv c))
        (synWbr (.cv v) (.cv r) (.cv c)) (synWbr (.cv c) (.cv r) (.cv b))
        (synWbr (.cv c) (.cv r) (.cv v)) p0879 p0880
    have p0882 := @gBreq2 (.cv c) (.cv w) (.cv v) (.cv r)
    have p0883 := @gBreq1 (.cv c) (.cv w) (.cv v) (.cv r)
    have p0884 :=
      @gOrbi12d (.classEq (.cv c) (.cv w)) (synWbr (.cv v) (.cv r) (.cv c))
        (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv c) (.cv r) (.cv v))
        (synWbr (.cv w) (.cv r) (.cv v)) p0882 p0883
    have p0885 :=
      @gRspc2v
        (synWo (synWbr (.cv b) (.cv r) (.cv c)) (synWbr (.cv c) (.cv r) (.cv b)))
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
        (synWo (synWbr (.cv v) (.cv r) (.cv c)) (synWbr (.cv c) (.cv r) (.cv v))) b c
        (.cv v) (.cv w) (.cv y) (.cv y) dv_cache_0151 dv_cache_0152 dv_cache_0153
        dv_cache_0003 dv_cache_0003 dv_cache_0009 dv_cache_0154 dv_cache_0155
        dv_cache_0032 p0881 p0884
    have p0886 :=
      @gSyl2anc syntaxFormula0141 (.classMem (.cv v) (.cv y)) (.classMem (.cv w) (.cv y))
        (.imp syntaxFormula0140
          (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v))))
        p0877 p0878 p0885
    have p0887 :=
      @gSyl5 (synWbr (.cv r) (synCconnex) (.cv y)) syntaxFormula0140 syntaxFormula0141
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v))) p0876
        p0886
    have p0888 :=
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0141 (synWbr (.cv r) (synCconnex) (.cv y))
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v))) p0865
        p0887
    have p0889 :=
      @gPm253 (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v))
    have p0890 := @gPm227 (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)
    have p0891 :=
      @gA1d (synWbr (.cv w) (.cv r) (.cv v))
        (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)) (.objEq w v))
        syntaxFormula0141 p0890
    have p0892 := @gSimpr (.classMem (.cv v) (.cv y)) (.classMem (.cv w) (.cv y))
    have p0894 :=
      @gSimp1bi (synWbr (.cv r) (synCpartial) (.cv y))
        (synWbr (.cv r) (synCref) (.cv y)) (synWbr (.cv r) (synCtrans) (.cv y))
        (synWbr (.cv r) (synCantisym) (.cv y)) p0286
    have p0895 :=
      @gAdantr (synWbr (.cv r) (synCpartial) (.cv y))
        (synWbr (.cv r) (synCref) (.cv y)) (synWbr (.cv r) (synCconnex) (.cv y)) p0894
    have p0896 :=
      @gSylbi (synWbr (.cv r) (synCstrict) (.cv y))
        (synWa (synWbr (.cv r) (synCpartial) (.cv y))
          (synWbr (.cv r) (synCconnex) (.cv y)))
        (synWbr (.cv r) (synCref) (.cv y)) p0862 p0895
    have p0897 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWbr (.cv r) (synCstrict) (.cv y)) (synWbr (.cv r) (synCref) (.cv y)) p0861
        p0896
    have p0898 :=
      @gAdantrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWbr (.cv r) (synCref) (.cv y)) (.classMem (.cv w) (.cv y)) p0897
    have p0907 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0142 (synWbr (.cv r) (synCref) (.cv y))
        (synWral b (.cv y) (synWbr (.cv b) (.cv r) (.cv b))) p0898 p0015
    have p0908 :=
      @gSimpr
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv w) (.cv y))
    have p0909 := @gId (.classEq (.cv b) (.cv w))
    have p0910 :=
      @gBreq12d (.classEq (.cv b) (.cv w)) (.cv b) (.cv w) (.cv b) (.cv w) (.cv r) p0909
        p0909
    have p0911 :=
      @gRspccv (synWbr (.cv b) (.cv r) (.cv b)) (synWbr (.cv w) (.cv r) (.cv w)) b
        (.cv w) (.cv y) dv_cache_0156 dv_cache_0003 dv_cache_0157 p0910
    have p0912 :=
      @gSyl5 syntaxFormula0142 (.classMem (.cv w) (.cv y))
        (synWral b (.cv y) (synWbr (.cv b) (.cv r) (.cv b)))
        (synWbr (.cv w) (.cv r) (.cv w)) p0908 p0911
    have p0913 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0142 (synWral b (.cv y) (synWbr (.cv b) (.cv r) (.cv b)))
        (.imp syntaxFormula0142 (synWbr (.cv w) (.cv r) (.cv w))) p0907 p0912
    have p0914 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0142 (synWbr (.cv w) (.cv r) (.cv w)) p0913
    have p0915 :=
      @gSylan2i (synWa (.classMem (.cv v) (.cv y)) (.classMem (.cv w) (.cv y)))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv w) (.cv y)) (synWbr (.cv w) (.cv r) (.cv w)) p0892 p0914
    have p0916 := @gBreq1 (.cv w) (.cv v) (.cv w) (.cv r)
    have p0917_e00_recanon :
      Nominal.NPrf
        (.imp (.objEq w v)
          (synWb (synWbr (.cv w) (.cv r) (.cv w)) (synWbr (.cv v) (.cv r) (.cv w)))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb, synWbr, synCop, synCun, synCnin, synWnan, synWa,
            synCcompl, synWrex, synWex, synCphi]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0916
    have p0917 :=
      @gBiimpd (.objEq w v) (synWbr (.cv w) (.cv r) (.cv w))
        (synWbr (.cv v) (.cv r) (.cv w)) p0917_e00_recanon
    have p0918_e01_recanon :
      Nominal.NPrf
        (.imp (.classEq (.cv w) (.cv v))
          (.imp (synWbr (.cv w) (.cv r) (.cv w)) (synWbr (.cv v) (.cv r) (.cv w)))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWbr, synCop, synCun, synCnin, synWnan, synWa, synCcompl,
            synWrex, synWex, synCphi]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0917
    have p0918 :=
      @gSyl9
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0141 (synWbr (.cv w) (.cv r) (.cv w)) (.classEq (.cv w) (.cv v))
        (synWbr (.cv v) (.cv r) (.cv w)) p0915 p0918_e01_recanon
    have p0919 :=
      @gCom23
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classEq (.cv w) (.cv v)) syntaxFormula0141 (synWbr (.cv v) (.cv r) (.cv w))
        p0918
    have p0920 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.imp syntaxFormula0141
          (.imp (.classEq (.cv w) (.cv v)) (synWbr (.cv v) (.cv r) (.cv w))))
        (synWbr (.cv w) (.cv r) (.cv v)) p0919
    have p0921 :=
      @gImim2 (.objEq w v) (synWbr (.cv v) (.cv r) (.cv w))
        (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
    have p0922_e01_recanon :
      Nominal.NPrf
        (.imp (.imp (.classEq (.cv w) (.cv v)) (synWbr (.cv v) (.cv r) (.cv w)))
          syntaxFormula0145) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWbr, synCop, synCun, synCnin, synWnan, synWa, synCcompl,
            synWrex, synWex, synCphi]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0921
    have p0922 :=
      @gSyl8
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv w) (.cv r) (.cv v)) syntaxFormula0141
        (.imp (.classEq (.cv w) (.cv v)) (synWbr (.cv v) (.cv r) (.cv w)))
        syntaxFormula0145 p0920 p0922_e01_recanon
    have p0923 :=
      Nominal.ax2 syntaxFormula0141
        (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)) (.objEq w v))
        (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
          (synWbr (.cv v) (.cv r) (.cv w)))
    have p0924_e01_recanon : Nominal.NPrf (.imp syntaxFormula0146 syntaxFormula0149) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWa, synWbr, synCop, synCun, synCnin, synWnan, synCcompl,
            synWrex, synWex, synCphi]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0923
    have p0924 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv w) (.cv r) (.cv v)) syntaxFormula0146 syntaxFormula0149 p0922
        p0924_e01_recanon
    have p0925_e00_recanon :
      Nominal.NPrf (.imp (synWbr (.cv w) (.cv r) (.cv v)) syntaxFormula0147) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWbr, synCop, synCun, synCnin, synWnan, synWa, synCcompl,
            synWrex, synWex, synCphi]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
        p0891
    have p0925 :=
      @gMpdi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv w) (.cv r) (.cv v)) syntaxFormula0147 syntaxFormula0148
        p0925_e00_recanon p0924
    have p0926 :=
      @gCom23
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv w) (.cv r) (.cv v)) syntaxFormula0141 syntaxFormula0144 p0925
    have p0927 :=
      @gCom23
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0141 (synWbr (.cv w) (.cv r) (.cv v)) syntaxFormula0144 p0926
    have p0928 :=
      @gSyl9r
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
        (.neg (synWbr (.cv v) (.cv r) (.cv w))) (synWbr (.cv w) (.cv r) (.cv v))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0148 p0889 p0927
    have p0929 :=
      @gNotnot1
        (.imp syntaxFormula0141 (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
            (synWbr (.cv v) (.cv r) (.cv w))))
    have p0930_e01_recanon : Nominal.NPrf (.imp syntaxFormula0148 syntaxFormula0151) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWa, synWbr, synCop, synCun, synCnin, synWnan, synCcompl,
            synWrex, synWex, synCphi]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0929
    have p0930 :=
      @gSyl8
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
        (.neg (synWbr (.cv v) (.cv r) (.cv w))) syntaxFormula0148 syntaxFormula0151 p0928
        p0930_e01_recanon
    have p0931 :=
      Nominal.ax3 (synWbr (.cv v) (.cv r) (.cv w))
        (.neg (.imp syntaxFormula0141
            (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
              (synWbr (.cv v) (.cv r) (.cv w)))))
    have p0932_e01_recanon : Nominal.NPrf (.imp syntaxFormula0152 syntaxFormula0153) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWbr, synCop, synCun, synCnin, synWnan, synWa, synCcompl,
            synWrex, synWex, synCphi]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0931
    have p0932 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
        syntaxFormula0152 syntaxFormula0153 p0930 p0932_e01_recanon
    have p0933 :=
      @gAx1 (synWbr (.cv v) (.cv r) (.cv w))
        (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
    have p0934 :=
      @gA1i
        (.imp (synWbr (.cv v) (.cv r) (.cv w))
          (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
            (synWbr (.cv v) (.cv r) (.cv w))))
        syntaxFormula0141 p0933
    have p0935 :=
      @gCom12 syntaxFormula0141 (synWbr (.cv v) (.cv r) (.cv w))
        (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
          (synWbr (.cv v) (.cv r) (.cv w)))
        p0934
    have p0936 :=
      @gA1i
        (.imp (synWbr (.cv v) (.cv r) (.cv w)) (.imp syntaxFormula0141
            (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
              (synWbr (.cv v) (.cv r) (.cv w)))))
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v))) p0935
    have p0937 :=
      @gA1d (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
        (.imp (synWbr (.cv v) (.cv r) (.cv w)) (.imp syntaxFormula0141
            (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
              (synWbr (.cv v) (.cv r) (.cv w)))))
        (.neg (.imp syntaxFormula0141
            (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
              (synWbr (.cv v) (.cv r) (.cv w)))))
        p0936
    have p0938 :=
      @gA2d (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
        (.neg (.imp syntaxFormula0141
            (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
              (synWbr (.cv v) (.cv r) (.cv w)))))
        (synWbr (.cv v) (.cv r) (.cv w))
        (.imp syntaxFormula0141 (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
            (synWbr (.cv v) (.cv r) (.cv w))))
        p0937
    have p0939_e01_recanon :
      Nominal.NPrf
        (.imp (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
          (.imp syntaxFormula0153 syntaxFormula0154)) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWo, synWbr, synCop, synCun, synCnin, synWnan, synWa,
            synCcompl, synWrex, synWex, synCphi]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0938
    have p0939 :=
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
        syntaxFormula0153 syntaxFormula0154 p0932 p0939_e01_recanon
    have p0940 :=
      @gPm218
        (.imp syntaxFormula0141 (.imp (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
            (synWbr (.cv v) (.cv r) (.cv w))))
    have p0941_e01_recanon : Nominal.NPrf (.imp syntaxFormula0154 syntaxFormula0148) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWa, synWbr, synCop, synCun, synCnin, synWnan, synCcompl,
            synWrex, synWex, synCphi]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0940
    have p0941 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
        syntaxFormula0154 syntaxFormula0148 p0939 p0941_e01_recanon
    have p0942 :=
      @gCom23
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
        syntaxFormula0141 syntaxFormula0144 p0941
    have p0943 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0141
        (synWo (synWbr (.cv v) (.cv r) (.cv w)) (synWbr (.cv w) (.cv r) (.cv v)))
        syntaxFormula0144 p0888 p0942
    have p0944 :=
      @gA1dd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0141 syntaxFormula0144 (.classMem (.cv w) (synCima (.cv f) (.cv a)))
        p0943
    have p0945 :=
      Nominal.ax2 (.classMem (.cv w) (synCima (.cv f) (.cv a)))
        (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))
        (synWbr (.cv v) (.cv r) (.cv w))
    have p0946_e01_recanon :
      Nominal.NPrf
        (.imp (.imp (.classMem (.cv w) (synCima (.cv f) (.cv a))) syntaxFormula0144)
          syntaxFormula0157) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synCima, synWrex, synWex, synWa, synWbr, synCop, synCun,
            synCnin, synWnan, synCcompl]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0945
    have p0946 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0141
        (.imp (.classMem (.cv w) (synCima (.cv f) (.cv a))) syntaxFormula0144)
        syntaxFormula0157 p0944 p0946_e01_recanon
    have p0947_e00_recanon : Nominal.NPrf (synWb syntaxFormula0134 syntaxFormula0155) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb, synWa, synCima, synWrex, synWex, synWbr, synCop,
            synCun, synCnin, synWnan, synCcompl]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
        p0839
    have p0947 :=
      @gSyl7bi syntaxFormula0134 syntaxFormula0155
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0141 syntaxFormula0156 p0947_e00_recanon p0946
    have p0948 :=
      @gExp4d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv v) (.cv y)) (.classMem (.cv w) (.cv y)) syntaxFormula0158 p0947
    have p0949 :=
      @gImp4c
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv v) (.cv y)) (.classMem (.cv w) (.cv y)) syntaxFormula0158 p0948
    have p0950 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0138 (.classMem (.cv w) (.cv y)) syntaxFormula0158 p0949
    have p0951 :=
      Nominal.ax2 (.classMem (.cv w) (.cv y)) (.imp syntaxFormula0132 (.objEq w v))
        syntaxFormula0156
    have p0952_e01_recanon : Nominal.NPrf (.imp syntaxFormula0159 syntaxFormula0162) :=
      Nominal.RecanonTransportDev.transport
        (by
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0951
    have p0952 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0138 syntaxFormula0159 syntaxFormula0162 p0950 p0952_e01_recanon
    have p0953 :=
      @gAlimdv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0138 syntaxFormula0162 w dv_cache_0158 p0952
    have p0954 :=
      @gAlim (.imp (.classMem (.cv w) (.cv y)) (.imp syntaxFormula0132 (.objEq w v)))
        syntaxFormula0161 w
    have p0955_e01_recanon : Nominal.NPrf (.imp syntaxFormula0163 syntaxFormula0166) :=
      Nominal.RecanonTransportDev.transport
        (by
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0954
    have p0955 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.all w syntaxFormula0138) syntaxFormula0163 syntaxFormula0166 p0953
        p0955_e01_recanon
    have p0956 :=
      @gSyl5 syntaxFormula0138 (.all w syntaxFormula0138)
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0166 p0858 p0955
    have p0957_e00_recanon : Nominal.NPrf (synWb syntaxFormula0135 syntaxFormula0164) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb, synWral]
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
        p0847
    have p0957 :=
      @gSyl7bi syntaxFormula0135 syntaxFormula0164
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0138 syntaxFormula0165 p0957_e00_recanon p0956
    have p0958 := (Nominal.biimpRefl syntaxFormula0167)
    have p0959 := @gBiimpri syntaxFormula0167 syntaxFormula0165 p0958
    have p0960 :=
      @gSyl8
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0138 syntaxFormula0135 syntaxFormula0165 syntaxFormula0167 p0957
        p0959
    have p0961 := @gIdd syntaxFormula0138 syntaxFormula0168
    have p0962 :=
      @gAncomsd syntaxFormula0138 (.classMem (.cv v) (synCima (.cv f) (.cv a)))
        syntaxFormula0167 syntaxFormula0168 p0961
    have p0963 :=
      @gExp3a syntaxFormula0138 syntaxFormula0167
        (.classMem (.cv v) (synCima (.cv f) (.cv a))) syntaxFormula0168 p0962
    have p0964 :=
      @gA1d syntaxFormula0138 (.imp syntaxFormula0167 syntaxFormula0169)
        (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))) p0963
    have p0965 :=
      @gA2d syntaxFormula0138 (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v)))
        syntaxFormula0167 syntaxFormula0169 p0964
    have p0966_e01_recanon :
      Nominal.NPrf (.imp syntaxFormula0138 (.imp syntaxFormula0170 syntaxFormula0171)) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWral]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0965
    have p0966 :=
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0138 syntaxFormula0170 syntaxFormula0171 p0960 p0966_e01_recanon
    have p0967 :=
      @gImp4a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0138 syntaxFormula0135 (.classMem (.cv v) (synCima (.cv f) (.cv a)))
        syntaxFormula0168 p0966
    have p0968_e00_recanon : Nominal.NPrf (synWb syntaxFormula0136 syntaxFormula0172) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb, synWa, synCima, synWrex, synWex, synWbr, synCop,
            synCun, synCnin, synWnan, synCcompl, synWral]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
        p0855
    have p0968 :=
      @gSyl7bi syntaxFormula0136 syntaxFormula0172
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0138 syntaxFormula0168 p0968_e00_recanon p0967
    have p0969 := @gIdd syntaxFormula0138 (.classMem (.cv v) (synCima (.cv f) (.cv a)))
    have p0970 :=
      @gA1ii
        (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
          (.imp syntaxFormula0138 syntaxFormula0173))
        (.imp syntaxFormula0138 (.imp (.classMem (.cv v) (synCima (.cv f) (.cv a)))
            (.classMem (.cv v) (synCima (.cv f) (.cv a)))))
        p0968 p0969
    have p0971 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv v) (.cv y)) syntaxFormula0173 p0970
    have p0972 :=
      @gAlimdv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0174 v dv_cache_0159 p0971
    have p0973 :=
      @gSyl5
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.all v (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0175 p0854 p0972
    have p0974 :=
      (Nominal.biimpRefl (synWral v (.cv y) (.imp
            (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a)))
              (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v)))) syntaxFormula0168)))
    have p0975_e01_recanon : Nominal.NPrf (synWb syntaxFormula0176 syntaxFormula0175) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWb, synWral, synWa, synCima, synWrex, synWex, synWbr,
            synCop, synCun, synCnin, synWnan, synCcompl]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                    apply Nominal.RecanonTransportDev.TRecanonWff.all
                    apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                      · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                      · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                    apply Nominal.RecanonTransportDev.TRecanonWff.all
                    apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                      · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                      · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                    apply Nominal.RecanonTransportDev.TRecanonWff.all
                    apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                      · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                      · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                    apply Nominal.RecanonTransportDev.TRecanonWff.all
                    apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                      · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                      · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0974
    have p0975 :=
      @gSyl6ibr
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0175 syntaxFormula0176 p0973 p0975_e01_recanon
    have p0976 :=
      @gRexim
        (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a)))
          (synWral w (.cv y) (.imp syntaxFormula0132 (.objEq w v))))
        syntaxFormula0168 v (.cv y)
    have p0977_e01_recanon : Nominal.NPrf (.imp syntaxFormula0176 syntaxFormula0178) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWral, synWa, synCima, synWrex, synWex, synWbr, synCop,
            synCun, synCnin, synWnan, synCcompl]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.all
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.all
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0976
    have p0977 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0176 syntaxFormula0178 p0975 p0977_e01_recanon
    have p0978 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0137 syntaxFormula0177 p0852 p0977
    have p0981 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (.cv f)) syntaxFormula0180 p0042
    have p0982 :=
      @gSimpr
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0179
    have p0983 := @gSimpr (.classMem (.cv v) (.cv y)) syntaxFormula0168
    have p0984 := @gSyl syntaxFormula0180 syntaxFormula0179 syntaxFormula0168 p0982 p0983
    have p0985 :=
      @gSimpl (.classMem (.cv v) (synCima (.cv f) (.cv a))) syntaxFormula0167
    have p0986 :=
      @gSyl syntaxFormula0180 syntaxFormula0168
        (.classMem (.cv v) (synCima (.cv f) (.cv a))) p0984 p0985
    have p0987 :=
      @g_pm3_2 (synWfun (.cv f)) (.classMem (.cv v) (synCima (.cv f) (.cv a)))
    have p0988 :=
      @gSyl5 syntaxFormula0180 (.classMem (.cv v) (synCima (.cv f) (.cv a)))
        (synWfun (.cv f))
        (synWa (synWfun (.cv f)) (.classMem (.cv v) (synCima (.cv f) (.cv a)))) p0986
        p0987
    have p0989 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0180 (synWfun (.cv f))
        (.imp syntaxFormula0180
          (synWa (synWfun (.cv f)) (.classMem (.cv v) (synCima (.cv f) (.cv a)))))
        p0981 p0988
    have p0990 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0180
        (synWa (synWfun (.cv f)) (.classMem (.cv v) (synCima (.cv f) (.cv a)))) p0989
    have p0991 :=
      @gFvelima t (.cv v) (.cv a) (.cv f) dv_cache_0160 dv_cache_0161 dv_cache_0162
    have p0992 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0180
        (synWa (synWfun (.cv f)) (.classMem (.cv v) (synCima (.cv f) (.cv a))))
        (synWrex t (.cv a) (.classEq (synCfv (.cv f) (.cv t)) (.cv v))) p0990 p0991
    have p0993 := @gNfv syntaxFormula0180 t dv_cache_0163
    have p0994 := @gNfri syntaxFormula0180 t p0993
    have p0995 := @gSimpr syntaxFormula0180 syntaxFormula0181
    have p0996 :=
      @gSimpl (.classMem (.cv t) (.cv a)) (.classEq (synCfv (.cv f) (.cv t)) (.cv v))
    have p0997 :=
      @gSyl syntaxFormula0182 syntaxFormula0181 (.classMem (.cv t) (.cv a)) p0995 p0996
    have p0998 := @gId syntaxFormula0185
    have p0999 :=
      @gA1i (.imp syntaxFormula0185 syntaxFormula0185) syntaxFormula0186 p0998
    have p1000 := @gCon1d syntaxFormula0186 syntaxFormula0184 syntaxFormula0185 p0999
    exact continuation p0854 p0978 p0984 p0992 p0994 p0995 p0997 p1000

end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `ReplaySupport.WellOrderPullback5`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_pwpullwesetimpndv_stage5`. -/
@[expose]
noncomputable def gPwpullwesetimpndvStage5 (x : Var) (y : Var) (f : Var) (r : Var)
    (p0000 : _) (p0036 : _) (p0038 : _) (p0039 : _) (p0042 : _) (p0045 : _) (p0047 : _)
    (p0049 : _) (p0050 : _) (p0055 : _) (p0058 : _) (p0081 : _) (p0101 : _) (p0114 : _)
    (p0117 : _) (p0162 : _) (p0169 : _) (p0185 : _) (p0193 : _) (p0201 : _) (p0318 : _)
    (p0709 : _) (p0854 : _) (p0978 : _) (p0984 : _) (p0992 : _) (p0994 : _) (p0995 : _)
    (p0997 : _) (p1000 : _) {Result : Type} (continuation : _ → _ → _ → Result) :=
  show Result from
    by
    let proofSupport : Finset Var :=
      ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ f } : Finset Var) ∪
        ({ r } : Finset Var)
    let a : Var := freshVar proofSupport 0
    let b : Var := freshVar proofSupport 1
    let c : Var := freshVar proofSupport 2
    let d : Var := freshVar proofSupport 3
    let g : Var := freshVar proofSupport 4
    let z : Var := freshVar proofSupport 5
    let h : Var := freshVar proofSupport 7
    let u : Var := freshVar proofSupport 8
    let v : Var := freshVar proofSupport 9
    let w : Var := freshVar proofSupport 10
    let t : Var := freshVar proofSupport 11
    have fresh_a : a ∉ proofSupport :=
      by
      change freshVar proofSupport 0 ∉ proofSupport
      exact freshVar_not_mem proofSupport 0
    have fresh_a_ne_x : a ≠ x := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_a_ne_y : a ≠ y := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_a_ne_f : a ≠ f := by
      intro h
      exact
        fresh_a
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_a_ne_r : a ≠ r := by
      intro h
      exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_b : b ∉ proofSupport :=
      by
      change freshVar proofSupport 1 ∉ proofSupport
      exact freshVar_not_mem proofSupport 1
    have fresh_b_ne_x : b ≠ x := by
      intro h
      exact
        fresh_b
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_b_ne_y : b ≠ y := by
      intro h
      exact
        fresh_b
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_b_ne_f : b ≠ f := by
      intro h
      exact
        fresh_b
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_b_ne_r : b ≠ r := by
      intro h
      exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_c : c ∉ proofSupport :=
      by
      change freshVar proofSupport 2 ∉ proofSupport
      exact freshVar_not_mem proofSupport 2
    have fresh_c_ne_x : c ≠ x := by
      intro h
      exact
        fresh_c
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_c_ne_f : c ≠ f := by
      intro h
      exact
        fresh_c
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_c_ne_r : c ≠ r := by
      intro h
      exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_d : d ∉ proofSupport :=
      by
      change freshVar proofSupport 3 ∉ proofSupport
      exact freshVar_not_mem proofSupport 3
    have fresh_d_ne_x : d ≠ x := by
      intro h
      exact
        fresh_d
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_d_ne_f : d ≠ f := by
      intro h
      exact
        fresh_d
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_d_ne_r : d ≠ r := by
      intro h
      exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_g : g ∉ proofSupport :=
      by
      change freshVar proofSupport 4 ∉ proofSupport
      exact freshVar_not_mem proofSupport 4
    have fresh_g_ne_f : g ≠ f := by
      intro h
      exact
        fresh_g
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_g_ne_r : g ≠ r := by
      intro h
      exact fresh_g (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_z : z ∉ proofSupport :=
      by
      change freshVar proofSupport 5 ∉ proofSupport
      exact freshVar_not_mem proofSupport 5
    have fresh_z_ne_f : z ≠ f := by
      intro h
      exact
        fresh_z
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_z_ne_r : z ≠ r := by
      intro h
      exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_v : v ∉ proofSupport :=
      by
      change freshVar proofSupport 9 ∉ proofSupport
      exact freshVar_not_mem proofSupport 9
    have fresh_v_ne_x : v ≠ x := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_v_ne_y : v ≠ y := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_v_ne_f : v ≠ f := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_v_ne_r : v ≠ r := by
      intro h
      exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_w : w ∉ proofSupport :=
      by
      change freshVar proofSupport 10 ∉ proofSupport
      exact freshVar_not_mem proofSupport 10
    have fresh_w_ne_y : w ≠ y := by
      intro h
      exact
        fresh_w
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_w_ne_f : w ≠ f := by
      intro h
      exact
        fresh_w
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_w_ne_r : w ≠ r := by
      intro h
      exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_t : t ∉ proofSupport :=
      by
      change freshVar proofSupport 11 ∉ proofSupport
      exact freshVar_not_mem proofSupport 11
    have fresh_t_ne_x : t ≠ x := by
      intro h
      exact
        fresh_t
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_t_ne_y : t ≠ y := by
      intro h
      exact
        fresh_t
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_t_ne_f : t ≠ f := by
      intro h
      exact
        fresh_t
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_t_ne_r : t ≠ r := by
      intro h
      exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_a_ne_b : a ≠ b :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 1
      exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
    have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
    have fresh_a_ne_c : a ≠ c :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 2
      exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
    have fresh_c_ne_a : c ≠ a := Ne.symm fresh_a_ne_c
    have fresh_a_ne_d : a ≠ d :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
    have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
    have fresh_a_ne_z : a ≠ z :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
    have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
    have fresh_a_ne_v : a ≠ v :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 0) (j := 9) (by decide)
    have fresh_v_ne_a : v ≠ a := Ne.symm fresh_a_ne_v
    have fresh_a_ne_w : a ≠ w :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 0) (j := 10) (by decide)
    have fresh_w_ne_a : w ≠ a := Ne.symm fresh_a_ne_w
    have fresh_a_ne_t : a ≠ t :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 0) (j := 11) (by decide)
    have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
    have fresh_b_ne_c : b ≠ c :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 2
      exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
    have fresh_c_ne_b : c ≠ b := Ne.symm fresh_b_ne_c
    have fresh_b_ne_d : b ≠ d :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
    have fresh_d_ne_b : d ≠ b := Ne.symm fresh_b_ne_d
    have fresh_b_ne_g : b ≠ g :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
    have fresh_g_ne_b : g ≠ b := Ne.symm fresh_b_ne_g
    have fresh_b_ne_z : b ≠ z :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
    have fresh_z_ne_b : z ≠ b := Ne.symm fresh_b_ne_z
    have fresh_b_ne_v : b ≠ v :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
    have fresh_v_ne_b : v ≠ b := Ne.symm fresh_b_ne_v
    have fresh_b_ne_w : b ≠ w :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 1) (j := 10) (by decide)
    have fresh_w_ne_b : w ≠ b := Ne.symm fresh_b_ne_w
    have fresh_b_ne_t : b ≠ t :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 1) (j := 11) (by decide)
    have fresh_t_ne_b : t ≠ b := Ne.symm fresh_b_ne_t
    have fresh_c_ne_d : c ≠ d :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
    have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
    have fresh_c_ne_z : c ≠ z :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
    have fresh_z_ne_c : z ≠ c := Ne.symm fresh_c_ne_z
    have fresh_c_ne_v : c ≠ v :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 2) (j := 9) (by decide)
    have fresh_v_ne_c : v ≠ c := Ne.symm fresh_c_ne_v
    have fresh_d_ne_z : d ≠ z :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
    have fresh_z_ne_d : z ≠ d := Ne.symm fresh_d_ne_z
    have fresh_g_ne_t : g ≠ t :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 4) (j := 11) (by decide)
    have fresh_z_ne_v : z ≠ v :=
      by
      change freshVar proofSupport 5 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 5) (j := 9) (by decide)
    have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
    have fresh_z_ne_t : z ≠ t :=
      by
      change freshVar proofSupport 5 ≠ freshVar proofSupport 11
      exact freshVar_injective proofSupport (i := 5) (j := 11) (by decide)
    have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
    have fresh_v_ne_w : v ≠ w :=
      by
      change freshVar proofSupport 9 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 9) (j := 10) (by decide)
    have fresh_w_ne_v : w ≠ v := Ne.symm fresh_v_ne_w
    have dv_cache_0004 : d ≠ c := by exact (show d ≠ c from (by exact fresh_d_ne_c))
    have dv_cache_0005 : d ≠ b := by exact (show d ≠ b from (by exact fresh_d_ne_b))
    have dv_cache_0006 : c ≠ b := by exact (show c ≠ b from (by exact fresh_c_ne_b))
    have dv_cache_0013 : c ≠ d := by exact (show c ≠ d from (by exact fresh_c_ne_d))
    have dv_cache_0017 : g ∉ ((synCcnv (.cv f))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_g_ne_f,
            not_false_eq_true])
    have dv_cache_0019 :
      a ∉
        ((synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, fresh_a_ne_f, fresh_a_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0020 : a ∉ (synWtru).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0024 : c ≠ a := by exact (show c ≠ a from (by exact fresh_c_ne_a))
    have dv_cache_0029 : c ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_x, not_false_eq_true])
    have dv_cache_0035 : g ≠ b := by exact (show g ≠ b from (by exact fresh_g_ne_b))
    have dv_cache_0073 :
      b ∉
        ((synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, fresh_b_ne_f, fresh_b_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0075 : a ≠ b := by exact (show a ≠ b from (by exact fresh_a_ne_b))
    have dv_cache_0082 : d ≠ a := by exact (show d ≠ a from (by exact fresh_d_ne_a))
    have dv_cache_0083 : d ≠ z := by exact (show d ≠ z from (by exact fresh_d_ne_z))
    have dv_cache_0084 : c ≠ z := by exact (show c ≠ z from (by exact fresh_c_ne_z))
    have dv_cache_0085 : a ≠ z := by exact (show a ≠ z from (by exact fresh_a_ne_z))
    have dv_cache_0086 : b ≠ z := by exact (show b ≠ z from (by exact fresh_b_ne_z))
    have dv_cache_0088 : d ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_d_ne_x, not_false_eq_true])
    have dv_cache_0159 :
      v ∉
        ((synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
            Finset.mem_singleton, fresh_v_ne_x, fresh_v_ne_y, fresh_v_ne_f, fresh_v_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0164 : g ≠ t := by exact (show g ≠ t from (by exact fresh_g_ne_t))
    have dv_cache_0165 :
      g ∉
        ((Wff.imp (synWfun (synCcnv (synCcnv (.cv f)))) (synWb (synWbr (.cv b)
                (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
                (.cv t)) (synWa (synWa (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
                  (.classMem (.cv t) (synCrn (synCcnv (.cv f)))))
                (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (.cv r)
                  (synCfv (synCcnv (synCcnv (.cv f))) (.cv t))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
            Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_b, fresh_g_ne_t, fresh_g_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0166 :
      g ∉
        ((Wff.imp (synWfun (synCcnv (synCcnv (.cv f)))) (synWb (synWbr (.cv t)
                (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
                (.cv b)) (synWa (synWa (.classMem (.cv t) (synCrn (synCcnv (.cv f))))
                  (.classMem (.cv b) (synCrn (synCcnv (.cv f)))))
                (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv t)) (.cv r)
                  (synCfv (synCcnv (synCcnv (.cv f))) (.cv b))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wfun,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
            Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_t, fresh_g_ne_b, fresh_g_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0167 : w ∉ ((synCfv (.cv f) (.cv b))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_w_ne_b, fresh_w_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0168 : w ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_w_ne_y, not_false_eq_true])
    have dv_cache_0169 :
      w ∉
        ((Wff.imp (.classMem (synCfv (.cv f) (.cv b)) (synCima (.cv f) (.cv a)))
            (synWbr (.cv v) (.cv r) (synCfv (.cv f) (.cv b))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_singleton, fresh_w_ne_b, fresh_w_ne_f, fresh_w_ne_a, fresh_w_ne_v,
            fresh_w_ne_r, or_false, not_false_eq_true])
    have dv_cache_0170 :
      b ∉
        ((synWa (synWa (synWa synWtru
                (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
              (synWa (.classMem (.cv v) (.cv y))
                (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a))) (synWral w (.cv y)
                    (.imp (.classMem (.cv w) (synCima (.cv f) (.cv a)))
                      (synWbr (.cv v) (.cv r) (.cv w))))))) (synWa (.classMem (.cv t) (.cv a))
              (.classEq (synCfv (.cv f) (.cv t)) (.cv v))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_x,
            fresh_b_ne_v, fresh_b_ne_y, fresh_b_ne_f, fresh_b_ne_w, fresh_b_ne_r,
            fresh_b_ne_t, compact_fv_not_mem_empty, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0171 : b ∉ ((Wff.classEq (.cv z) (.cv t))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_t, or_false,
            not_false_eq_true])
    have dv_cache_0172 : z ∉ ((Class.cv t)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_z_ne_t, not_false_eq_true])
    have dv_cache_0173 : z ∉ ((Class.cv a)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_z_ne_a, not_false_eq_true])
    have dv_cache_0174 :
      z ∉
        ((synWral b (.cv a) (.imp (synWbr (.cv b) (synCdif (synCpwpull (.cv f) (.cv r))
                  (synCcnv (synCpwpull (.cv f) (.cv r)))) (.cv t))
              (.classEq (.cv b) (.cv t))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_b,
            fresh_z_ne_t, fresh_z_ne_f, fresh_z_ne_r, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0175 :
      t ∉
        ((synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
            Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_ne_f, fresh_t_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0176 :
      t ∉
        ((synWrex z (.cv a) (synWral b (.cv a) (.imp (synWbr (.cv b)
                  (synCdif (synCpwpull (.cv f) (.cv r))
                    (synCcnv (synCpwpull (.cv f) (.cv r)))) (.cv z))
                (.classEq (.cv b) (.cv z)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_b,
            fresh_t_ne_z, fresh_t_ne_f, fresh_t_ne_r, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0177 :
      v ∉
        ((synWrex z (.cv a) (synWral b (.cv a) (.imp (synWbr (.cv b)
                  (synCdif (synCpwpull (.cv f) (.cv r))
                    (synCcnv (synCpwpull (.cv f) (.cv r)))) (.cv z))
                (.classEq (.cv b) (.cv z)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_v_ne_a, fresh_v_ne_b,
            fresh_v_ne_z, fresh_v_ne_f, fresh_v_ne_r, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0178 :
      z ∉
        ((Wff.classEq (.cv d) (synCdif (synCpwpull (.cv f) (.cv r))
              (synCcnv (synCpwpull (.cv f) (.cv r)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_d, fresh_z_ne_f, fresh_z_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0179 :
      b ∉
        ((Wff.classEq (.cv d) (synCdif (synCpwpull (.cv f) (.cv r))
              (synCcnv (synCpwpull (.cv f) (.cv r)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_d, fresh_b_ne_f, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0180 :
      a ∉
        ((Wff.classEq (.cv d) (synCdif (synCpwpull (.cv f) (.cv r))
              (synCcnv (synCpwpull (.cv f) (.cv r)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_d, fresh_a_ne_f, fresh_a_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0181 : a ∉ ((Wff.classEq (.cv c) (.cv x))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_c, fresh_a_ne_x, or_false,
            not_false_eq_true])
    have dv_cache_0182 :
      d ∉
        ((synCdif (synCpwpull (.cv f) (.cv r))
            (synCcnv (synCpwpull (.cv f) (.cv r))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_f, fresh_d_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0183 :
      c ∉
        ((synCdif (synCpwpull (.cv f) (.cv r))
            (synCcnv (synCpwpull (.cv f) (.cv r))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_f, fresh_c_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0184 :
      d ∉
        ((Wff.all a (.imp (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))
              (synWrex z (.cv a) (synWral b (.cv a) (.imp (synWbr (.cv b)
                      (synCdif (synCpwpull (.cv f) (.cv r))
                        (synCcnv (synCpwpull (.cv f) (.cv r)))) (.cv z))
                    (.classEq (.cv b) (.cv z)))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_x,
            fresh_d_ne_b, fresh_d_ne_z, fresh_d_ne_f, fresh_d_ne_r,
            compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
    have dv_cache_0185 :
      c ∉
        ((Wff.all a (.imp (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))
              (synWrex z (.cv a) (synWral b (.cv a) (.imp (synWbr (.cv b)
                      (synCdif (synCpwpull (.cv f) (.cv r))
                        (synCcnv (synCpwpull (.cv f) (.cv r)))) (.cv z))
                    (.classEq (.cv b) (.cv z)))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_x,
            fresh_c_ne_b, fresh_c_ne_z, fresh_c_ne_f, fresh_c_ne_r,
            compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
    have dv_cache_0186 :
      z ∉
        ((Wff.classEq (.cv c) (synCdif (synCpwpull (.cv f) (.cv r))
              (synCcnv (synCpwpull (.cv f) (.cv r)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_c, fresh_z_ne_f, fresh_z_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0187 :
      v ∉
        ((Wff.classEq (.cv c) (synCdif (synCpwpull (.cv f) (.cv r))
              (synCcnv (synCpwpull (.cv f) (.cv r)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
            Finset.mem_singleton, fresh_v_ne_c, fresh_v_ne_f, fresh_v_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0188 :
      a ∉
        ((Wff.classEq (.cv c) (synCdif (synCpwpull (.cv f) (.cv r))
              (synCcnv (synCpwpull (.cv f) (.cv r)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_c, fresh_a_ne_f, fresh_a_ne_r, or_false,
            not_false_eq_true])
    let syntaxFormula0156 : Wff :=
      (.imp (.classMem (.cv w) (synCima (.cv f) (.cv a))) (synWbr (.cv v) (.cv r) (.cv w)))
    let syntaxFormula0167 : Wff := (synWral w (.cv y) syntaxFormula0156)
    let syntaxFormula0168 : Wff :=
      (synWa (.classMem (.cv v) (synCima (.cv f) (.cv a))) syntaxFormula0167)
    let syntaxFormula0177 : Wff := (synWrex v (.cv y) syntaxFormula0168)
    let syntaxFormula0179 : Wff := (synWa (.classMem (.cv v) (.cv y)) syntaxFormula0168)
    let syntaxFormula0180 : Wff :=
      (synWa (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0179)
    let syntaxFormula0181 : Wff :=
      (synWa (.classMem (.cv t) (.cv a)) (.classEq (synCfv (.cv f) (.cv t)) (.cv v)))
    let syntaxFormula0182 : Wff := (synWa syntaxFormula0180 syntaxFormula0181)
    let syntaxClass0183 : Class :=
      (synCdif (synCpwpull (.cv f) (.cv r)) (synCcnv (synCpwpull (.cv f) (.cv r))))
    let syntaxFormula0184 : Wff := (synWbr (.cv b) syntaxClass0183 (.cv t))
    let syntaxFormula0185 : Wff := (.neg syntaxFormula0184)
    let syntaxFormula0186 : Wff := (synWa syntaxFormula0182 (.classMem (.cv b) (.cv a)))
    let syntaxFormula0187 : Wff :=
      (synWa (.classMem (.cv b) (synCrn (.cv g))) (.classMem (.cv t) (synCrn (.cv g))))
    let syntaxFormula0188 : Wff :=
      (synWa (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv t) (synCrn (synCcnv (.cv f)))))
    let syntaxFormula0189 : Wff :=
      (synWbr (synCfv (synCcnv (.cv g)) (.cv b)) (.cv r)
        (synCfv (synCcnv (.cv g)) (.cv t)))
    let syntaxFormula0190 : Wff :=
      (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (.cv r)
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv t)))
    let syntaxFormula0191 : Wff :=
      (synWbr (.cv b)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f)))) (.cv t))
    let syntaxFormula0192 : Wff := (synWa syntaxFormula0187 syntaxFormula0189)
    let syntaxFormula0193 : Wff := (synWa syntaxFormula0188 syntaxFormula0190)
    let syntaxFormula0194 : Wff :=
      (synWb (synWbr (.cv b) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv t))
        syntaxFormula0192)
    let syntaxFormula0195 : Wff := (synWb syntaxFormula0191 syntaxFormula0193)
    let syntaxFormula0196 : Wff :=
      (synWa (.classMem (.cv b) (synCdm (.cv f))) (.classMem (.cv t) (synCdm (.cv f))))
    let syntaxFormula0197 : Wff :=
      (synWa syntaxFormula0196
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t))))
    let syntaxFormula0198 : Wff :=
      (synWa (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t))))
    let syntaxFormula0199 : Wff :=
      (synWa (.classMem (.cv t) (synCrn (.cv g))) (.classMem (.cv b) (synCrn (.cv g))))
    let syntaxFormula0200 : Wff :=
      (synWa (.classMem (.cv t) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv b) (synCrn (synCcnv (.cv f)))))
    let syntaxFormula0201 : Wff :=
      (synWbr (synCfv (synCcnv (.cv g)) (.cv t)) (.cv r)
        (synCfv (synCcnv (.cv g)) (.cv b)))
    let syntaxFormula0202 : Wff :=
      (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv t)) (.cv r)
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)))
    let syntaxFormula0203 : Wff :=
      (synWbr (.cv t)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f)))) (.cv b))
    let syntaxFormula0204 : Wff := (synWa syntaxFormula0199 syntaxFormula0201)
    let syntaxFormula0205 : Wff := (synWa syntaxFormula0200 syntaxFormula0202)
    let syntaxFormula0206 : Wff :=
      (synWb (synWbr (.cv t) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv b))
        syntaxFormula0204)
    let syntaxFormula0207 : Wff := (synWb syntaxFormula0203 syntaxFormula0205)
    let syntaxFormula0208 : Wff :=
      (synWa (.classMem (.cv t) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
    let syntaxFormula0209 : Wff :=
      (synWa syntaxFormula0208
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))))
    let syntaxFormula0210 : Wff :=
      (synWa (synWa (.classMem (.cv t) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))))
    let syntaxFormula0211 : Wff := (.neg syntaxFormula0210)
    let syntaxFormula0212 : Wff := (synWa syntaxFormula0198 syntaxFormula0211)
    let syntaxFormula0213 : Wff :=
      (synWa (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))))
    let syntaxFormula0214 : Wff := (.neg syntaxFormula0213)
    let syntaxFormula0215 : Wff := (synWa syntaxFormula0198 syntaxFormula0214)
    let syntaxFormula0216 : Wff :=
      (synWa (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t)))
        (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))))
    let syntaxFormula0217 : Wff :=
      (synWa (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x)))
        syntaxFormula0216)
    let syntaxFormula0218 : Wff :=
      (synWa (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0167)
    let syntaxFormula0219 : Wff := (.neg syntaxFormula0185)
    let syntaxFormula0220 : Wff := (.imp syntaxFormula0184 syntaxFormula0185)
    let syntaxFormula0221 : Wff := (.imp syntaxFormula0219 syntaxFormula0184)
    let syntaxFormula0222 : Wff := (.imp syntaxFormula0219 syntaxFormula0185)
    let syntaxFormula0223 : Wff := (.imp syntaxFormula0184 (.classEq (.cv b) (.cv t)))
    let syntaxFormula0224 : Wff := (synWral b (.cv a) syntaxFormula0223)
    let syntaxFormula0225 : Wff := (synWa (.classMem (.cv t) (.cv a)) syntaxFormula0224)
    let syntaxFormula0226 : Wff := (synWbr (.cv b) syntaxClass0183 (.cv z))
    let syntaxFormula0227 : Wff := (.imp syntaxFormula0226 (.classEq (.cv b) (.cv z)))
    let syntaxFormula0228 : Wff := (synWral b (.cv a) syntaxFormula0227)
    let syntaxFormula0229 : Wff := (synWrex z (.cv a) syntaxFormula0228)
    let syntaxFormula0230 : Wff :=
      (.imp (.classEq (synCfv (.cv f) (.cv t)) (.cv v)) syntaxFormula0229)
    let syntaxFormula0231 : Wff := (.imp (.classMem (.cv t) (.cv a)) syntaxFormula0230)
    let syntaxFormula0232 : Wff := (.all t syntaxFormula0231)
    let syntaxFormula0233 : Wff := (synWral t (.cv a) syntaxFormula0230)
    let syntaxFormula0234 : Wff := (.imp syntaxFormula0168 syntaxFormula0229)
    let syntaxFormula0235 : Wff := (.imp (.classMem (.cv v) (.cv y)) syntaxFormula0234)
    let syntaxFormula0236 : Wff := (.all v syntaxFormula0235)
    let syntaxFormula0237 : Wff := (synWral v (.cv y) syntaxFormula0234)
    let syntaxFormula0238 : Wff :=
      (.imp (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))) syntaxFormula0229)
    let syntaxFormula0239 : Wff := (.classMem syntaxClass0183 (synCvv))
    let syntaxFormula0240 : Wff := (.classEq (.cv d) syntaxClass0183)
    let syntaxFormula0241 : Wff :=
      (synWral b (.cv a) (.imp (synWbr (.cv b) (.cv d) (.cv z)) (.classEq (.cv b) (.cv z))))
    let syntaxFormula0242 : Wff := (synWrex z (.cv a) syntaxFormula0241)
    let syntaxFormula0243 : Wff :=
      (.imp (synWa (synWss (.cv a) (.cv c)) (synWne (.cv a) (synC0))) syntaxFormula0242)
    let syntaxFormula0244 : Wff :=
      (.imp (synWa (synWss (.cv a) (.cv c)) (synWne (.cv a) (synC0))) syntaxFormula0229)
    let syntaxFormula0245 : Wff := (.all a syntaxFormula0243)
    let syntaxFormula0246 : Wff := (.all a syntaxFormula0238)
    let syntaxFormula0247 : Wff := (synWbr syntaxClass0183 (synCfound) (.cv x))
    let syntaxFormula0248 : Wff := (.classEq (.cv c) syntaxClass0183)
    let syntaxFormula0249 : Wff := (synWbr (.cv v) syntaxClass0183 (.cv z))
    have p1001 :=
      @gBrdif (.cv b) (.cv t) (synCpwpull (.cv f) (.cv r))
        (synCcnv (synCpwpull (.cv f) (.cv r)))
    have p1003 :=
      @gBreqi (.cv b) (.cv t) (synCpwpull (.cv f) (.cv r))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p1006 :=
      @gBreqi (.cv b) (.cv t)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p1016 :=
      @gBreqd (.classEq (.cv g) (synCcnv (.cv f)))
        (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g)))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (.cv b) (.cv t) p0055
    have p1022 :=
      @gEleq2d (.classEq (.cv g) (synCcnv (.cv f))) (synCrn (.cv g))
        (synCrn (synCcnv (.cv f))) (.cv t) p0058
    have p1023 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (.classMem (.cv b) (synCrn (.cv g)))
        (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv t) (synCrn (.cv g)))
        (.classMem (.cv t) (synCrn (synCcnv (.cv f)))) p0162 p1022
    have p1029 :=
      @gFveq1d (.classEq (.cv g) (synCcnv (.cv f))) (.cv t) (synCcnv (.cv g))
        (synCcnv (synCcnv (.cv f))) p0049
    have p1030 :=
      @gBreq12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synCfv (synCcnv (.cv g)) (.cv b))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv b))
        (synCfv (synCcnv (.cv g)) (.cv t))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv t)) (.cv r) p0169 p1029
    have p1031 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f))) syntaxFormula0187 syntaxFormula0188
        syntaxFormula0189 syntaxFormula0190 p1023 p1030
    have p1032 :=
      @gBibi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synWbr (.cv b) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv t))
        syntaxFormula0191 syntaxFormula0192 syntaxFormula0193 p1016 p1031
    have p1033 :=
      @gImbi12d (.classEq (.cv g) (synCcnv (.cv f))) (synWfun (synCcnv (.cv g)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0194 syntaxFormula0195 p0050
        p1032
    have p1034 := @gHwtrnbrd b t g r dv_cache_0035 dv_cache_0164
    have p1035 :=
      @gVtoclg (.imp (synWfun (synCcnv (.cv g))) syntaxFormula0194)
        (.imp (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0195) g
        (synCcnv (.cv f)) (synCvv) dv_cache_0017 dv_cache_0165 p1033 p1034
    have p1036 := Nominal.mp p0047 p1035
    have p1037 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0195 p0045 p1036
    have p1047 := @gEleq2i (synCrn (synCcnv (.cv f))) (synCdm (.cv f)) (.cv t) p0081
    have p1048 :=
      @gAnbi12i (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv b) (synCdm (.cv f)))
        (.classMem (.cv t) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv t) (synCdm (.cv f))) p0185 p1047
    have p1052 := @gFveq1i (.cv t) (synCcnv (synCcnv (.cv f))) (.cv f) p0038
    have p1053 :=
      @gBreq12i (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (synCfv (.cv f) (.cv b))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv t)) (synCfv (.cv f) (.cv t)) (.cv r)
        p0193 p1052
    have p1054 :=
      @gAnbi12i syntaxFormula0188 syntaxFormula0196 syntaxFormula0190
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t))) p1048 p1053
    have p1055 :=
      @gSyl6bb
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0191 syntaxFormula0193 syntaxFormula0197 p1037 p1054
    have p1056 :=
      @gSyl5bbr
        (synWbr (.cv b) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv t))
        syntaxFormula0191
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0197 p1006 p1055
    have p1057 :=
      @gSyl5bb (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv t))
        (synWbr (.cv b) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv t))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0197 p1003 p1056
    have p1058 :=
      @gEleq2d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synCdm (.cv f)) (.cv x) (.cv t) p0101
    have p1059 :=
      @gAnbi12d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv b) (synCdm (.cv f))) (.classMem (.cv b) (.cv x))
        (.classMem (.cv t) (synCdm (.cv f))) (.classMem (.cv t) (.cv x)) p0201 p1058
    have p1060 :=
      @gAnbi1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0196 (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t))) p1059
    have p1061 :=
      @gBiid (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t)))
    have p1062 :=
      @gAnbi2i (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t)))
        (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x))) p1061
    have p1063 :=
      @gA1ii
        (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
          (synWb syntaxFormula0197 syntaxFormula0198))
        (synWb syntaxFormula0198 syntaxFormula0198) p1060 p1062
    have p1064 :=
      @gBitrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv t)) syntaxFormula0197
        syntaxFormula0198 p1057 p1063
    have p1065 := @gBrcnv (.cv b) (.cv t) (synCpwpull (.cv f) (.cv r))
    have p1066 :=
      @gNotbii (synWbr (.cv b) (synCcnv (synCpwpull (.cv f) (.cv r))) (.cv t))
        (synWbr (.cv t) (synCpwpull (.cv f) (.cv r)) (.cv b)) p1065
    have p1068 :=
      @gBreqi (.cv t) (.cv b) (synCpwpull (.cv f) (.cv r))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p1071 :=
      @gBreqi (.cv t) (.cv b)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p1081 :=
      @gBreqd (.classEq (.cv g) (synCcnv (.cv f)))
        (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g)))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (.cv t) (.cv b) p0055
    have p1088 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (.classMem (.cv t) (synCrn (.cv g)))
        (.classMem (.cv t) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv b) (synCrn (.cv g)))
        (.classMem (.cv b) (synCrn (synCcnv (.cv f)))) p1022 p0162
    have p1095 :=
      @gBreq12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synCfv (synCcnv (.cv g)) (.cv t))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv t))
        (synCfv (synCcnv (.cv g)) (.cv b))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (.cv r) p1029 p0169
    have p1096 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f))) syntaxFormula0199 syntaxFormula0200
        syntaxFormula0201 syntaxFormula0202 p1088 p1095
    have p1097 :=
      @gBibi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synWbr (.cv t) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv b))
        syntaxFormula0203 syntaxFormula0204 syntaxFormula0205 p1081 p1096
    have p1098 :=
      @gImbi12d (.classEq (.cv g) (synCcnv (.cv f))) (synWfun (synCcnv (.cv g)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0206 syntaxFormula0207 p0050
        p1097
    have p1099 := @gHwtrnbrd t b g r dv_cache_0164 dv_cache_0035
    have p1100 :=
      @gVtoclg (.imp (synWfun (synCcnv (.cv g))) syntaxFormula0206)
        (.imp (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0207) g
        (synCcnv (.cv f)) (synCvv) dv_cache_0017 dv_cache_0166 p1098 p1099
    have p1101 := Nominal.mp p0047 p1100
    have p1102 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0207 p0045 p1101
    have p1113 :=
      @gAnbi12i (.classMem (.cv t) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv t) (synCdm (.cv f)))
        (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv b) (synCdm (.cv f))) p1047 p0185
    have p1118 :=
      @gBreq12i (synCfv (synCcnv (synCcnv (.cv f))) (.cv t)) (synCfv (.cv f) (.cv t))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (synCfv (.cv f) (.cv b)) (.cv r)
        p1052 p0193
    have p1119 :=
      @gAnbi12i syntaxFormula0200 syntaxFormula0208 syntaxFormula0202
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))) p1113 p1118
    have p1120 :=
      @gSyl6bb
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0203 syntaxFormula0205 syntaxFormula0209 p1102 p1119
    have p1121 :=
      @gSyl5bbr
        (synWbr (.cv t) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv b))
        syntaxFormula0203
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0209 p1071 p1120
    have p1122 :=
      @gSyl5bb (synWbr (.cv t) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv t) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv b))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0209 p1068 p1121
    have p1123 :=
      @gAnbi12d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv t) (synCdm (.cv f))) (.classMem (.cv t) (.cv x))
        (.classMem (.cv b) (synCdm (.cv f))) (.classMem (.cv b) (.cv x)) p1058 p0201
    have p1124 :=
      @gAnbi1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0208 (synWa (.classMem (.cv t) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))) p1123
    have p1125 :=
      @gBiid (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
    have p1126 :=
      @gAnbi2i (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWa (.classMem (.cv t) (.cv x)) (.classMem (.cv b) (.cv x))) p1125
    have p1127 :=
      @gA1ii
        (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
          (synWb syntaxFormula0209 syntaxFormula0210))
        (synWb syntaxFormula0210 syntaxFormula0210) p1124 p1126
    have p1128 :=
      @gBitrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv t) (synCpwpull (.cv f) (.cv r)) (.cv b)) syntaxFormula0209
        syntaxFormula0210 p1122 p1127
    have p1129 :=
      @gNotbid
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv t) (synCpwpull (.cv f) (.cv r)) (.cv b)) syntaxFormula0210 p1128
    have p1130 :=
      @gSyl5bb (.neg (synWbr (.cv b) (synCcnv (synCpwpull (.cv f) (.cv r))) (.cv t)))
        (.neg (synWbr (.cv t) (synCpwpull (.cv f) (.cv r)) (.cv b)))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0211 p1066 p1129
    have p1131 :=
      @gAnbi12d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv t)) syntaxFormula0198
        (.neg (synWbr (.cv b) (synCcnv (synCpwpull (.cv f) (.cv r))) (.cv t)))
        syntaxFormula0211 p1064 p1130
    have p1132 :=
      @gSyl5bb syntaxFormula0184
        (synWa (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv t))
          (.neg (synWbr (.cv b) (synCcnv (synCpwpull (.cv f) (.cv r))) (.cv t))))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0212 p1001 p1131
    have p1133 := @gAncom (.classMem (.cv t) (.cv x)) (.classMem (.cv b) (.cv x))
    have p1134 :=
      @gAnbi1i (synWa (.classMem (.cv t) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))) p1133
    have p1135 := @gNotbii syntaxFormula0210 syntaxFormula0213 p1134
    have p1136 := @gAnbi2i syntaxFormula0211 syntaxFormula0214 syntaxFormula0198 p1135
    have p1137 :=
      @gSyl6bb
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0184 syntaxFormula0212 syntaxFormula0215 p1132 p1136
    have p1138 :=
      @gSimpl (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t)))
    have p1139 :=
      Nominal.ax1 (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
    have p1140 :=
      @gSyl syntaxFormula0198
        (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x)))
        (.imp (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
          (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x))))
        p1138 p1139
    have p1141 :=
      @gPm471rd syntaxFormula0198
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x))) p1140
    have p1142 :=
      @gNotbid syntaxFormula0198
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
        syntaxFormula0213 p1141
    have p1143 :=
      @gBicomd syntaxFormula0198
        (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))))
        syntaxFormula0214 p1142
    have p1144 :=
      @gPm532i syntaxFormula0198 syntaxFormula0214
        (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))) p1143
    have p1145 :=
      @gAnass (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t)))
        (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))))
    have p1146 :=
      @gBitri syntaxFormula0215
        (synWa syntaxFormula0198
          (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))))
        syntaxFormula0217 p1144 p1145
    have p1147 :=
      @gSyl6bb
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0184 syntaxFormula0215 syntaxFormula0217 p1137 p1146
    have p1148 :=
      @gBiimpd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0184 syntaxFormula0217 p1147
    have p1149 :=
      @gSimpr (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv t) (.cv x)))
        syntaxFormula0216
    have p1150 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0184 syntaxFormula0217 syntaxFormula0216 p1148 p1149
    have p1151 :=
      @gSimpr (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv t)))
        (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))))
    have p1152 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0184 syntaxFormula0216
        (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))) p1150
        p1151
    have p1153 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.imp syntaxFormula0184
          (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))))
        syntaxFormula0186 p1152
    have p1154 := @gNotnot2 syntaxFormula0184
    have p1155 := @gSimpr syntaxFormula0182 (.classMem (.cv b) (.cv a))
    have p1156 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (.cv f)) syntaxFormula0186 p0042
    have p1157 := @gSimpl syntaxFormula0182 (.classMem (.cv b) (.cv a))
    have p1158 := @gSimpl syntaxFormula0180 syntaxFormula0181
    have p1159 := @gSyl syntaxFormula0186 syntaxFormula0182 syntaxFormula0180 p1157 p1158
    have p1160 :=
      @gSimpl
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0179
    have p1161 :=
      @gSyl syntaxFormula0186 syntaxFormula0180
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        p1159 p1160
    have p1165 :=
      @gSyl syntaxFormula0186
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWss (.cv a) (.cv x)) p1161 p0709
    have p1167 :=
      @gJca syntaxFormula0186 (synWss (.cv a) (.cv x)) (.classMem (.cv b) (.cv a)) p1165
        p1155
    have p1168 := @gSsel2 (.cv a) (.cv x) (.cv b)
    have p1169 :=
      @gSyl syntaxFormula0186
        (synWa (synWss (.cv a) (.cv x)) (.classMem (.cv b) (.cv a)))
        (.classMem (.cv b) (.cv x)) p1167 p1168
    have p1170 :=
      @gBiimprd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv b) (synCdm (.cv f))) (.classMem (.cv b) (.cv x)) p0201
    have p1171 :=
      @gSyl5 syntaxFormula0186 (.classMem (.cv b) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv b) (synCdm (.cv f))) p1169 p1170
    have p1172 :=
      @gJcad
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 (synWfun (.cv f)) (.classMem (.cv b) (synCdm (.cv f))) p1156
        p1171
    have p1173 := @gFunfvima (.cv a) (.cv b) (.cv f)
    have p1174 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186
        (synWa (synWfun (.cv f)) (.classMem (.cv b) (synCdm (.cv f))))
        (.imp (.classMem (.cv b) (.cv a))
          (.classMem (synCfv (.cv f) (.cv b)) (synCima (.cv f) (.cv a))))
        p1172 p1173
    have p1175 :=
      @gMpdi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 (.classMem (.cv b) (.cv a))
        (.classMem (synCfv (.cv f) (.cv b)) (synCima (.cv f) (.cv a))) p1155 p1174
    have p1189 :=
      @gSyl5 syntaxFormula0186 (.classMem (.cv b) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) p1169 p0318
    have p1195 :=
      @gSimpr (.classMem (.cv v) (synCima (.cv f) (.cv a))) syntaxFormula0167
    have p1196 := @gSyl syntaxFormula0180 syntaxFormula0168 syntaxFormula0167 p0984 p1195
    have p1197 := @gSyl syntaxFormula0182 syntaxFormula0180 syntaxFormula0167 p1158 p1196
    have p1198 := @gSyl syntaxFormula0186 syntaxFormula0182 syntaxFormula0167 p1157 p1197
    have p1199 := @g_pm3_2 (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0167
    have p1200 :=
      @gSyl5 syntaxFormula0186 syntaxFormula0167
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0218 p1198 p1199
    have p1201 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 (.classMem (synCfv (.cv f) (.cv b)) (.cv y))
        (.imp syntaxFormula0186 syntaxFormula0218) p1189 p1200
    have p1202 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 syntaxFormula0218 p1201
    have p1203 := @gEleq1 (.cv w) (synCfv (.cv f) (.cv b)) (synCima (.cv f) (.cv a))
    have p1204 := @gBreq2 (.cv w) (synCfv (.cv f) (.cv b)) (.cv v) (.cv r)
    have p1205 :=
      @gImbi12d (.classEq (.cv w) (synCfv (.cv f) (.cv b)))
        (.classMem (.cv w) (synCima (.cv f) (.cv a)))
        (.classMem (synCfv (.cv f) (.cv b)) (synCima (.cv f) (.cv a)))
        (synWbr (.cv v) (.cv r) (.cv w))
        (synWbr (.cv v) (.cv r) (synCfv (.cv f) (.cv b))) p1203 p1204
    have p1206 :=
      @gRspcva syntaxFormula0156
        (.imp (.classMem (synCfv (.cv f) (.cv b)) (synCima (.cv f) (.cv a)))
          (synWbr (.cv v) (.cv r) (synCfv (.cv f) (.cv b))))
        w (synCfv (.cv f) (.cv b)) (.cv y) dv_cache_0167 dv_cache_0168 dv_cache_0169
        p1205
    have p1207 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 syntaxFormula0218
        (.imp (.classMem (synCfv (.cv f) (.cv b)) (synCima (.cv f) (.cv a)))
          (synWbr (.cv v) (.cv r) (synCfv (.cv f) (.cv b))))
        p1202 p1206
    have p1208 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 (.classMem (synCfv (.cv f) (.cv b)) (synCima (.cv f) (.cv a)))
        (synWbr (.cv v) (.cv r) (synCfv (.cv f) (.cv b))) p1175 p1207
    have p1211 :=
      @gSimpr (.classMem (.cv t) (.cv a)) (.classEq (synCfv (.cv f) (.cv t)) (.cv v))
    have p1212 :=
      @gSyl syntaxFormula0182 syntaxFormula0181
        (.classEq (synCfv (.cv f) (.cv t)) (.cv v)) p0995 p1211
    have p1213 :=
      @gSyl syntaxFormula0186 syntaxFormula0182
        (.classEq (synCfv (.cv f) (.cv t)) (.cv v)) p1157 p1212
    have p1214 :=
      @gBreq1d syntaxFormula0186 (synCfv (.cv f) (.cv t)) (.cv v)
        (synCfv (.cv f) (.cv b)) (.cv r) p1213
    have p1215 :=
      @gBiimprd syntaxFormula0186
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (.cv v) (.cv r) (synCfv (.cv f) (.cv b))) p1214
    have p1216 :=
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 (synWbr (.cv v) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))) p1208 p1215
    have p1217 :=
      @gA1dd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
        syntaxFormula0184 p1216
    have p1218 :=
      @gSyl7 syntaxFormula0219 syntaxFormula0184
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))) p1154 p1217
    have p1219 :=
      @gNotnot1 (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
    have p1220 :=
      @gSyl8
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 syntaxFormula0219
        (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))
        (.neg (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b)))))
        p1218 p1219
    have p1221 :=
      Nominal.ax3 syntaxFormula0185
        (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))))
    have p1222 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186
        (.imp syntaxFormula0219 (.neg
            (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))))))
        (.imp (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))))
          syntaxFormula0185)
        p1220 p1221
    have p1223 :=
      @gSyldd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 syntaxFormula0184
        (.neg (synWbr (synCfv (.cv f) (.cv t)) (.cv r) (synCfv (.cv f) (.cv b))))
        syntaxFormula0185 p1153 p1222
    have p1224 :=
      @gA1dd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 syntaxFormula0220 syntaxFormula0219 p1223
    have p1225 := Nominal.ax2 syntaxFormula0219 syntaxFormula0184 syntaxFormula0185
    have p1226 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 (.imp syntaxFormula0219 syntaxFormula0220)
        (.imp syntaxFormula0221 syntaxFormula0222) p1224 p1225
    have p1227 :=
      @gMpdi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 syntaxFormula0221 syntaxFormula0222 p1000 p1226
    have p1228 := @gPm218 syntaxFormula0185
    have p1229 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 syntaxFormula0222 syntaxFormula0185 p1227 p1228
    have p1230 :=
      @gA1dd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 syntaxFormula0185 (.neg (.classEq (.cv b) (.cv t))) p1229
    have p1231 := Nominal.ax3 (.classEq (.cv b) (.cv t)) syntaxFormula0184
    have p1232 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0186 (.imp (.neg (.classEq (.cv b) (.cv t))) syntaxFormula0185)
        syntaxFormula0223 p1230 p1231
    have p1233 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0182 (.classMem (.cv b) (.cv a)) syntaxFormula0223 p1232
    have p1234 :=
      @gRalrimdv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0182 syntaxFormula0223 b (.cv a) dv_cache_0073 dv_cache_0170 p1233
    have p1235 := @g_pm3_2 (.classMem (.cv t) (.cv a)) syntaxFormula0224
    have p1236 :=
      @gSyl9
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0182 syntaxFormula0224 (.classMem (.cv t) (.cv a)) syntaxFormula0225
        p1234 p1235
    have p1237 :=
      @gSyl5 syntaxFormula0182 (.classMem (.cv t) (.cv a))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.imp syntaxFormula0182 syntaxFormula0225) p0997 p1236
    have p1238 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0182 syntaxFormula0225 p1237
    have p1239 := @gId (.classEq (.cv z) (.cv t))
    have p1240 :=
      @gBreq2d (.classEq (.cv z) (.cv t)) (.cv z) (.cv t) (.cv b) syntaxClass0183 p1239
    have p1242 := @gEqeq2d (.classEq (.cv z) (.cv t)) (.cv z) (.cv t) (.cv b) p1239
    have p1243 :=
      @gImbi12d (.classEq (.cv z) (.cv t)) syntaxFormula0226 syntaxFormula0184
        (.classEq (.cv b) (.cv z)) (.classEq (.cv b) (.cv t)) p1240 p1242
    have p1244 :=
      @gRalbidv (.classEq (.cv z) (.cv t)) syntaxFormula0227 syntaxFormula0223 b (.cv a)
        dv_cache_0171 p1243
    have p1245 :=
      @gRspcev syntaxFormula0228 syntaxFormula0224 z (.cv t) (.cv a) dv_cache_0172
        dv_cache_0173 dv_cache_0174 p1244
    have p1246 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0182 syntaxFormula0225 syntaxFormula0229 p1238 p1245
    have p1247 :=
      @gExp4d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0180 (.classMem (.cv t) (.cv a))
        (.classEq (synCfv (.cv f) (.cv t)) (.cv v)) syntaxFormula0229 p1246
    have p1248 :=
      @gImp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0180 (.classMem (.cv t) (.cv a)) syntaxFormula0230 p1247
    have p1249 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0180 (.classMem (.cv t) (.cv a)) syntaxFormula0230 p1248
    have p1250 :=
      @gAlimdv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0180 syntaxFormula0231 t dv_cache_0175 p1249
    have p1251 :=
      @gSyl5 syntaxFormula0180 (.all t syntaxFormula0180)
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0232 p0994 p1250
    have p1252 := (Nominal.biimpRefl syntaxFormula0233)
    have p1253 :=
      @gSyl6ibr
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0180 syntaxFormula0232 syntaxFormula0233 p1251 p1252
    have p1254 := @gNfv syntaxFormula0229 t dv_cache_0176
    have p1255 :=
      @gR1923 (.classEq (synCfv (.cv f) (.cv t)) (.cv v)) syntaxFormula0229 t (.cv a)
        p1254
    have p1256 :=
      @gSyl6ib
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0180 syntaxFormula0233
        (.imp (synWrex t (.cv a) (.classEq (synCfv (.cv f) (.cv t)) (.cv v)))
          syntaxFormula0229)
        p1253 p1255
    have p1257 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0180
        (synWrex t (.cv a) (.classEq (synCfv (.cv f) (.cv t)) (.cv v)))
        syntaxFormula0229 p0992 p1256
    have p1258 :=
      @gExp4d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv v) (.cv y)) syntaxFormula0168 syntaxFormula0229 p1257
    have p1259 :=
      @gImp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv v) (.cv y)) syntaxFormula0234 p1258
    have p1260 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv v) (.cv y)) syntaxFormula0234 p1259
    have p1261 :=
      @gAlimdv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0235 v dv_cache_0159 p1260
    have p1262 :=
      @gSyl5
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.all v (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0236 p0854 p1261
    have p1263 := (Nominal.biimpRefl syntaxFormula0237)
    have p1264 :=
      @gSyl6ibr
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0236 syntaxFormula0237 p1262 p1263
    have p1265 := @gNfv syntaxFormula0229 v dv_cache_0177
    have p1266 := @gR1923 syntaxFormula0168 syntaxFormula0229 v (.cv y) p1265
    have p1267 :=
      @gSyl6ib
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0237 (.imp syntaxFormula0177 syntaxFormula0229) p1264 p1266
    have p1268 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0177 syntaxFormula0229 p0978 p1267
    have p1269 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))
        syntaxFormula0229 p1268
    have p1270 :=
      @gAlrimdv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0238 a dv_cache_0019 dv_cache_0020 p1269
    have p1273 := @gCnvex (synCpwpull (.cv f) (.cv r)) p0114
    have p1274 :=
      @gDifex (synCpwpull (.cv f) (.cv r)) (synCcnv (synCpwpull (.cv f) (.cv r)))
        p0114 p1273
    have p1275 := @gA1i syntaxFormula0239 synWtru p1274
    have p1277 :=
      @gJca synWtru syntaxFormula0239 (.classMem (.cv x) (synCvv)) p1275 p0117
    have p1278 := @gBreq (.cv b) (.cv z) (.cv d) syntaxClass0183
    have p1279 :=
      @gImbi1d syntaxFormula0240 (synWbr (.cv b) (.cv d) (.cv z)) syntaxFormula0226
        (.classEq (.cv b) (.cv z)) p1278
    have p1280 :=
      @gRexralbidv syntaxFormula0240
        (.imp (synWbr (.cv b) (.cv d) (.cv z)) (.classEq (.cv b) (.cv z)))
        syntaxFormula0227 z b (.cv a) (.cv a) dv_cache_0178 dv_cache_0179 p1279
    have p1281 :=
      @gImbi2d syntaxFormula0240 syntaxFormula0242 syntaxFormula0229
        (synWa (synWss (.cv a) (.cv c)) (synWne (.cv a) (synC0))) p1280
    have p1282 :=
      @gAlbidv syntaxFormula0240 syntaxFormula0243 syntaxFormula0244 a dv_cache_0180
        p1281
    have p1283 := @gSseq2 (.cv c) (.cv x) (.cv a)
    have p1284 :=
      @gAnbi1d (.classEq (.cv c) (.cv x)) (synWss (.cv a) (.cv c))
        (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)) p1283
    have p1285 :=
      @gImbi1d (.classEq (.cv c) (.cv x))
        (synWa (synWss (.cv a) (.cv c)) (synWne (.cv a) (synC0)))
        (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))) syntaxFormula0229
        p1284
    have p1286 :=
      @gAlbidv (.classEq (.cv c) (.cv x)) syntaxFormula0244 syntaxFormula0238 a
        dv_cache_0181 p1285
    have p1287 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFound a b z d c
        dv_cache_0013 dv_cache_0024 dv_cache_0006 dv_cache_0084 dv_cache_0082
        dv_cache_0005 dv_cache_0083 dv_cache_0075 dv_cache_0085 dv_cache_0086
    have p1288_e02_recanon :
      Nominal.NPrf (.classEq (synCfound) (synCopab d c syntaxFormula0245)) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synCfound, synCopab, synWex, synWa, synWss, synCin, synCcompl,
            synCnin, synWnan, synWne, synC0, synCdif, synCvv, synWrex, synWral,
            synWbr, synCop, synCun]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.classEq
          · exact Nominal.RecanonTransportDev.TRecanonClass.same _
          · apply Nominal.RecanonTransportDev.TRecanonClass.cab
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.neg
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.neg
                  apply Nominal.RecanonTransportDev.TRecanonWff.all
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
        p1287
    have p1288 :=
      @gBrabg syntaxFormula0245 (.all a syntaxFormula0244) syntaxFormula0246 d c
        syntaxClass0183 (.cv x) (synCvv) (synCvv) (synCfound) dv_cache_0182
        dv_cache_0183 dv_cache_0088 dv_cache_0029 dv_cache_0184 dv_cache_0185
        dv_cache_0004 p1282 p1286 p1288_e02_recanon
    have p1289 :=
      @gSyl synWtru (synWa syntaxFormula0239 (.classMem (.cv x) (synCvv)))
        (synWb syntaxFormula0247 syntaxFormula0246) p1277 p1288
    have p1290 := @gBiimprd synWtru syntaxFormula0247 syntaxFormula0246 p1289
    have p1291 :=
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0246 syntaxFormula0247 p1270 p1290
    have p1292 :=
      @gMpi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0247 p0000 p1291
    have p1293 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0247
        (synWa synWtru (synWa (synWss (.cv u) (.cv x)) (synWne (.cv u) (synC0))))
        p1292
    have p1294 := @gBrex syntaxClass0183 (.cv x) (synCfound)
    have p1295 := @gBreq (.cv v) (.cv z) (.cv c) syntaxClass0183
    have p1296 :=
      @gImbi1d syntaxFormula0248 (synWbr (.cv v) (.cv c) (.cv z)) syntaxFormula0249
        (.objEq v z) p1295
    have p1297 :=
      @gRexralbidv syntaxFormula0248
        (.imp (synWbr (.cv v) (.cv c) (.cv z)) (.objEq v z))
        (.imp syntaxFormula0249 (.objEq v z)) z v (.cv a) (.cv a) dv_cache_0186
        dv_cache_0187 p1296
    have p1298 :=
      @gImbi2d syntaxFormula0248
        (synWrex z (.cv a)
          (synWral v (.cv a) (.imp (synWbr (.cv v) (.cv c) (.cv z)) (.objEq v z))))
        (synWrex z (.cv a) (synWral v (.cv a) (.imp syntaxFormula0249 (.objEq v z))))
        (synWa (synWss (.cv a) (.cv b)) (synWne (.cv a) (synC0))) p1297
    have p1299 :=
      @gAlbidv syntaxFormula0248
        (.imp (synWa (synWss (.cv a) (.cv b)) (synWne (.cv a) (synC0))) (synWrex z (.cv a)
            (synWral v (.cv a) (.imp (synWbr (.cv v) (.cv c) (.cv z)) (.objEq v z)))))
        (.imp (synWa (synWss (.cv a) (.cv b)) (synWne (.cv a) (synC0)))
          (synWrex z (.cv a) (synWral v (.cv a) (.imp syntaxFormula0249 (.objEq v z)))))
        a dv_cache_0188 p1298
    exact continuation p1293 p1294 p1299

end NFChoice.DirectNominalPrf.WPPReplay

end
