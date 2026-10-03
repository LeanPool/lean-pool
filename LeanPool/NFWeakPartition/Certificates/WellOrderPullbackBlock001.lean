/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block011

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `ReplaySupport.WellOrderPullback1`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_pwpullwesetimpndv_stage1 (x : Var) (y : Var) (f : Var) (r : Var)
    {Result : Type}
    (continuation : _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ →
        _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ →
        _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → Result) :=
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
    let e : Var := freshVar proofSupport 6
    let h : Var := freshVar proofSupport 7
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
    have fresh_c_ne_y : c ≠ y := by
      intro h
      exact
        fresh_c
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
    have fresh_d_ne_y : d ≠ y := by
      intro h
      exact
        fresh_d
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
    have fresh_z_ne_x : z ≠ x := by
      intro h
      exact
        fresh_z
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
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
    have fresh_a_ne_g : a ≠ g :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
    have fresh_g_ne_a : g ≠ a := Ne.symm fresh_a_ne_g
    have fresh_a_ne_z : a ≠ z :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
    have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
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
    have fresh_c_ne_d : c ≠ d :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
    have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
    have fresh_g_ne_z : g ≠ z :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
    have dv_cache_0001 : b ∉ ((Wff.classEq (.cv c) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_c, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0002 : b ∉ ((Class.cv d)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_d, not_false_eq_true])
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
    have dv_cache_0006 : c ≠ b := by exact (show c ≠ b from (by exact fresh_c_ne_b))
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
    have dv_cache_0011 :
      c ∉ ((syn_wral b (.cv y) (syn_wbr (.cv b) (.cv r) (.cv b)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_y, fresh_c_ne_b,
            fresh_c_ne_r, or_false, and_false, not_false_eq_true])
    have dv_cache_0012 :
      d ∉ ((syn_wral b (.cv y) (syn_wbr (.cv b) (.cv r) (.cv b)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_y, fresh_d_ne_b,
            fresh_d_ne_r, or_false, and_false, not_false_eq_true])
    have dv_cache_0013 : c ≠ d := by exact (show c ≠ d from (by exact fresh_c_ne_d))
    have dv_cache_0014 : b ∉ ((syn_cfv (.cv f) (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0015 :
      b ∉ ((syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_f, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0016 : g ≠ a := by exact (show g ≠ a from (by exact fresh_g_ne_a))
    have dv_cache_0017 : g ∉ ((syn_ccnv (.cv f))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_g_ne_f,
            not_false_eq_true])
    have dv_cache_0018 :
      g ∉
        ((Wff.imp (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) (syn_wb (syn_wbr (.cv a)
                (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
                (.cv a)) (syn_wa (syn_wa (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
                  (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f)))))
                (syn_wbr (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (.cv r)
                  (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a))))))).fv :=
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
            Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_a, fresh_g_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0019 :
      a ∉
        ((syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))).fv :=
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
    have dv_cache_0020 : a ∉ (syn_wtru).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0021 : a ∉ ((Wff.classEq (.cv b) (syn_cpwpull (.cv f) (.cv r)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_f, fresh_a_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0022 : a ∉ ((Class.cv c)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_c, not_false_eq_true])
    have dv_cache_0023 : a ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_x, not_false_eq_true])
    have dv_cache_0024 : c ≠ a := by exact (show c ≠ a from (by exact fresh_c_ne_a))
    have dv_cache_0025 : b ≠ a := by exact (show b ≠ a from (by exact fresh_b_ne_a))
    have dv_cache_0026 : b ∉ ((syn_cpwpull (.cv f) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_f, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0027 : c ∉ ((syn_cpwpull (.cv f) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_f, fresh_c_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0028 : b ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_x, not_false_eq_true])
    have dv_cache_0029 : c ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_x, not_false_eq_true])
    have dv_cache_0030 :
      b ∉
        ((syn_wral a (.cv x) (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_a,
            fresh_b_ne_f, fresh_b_ne_r, or_false, and_false, not_false_eq_true])
    have dv_cache_0031 :
      c ∉
        ((syn_wral a (.cv x) (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_a,
            fresh_c_ne_f, fresh_c_ne_r, or_false, and_false, not_false_eq_true])
    have dv_cache_0032 : b ≠ c := by exact (show b ≠ c from (by exact fresh_b_ne_c))
    have dv_cache_0033 :
      z ∉ ((syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_x, fresh_z_ne_b, or_false,
            not_false_eq_true])
    have dv_cache_0034 : z ∉ (syn_wtru).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0035 : g ≠ b := by exact (show g ≠ b from (by exact fresh_g_ne_b))
    have dv_cache_0036 : g ≠ z := by exact (show g ≠ z from (by exact fresh_g_ne_z))
    have dv_cache_0037 :
      g ∉
        ((Wff.imp (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) (syn_wb (syn_wbr (.cv b)
                (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
                (.cv z)) (syn_wa (syn_wa (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f))))
                  (.classMem (.cv z) (syn_crn (syn_ccnv (.cv f)))))
                (syn_wbr (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b)) (.cv r)
                  (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv z))))))).fv :=
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
            Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_b, fresh_g_ne_z, fresh_g_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0038 :
      g ∉
        ((Wff.imp (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) (syn_wb (syn_wbr (.cv a)
                (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
                (.cv b)) (syn_wa (syn_wa (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
                  (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f)))))
                (syn_wbr (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (.cv r)
                  (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b))))))).fv :=
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
            Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_a, fresh_g_ne_b, fresh_g_ne_r,
            or_false, not_false_eq_true])
    let syntaxFormula0000 : Wff :=
      (syn_wa (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a))))
    let syntaxFormula0001 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_crn (.cv g))) (.classMem (.cv a) (syn_crn (.cv g))))
    let syntaxFormula0002 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f)))))
    let syntaxFormula0003 : Wff :=
      (syn_wbr (syn_cfv (syn_ccnv (.cv g)) (.cv a)) (.cv r)
        (syn_cfv (syn_ccnv (.cv g)) (.cv a)))
    let syntaxFormula0004 : Wff :=
      (syn_wbr (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (.cv r)
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)))
    let syntaxFormula0005 : Wff :=
      (syn_wbr (.cv a)
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f)))) (.cv a))
    let syntaxFormula0006 : Wff := (syn_wa syntaxFormula0001 syntaxFormula0003)
    let syntaxFormula0007 : Wff := (syn_wa syntaxFormula0002 syntaxFormula0004)
    let syntaxFormula0008 : Wff :=
      (syn_wb (syn_wbr (.cv a) (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g))) (.cv a))
        syntaxFormula0006)
    let syntaxFormula0009 : Wff := (syn_wb syntaxFormula0005 syntaxFormula0007)
    let syntaxFormula0010 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv a) (syn_cdm (.cv f))))
    let syntaxFormula0011 : Wff :=
      (syn_wa syntaxFormula0010
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a))))
    let syntaxFormula0012 : Wff :=
      (syn_w3a (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (.cv x)))
    let syntaxFormula0013 : Wff :=
      (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z)))
    let syntaxFormula0014 : Wff := (syn_w3a syn_wtru syntaxFormula0012 syntaxFormula0013)
    let syntaxFormula0015 : Wff :=
      (syn_wa (.classMem (.cv b) (syn_crn (.cv g))) (.classMem (.cv z) (syn_crn (.cv g))))
    let syntaxFormula0016 : Wff :=
      (syn_wa (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv z) (syn_crn (syn_ccnv (.cv f)))))
    let syntaxFormula0017 : Wff :=
      (syn_wbr (syn_cfv (syn_ccnv (.cv g)) (.cv b)) (.cv r)
        (syn_cfv (syn_ccnv (.cv g)) (.cv z)))
    let syntaxFormula0018 : Wff :=
      (syn_wbr (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b)) (.cv r)
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv z)))
    let syntaxFormula0019 : Wff :=
      (syn_wbr (.cv b)
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f)))) (.cv z))
    let syntaxFormula0020 : Wff := (syn_wa syntaxFormula0015 syntaxFormula0017)
    let syntaxFormula0021 : Wff := (syn_wa syntaxFormula0016 syntaxFormula0018)
    let syntaxFormula0022 : Wff :=
      (syn_wb (syn_wbr (.cv b) (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g))) (.cv z))
        syntaxFormula0020)
    let syntaxFormula0023 : Wff := (syn_wb syntaxFormula0019 syntaxFormula0021)
    let syntaxFormula0024 : Wff :=
      (syn_wa (.classMem (.cv b) (syn_cdm (.cv f))) (.classMem (.cv z) (syn_cdm (.cv f))))
    let syntaxFormula0025 : Wff :=
      (syn_wa syntaxFormula0024
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z))))
    let syntaxFormula0026 : Wff :=
      (syn_wa (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv z) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z))))
    let syntaxFormula0027 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_crn (.cv g))) (.classMem (.cv b) (syn_crn (.cv g))))
    let syntaxFormula0028 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f)))))
    let syntaxFormula0029 : Wff :=
      (syn_wbr (syn_cfv (syn_ccnv (.cv g)) (.cv a)) (.cv r)
        (syn_cfv (syn_ccnv (.cv g)) (.cv b)))
    let syntaxFormula0030 : Wff :=
      (syn_wbr (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (.cv r)
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b)))
    let syntaxFormula0031 : Wff :=
      (syn_wbr (.cv a)
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f)))) (.cv b))
    let syntaxFormula0032 : Wff := (syn_wa syntaxFormula0027 syntaxFormula0029)
    let syntaxFormula0033 : Wff := (syn_wa syntaxFormula0028 syntaxFormula0030)
    let syntaxFormula0034 : Wff :=
      (syn_wb (syn_wbr (.cv a) (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g))) (.cv b))
        syntaxFormula0032)
    let syntaxFormula0035 : Wff := (syn_wb syntaxFormula0031 syntaxFormula0033)
    let syntaxFormula0036 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv b) (syn_cdm (.cv f))))
    let syntaxFormula0037 : Wff :=
      (syn_wa syntaxFormula0036
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
    let syntaxFormula0038 : Wff :=
      (syn_wa (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
    have p0000 := @g_tru
    have p0001 := @g_id (.classMem (.cv a) (.cv x))
    have p0003 :=
      @g_jca (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x))
        (.classMem (.cv a) (.cv x)) p0001 p0001
    have p0004 :=
      @g_simpr (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))
    have p0005 := @g_wppweref (.cv y) (.cv r)
    have p0006 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cref) (.cv y)) p0004
        p0005
    have p0007 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv r) (syn_cref) (.cv y)) (.classMem (.cv a) (.cv x)) p0006
    have p0008 := @g_brex (.cv r) (.cv y) (syn_cref)
    have p0009 := @g_breq (.cv b) (.cv b) (.cv c) (.cv r)
    have p0010 :=
      @g_ralbidv (.classEq (.cv c) (.cv r)) (syn_wbr (.cv b) (.cv c) (.cv b))
        (syn_wbr (.cv b) (.cv r) (.cv b)) b (.cv d) dv_cache_0001 p0009
    have p0011 :=
      @g_raleq (syn_wbr (.cv b) (.cv r) (.cv b)) b (.cv d) (.cv y) dv_cache_0002
        dv_cache_0003
    have p0012 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ref b c d
        dv_cache_0004 dv_cache_0005 dv_cache_0006
    have p0013 :=
      @g_brabg (syn_wral b (.cv d) (syn_wbr (.cv b) (.cv c) (.cv b)))
        (syn_wral b (.cv d) (syn_wbr (.cv b) (.cv r) (.cv b)))
        (syn_wral b (.cv y) (syn_wbr (.cv b) (.cv r) (.cv b))) c d (.cv r) (.cv y)
        (syn_cvv) (syn_cvv) (syn_cref) dv_cache_0007 dv_cache_0008 dv_cache_0009
        dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 p0010 p0011 p0012
    have p0014 :=
      @g_syl (syn_wbr (.cv r) (syn_cref) (.cv y))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
        (syn_wb (syn_wbr (.cv r) (syn_cref) (.cv y))
          (syn_wral b (.cv y) (syn_wbr (.cv b) (.cv r) (.cv b))))
        p0008 p0013
    have p0015 :=
      @g_ibi (syn_wbr (.cv r) (syn_cref) (.cv y))
        (syn_wral b (.cv y) (syn_wbr (.cv b) (.cv r) (.cv b))) p0014
    have p0016 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv a) (.cv x)) (syn_wbr (.cv r) (syn_cref) (.cv y))
        (syn_wral b (.cv y) (syn_wbr (.cv b) (.cv r) (.cv b))) p0007 p0015
    have p0018 :=
      @g_simpl (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y))
    have p0019 := @g_f1ofo (.cv x) (.cv y) (.cv f)
    have p0020 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wfo (.cv f) (.cv x) (.cv y)) p0018 p0019
    have p0021 := @g_fof (.cv x) (.cv y) (.cv f)
    have p0022 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wf (.cv f) (.cv x) (.cv y)) p0020 p0021
    have p0023 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf (.cv f) (.cv x) (.cv y)) (.classMem (.cv a) (.cv x)) p0022
    have p0024 := @g_ffvelrn (.cv x) (.cv y) (.cv a) (.cv f)
    have p0025 :=
      @g_ex (syn_wf (.cv f) (.cv x) (.cv y)) (.classMem (.cv a) (.cv x))
        (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y)) p0024
    have p0026 :=
      @g_syl56 (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf (.cv f) (.cv x) (.cv y))
        (.imp (.classMem (.cv a) (.cv x)) (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y)))
        p0001 p0023 p0025
    have p0027 :=
      @g_pm2_43d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv a) (.cv x)) (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y)) p0026
    have p0028 := @g_id (.classEq (.cv b) (syn_cfv (.cv f) (.cv a)))
    have p0029 :=
      @g_breq12d (.classEq (.cv b) (syn_cfv (.cv f) (.cv a))) (.cv b)
        (syn_cfv (.cv f) (.cv a)) (.cv b) (syn_cfv (.cv f) (.cv a)) (.cv r) p0028 p0028
    have p0030 :=
      @g_rspccv (syn_wbr (.cv b) (.cv r) (.cv b))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a))) b
        (syn_cfv (.cv f) (.cv a)) (.cv y) dv_cache_0014 dv_cache_0003 dv_cache_0015 p0029
    have p0031 :=
      @g_syl6c
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv a) (.cv x)) (syn_wral b (.cv y) (syn_wbr (.cv b) (.cv r) (.cv b)))
        (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a))) p0016 p0027
        p0030
    have p0032 :=
      @g_pm3_2 (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a)))
    have p0033 :=
      @g_syl9
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv a) (.cv x))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x))) syntaxFormula0000
        p0031 p0032
    have p0034 :=
      @g_syl5 (.classMem (.cv a) (.cv x))
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x)))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.imp (.classMem (.cv a) (.cv x)) syntaxFormula0000) p0003 p0033
    have p0035 :=
      @g_pm2_43d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv a) (.cv x)) syntaxFormula0000 p0034
    have p0036 := (Nominal.classEqRefl (syn_cpwpull (.cv f) (.cv r)))
    have p0037 :=
      @g_breqi (.cv a) (.cv a) (syn_cpwpull (.cv f) (.cv r))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p0038 := @g_cnvcnv (.cv f)
    have p0039 :=
      @g_coeq2i (syn_ccnv (syn_ccnv (.cv f))) (.cv f)
        (syn_ccom (syn_ccnv (.cv f)) (.cv r)) p0038
    have p0040 :=
      @g_breqi (.cv a) (.cv a)
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p0041 := @g_fofun (.cv x) (.cv y) (.cv f)
    have p0042 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wfun (.cv f)) p0020 p0041
    have p0044 := @g_funeqi (syn_ccnv (syn_ccnv (.cv f))) (.cv f) p0038
    have p0045 :=
      @g_sylibr
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfun (.cv f)) (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) p0042 p0044
    have p0046 := @g_vex f
    have p0047 := @g_cnvex (.cv f) p0046
    have p0048 := @g_id (.classEq (.cv g) (syn_ccnv (.cv f)))
    have p0049 :=
      @g_cnveqd (.classEq (.cv g) (syn_ccnv (.cv f))) (.cv g) (syn_ccnv (.cv f)) p0048
    have p0050 :=
      @g_funeqd (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_ccnv (.cv g))
        (syn_ccnv (syn_ccnv (.cv f))) p0049
    have p0052 :=
      @g_coeq1d (.classEq (.cv g) (syn_ccnv (.cv f))) (.cv g) (syn_ccnv (.cv f)) (.cv r)
        p0048
    have p0055 :=
      @g_coeq12d (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_ccom (.cv g) (.cv r))
        (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (.cv g))
        (syn_ccnv (syn_ccnv (.cv f))) p0052 p0049
    have p0056 :=
      @g_breqd (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g)))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
        (.cv a) (.cv a) p0055
    have p0058 :=
      @g_rneqd (.classEq (.cv g) (syn_ccnv (.cv f))) (.cv g) (syn_ccnv (.cv f)) p0048
    have p0059 :=
      @g_eleq2d (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_crn (.cv g))
        (syn_crn (syn_ccnv (.cv f))) (.cv a) p0058
    have p0063 :=
      @g_anbi12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (.classMem (.cv a) (syn_crn (.cv g)))
        (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv a) (syn_crn (.cv g)))
        (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f)))) p0059 p0059
    have p0066 :=
      @g_fveq1d (.classEq (.cv g) (syn_ccnv (.cv f))) (.cv a) (syn_ccnv (.cv g))
        (syn_ccnv (syn_ccnv (.cv f))) p0049
    have p0070 :=
      @g_breq12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_cfv (syn_ccnv (.cv g)) (.cv a))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a))
        (syn_cfv (syn_ccnv (.cv g)) (.cv a))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (.cv r) p0066 p0066
    have p0071 :=
      @g_anbi12d (.classEq (.cv g) (syn_ccnv (.cv f))) syntaxFormula0001 syntaxFormula0002
        syntaxFormula0003 syntaxFormula0004 p0063 p0070
    have p0072 :=
      @g_bibi12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_wbr (.cv a) (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g))) (.cv a))
        syntaxFormula0005 syntaxFormula0006 syntaxFormula0007 p0056 p0071
    have p0073 :=
      @g_imbi12d (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfun (syn_ccnv (.cv g)))
        (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0008 syntaxFormula0009 p0050
        p0072
    have p0074 := @g_hwtrnbrd a a g r dv_cache_0016 dv_cache_0016
    have p0075 :=
      @g_vtoclg (.imp (syn_wfun (syn_ccnv (.cv g))) syntaxFormula0008)
        (.imp (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0009) g
        (syn_ccnv (.cv f)) (syn_cvv) dv_cache_0017 dv_cache_0018 p0073 p0074
    have p0076 := Nominal.mp p0047 p0075
    have p0077 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0009 p0045 p0076
    have p0078 := @g_dfrn4 (syn_ccnv (.cv f))
    have p0080 := @g_dmeqi (syn_ccnv (syn_ccnv (.cv f))) (.cv f) p0038
    have p0081 :=
      @g_eqtri (syn_crn (syn_ccnv (.cv f))) (syn_cdm (syn_ccnv (syn_ccnv (.cv f))))
        (syn_cdm (.cv f)) p0078 p0080
    have p0082 := @g_eleq2i (syn_crn (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (.cv a) p0081
    have p0088 :=
      @g_anbi12i (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv a) (syn_cdm (.cv f)))
        (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv a) (syn_cdm (.cv f))) p0082 p0082
    have p0090 := @g_fveq1i (.cv a) (syn_ccnv (syn_ccnv (.cv f))) (.cv f) p0038
    have p0093 :=
      @g_breq12i (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (syn_cfv (.cv f) (.cv a))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (syn_cfv (.cv f) (.cv a)) (.cv r)
        p0090 p0090
    have p0094 :=
      @g_anbi12i syntaxFormula0002 syntaxFormula0010 syntaxFormula0004
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a))) p0088 p0093
    have p0095 :=
      @g_syl6bb
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0005 syntaxFormula0007 syntaxFormula0011 p0077 p0094
    have p0096 :=
      @g_syl5bbr
        (syn_wbr (.cv a) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (.cv a))
        syntaxFormula0005
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0011 p0040 p0095
    have p0097 :=
      @g_syl5bb (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (syn_wbr (.cv a) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (.cv a))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0011 p0037 p0096
    have p0098 := @g_fofn (.cv x) (.cv y) (.cv f)
    have p0099 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfo (.cv f) (.cv x) (.cv y)) (syn_wfn (.cv f) (.cv x)) p0020 p0098
    have p0100 := @g_fndm (.cv x) (.cv f)
    have p0101 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfn (.cv f) (.cv x)) (.classEq (syn_cdm (.cv f)) (.cv x)) p0099 p0100
    have p0102 :=
      @g_eleq2d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_cdm (.cv f)) (.cv x) (.cv a) p0101
    have p0103 :=
      @g_anbi12d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv a) (.cv x))
        (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv a) (.cv x)) p0102 p0102
    have p0104 :=
      @g_anbi1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0010 (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a))) p0103
    have p0105 :=
      @g_biid (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a)))
    have p0106 :=
      @g_anbi2i (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x))) p0105
    have p0107 :=
      @g_a1ii
        (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
          (syn_wb syntaxFormula0011 syntaxFormula0000))
        (syn_wb syntaxFormula0000 syntaxFormula0000) p0104 p0106
    have p0108 :=
      @g_bitrd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) syntaxFormula0011
        syntaxFormula0000 p0097 p0107
    have p0109 :=
      @g_sylibrd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv a) (.cv x)) syntaxFormula0000
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p0035 p0108
    have p0110 :=
      @g_adantld
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv a) (.cv x))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) syn_wtru p0109
    have p0111 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (.classMem (.cv a) (.cv x))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p0110
    have p0112 :=
      @g_ralrimdv
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) a (.cv x)
        dv_cache_0019 dv_cache_0020 p0111
    have p0113 := @g_vex r
    have p0114 := @g_pwpullex (.cv r) (.cv f) p0046 p0113
    have p0115 :=
      @g_a1i (.classMem (syn_cpwpull (.cv f) (.cv r)) (syn_cvv)) syn_wtru p0114
    have p0116 := @g_vex x
    have p0117 := @g_a1i (.classMem (.cv x) (syn_cvv)) syn_wtru p0116
    have p0118 := @g_breq (.cv a) (.cv a) (.cv b) (syn_cpwpull (.cv f) (.cv r))
    have p0119 :=
      @g_ralbidv (.classEq (.cv b) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wbr (.cv a) (.cv b) (.cv a))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) a (.cv c) dv_cache_0021
        p0118
    have p0120 :=
      @g_raleq (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) a (.cv c) (.cv x)
        dv_cache_0022 dv_cache_0023
    have p0121 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ref a b c
        dv_cache_0006 dv_cache_0024 dv_cache_0025
    have p0122 :=
      @g_brabg (syn_wral a (.cv c) (syn_wbr (.cv a) (.cv b) (.cv a)))
        (syn_wral a (.cv c) (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
        (syn_wral a (.cv x) (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a))) b c
        (syn_cpwpull (.cv f) (.cv r)) (.cv x) (syn_cvv) (syn_cvv) (syn_cref) dv_cache_0026
        dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
        dv_cache_0032 p0119 p0120 p0121
    have p0123 :=
      @g_syl2anc syn_wtru (.classMem (syn_cpwpull (.cv f) (.cv r)) (syn_cvv))
        (.classMem (.cv x) (syn_cvv))
        (syn_wb (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cref) (.cv x))
          (syn_wral a (.cv x) (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a))))
        p0115 p0117 p0122
    have p0124 :=
      @g_biimprd syn_wtru (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cref) (.cv x))
        (syn_wral a (.cv x) (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a))) p0123
    have p0125 :=
      @g_sylcom
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru
        (syn_wral a (.cv x) (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cref) (.cv x)) p0112 p0124
    have p0126 :=
      @g_mpi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cref) (.cv x)) p0000 p0125
    have p0128 :=
      @g_nfv (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) z
        dv_cache_0033
    have p0129 :=
      @g_a1i (syn_wnf z (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
        syn_wtru p0128
    have p0130 :=
      @g_nfrd syn_wtru (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) z
        p0129
    have p0131 := @g_nfv syn_wtru z dv_cache_0034
    have p0132 := @g_nfri syn_wtru z p0131
    have p0133 := (Nominal.biimpRefl syntaxFormula0012)
    have p0134 :=
      @g_biimpri syntaxFormula0012
        (syn_wa (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
          (.classMem (.cv z) (.cv x)))
        p0133
    have p0135 := @g_simp2 syn_wtru syntaxFormula0012 syntaxFormula0013
    have p0136 :=
      @g_simp1 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (.cv x))
    have p0137 :=
      @g_syl syntaxFormula0014 syntaxFormula0012 (.classMem (.cv a) (.cv x)) p0135 p0136
    have p0139 :=
      @g_simp3 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (.cv x))
    have p0140 :=
      @g_syl syntaxFormula0014 syntaxFormula0012 (.classMem (.cv z) (.cv x)) p0135 p0139
    have p0141 :=
      @g_jca syntaxFormula0014 (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x))
        p0137 p0140
    have p0142 := @g_simp3 syn_wtru syntaxFormula0012 syntaxFormula0013
    have p0143 :=
      @g_simpr (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
    have p0144 :=
      @g_syl syntaxFormula0014 syntaxFormula0013
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) p0142 p0143
    have p0146 :=
      @g_breqi (.cv b) (.cv z) (syn_cpwpull (.cv f) (.cv r))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p0149 :=
      @g_breqi (.cv b) (.cv z)
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p0159 :=
      @g_breqd (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g)))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
        (.cv b) (.cv z) p0055
    have p0162 :=
      @g_eleq2d (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_crn (.cv g))
        (syn_crn (syn_ccnv (.cv f))) (.cv b) p0058
    have p0165 :=
      @g_eleq2d (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_crn (.cv g))
        (syn_crn (syn_ccnv (.cv f))) (.cv z) p0058
    have p0166 :=
      @g_anbi12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (.classMem (.cv b) (syn_crn (.cv g)))
        (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv z) (syn_crn (.cv g)))
        (.classMem (.cv z) (syn_crn (syn_ccnv (.cv f)))) p0162 p0165
    have p0169 :=
      @g_fveq1d (.classEq (.cv g) (syn_ccnv (.cv f))) (.cv b) (syn_ccnv (.cv g))
        (syn_ccnv (syn_ccnv (.cv f))) p0049
    have p0172 :=
      @g_fveq1d (.classEq (.cv g) (syn_ccnv (.cv f))) (.cv z) (syn_ccnv (.cv g))
        (syn_ccnv (syn_ccnv (.cv f))) p0049
    have p0173 :=
      @g_breq12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_cfv (syn_ccnv (.cv g)) (.cv b))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b))
        (syn_cfv (syn_ccnv (.cv g)) (.cv z))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv z)) (.cv r) p0169 p0172
    have p0174 :=
      @g_anbi12d (.classEq (.cv g) (syn_ccnv (.cv f))) syntaxFormula0015 syntaxFormula0016
        syntaxFormula0017 syntaxFormula0018 p0166 p0173
    have p0175 :=
      @g_bibi12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_wbr (.cv b) (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g))) (.cv z))
        syntaxFormula0019 syntaxFormula0020 syntaxFormula0021 p0159 p0174
    have p0176 :=
      @g_imbi12d (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfun (syn_ccnv (.cv g)))
        (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0022 syntaxFormula0023 p0050
        p0175
    have p0177 := @g_hwtrnbrd b z g r dv_cache_0035 dv_cache_0036
    have p0178 :=
      @g_vtoclg (.imp (syn_wfun (syn_ccnv (.cv g))) syntaxFormula0022)
        (.imp (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0023) g
        (syn_ccnv (.cv f)) (syn_cvv) dv_cache_0017 dv_cache_0037 p0176 p0177
    have p0179 := Nominal.mp p0047 p0178
    have p0180 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0023 p0045 p0179
    have p0185 := @g_eleq2i (syn_crn (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (.cv b) p0081
    have p0190 := @g_eleq2i (syn_crn (syn_ccnv (.cv f))) (syn_cdm (.cv f)) (.cv z) p0081
    have p0191 :=
      @g_anbi12i (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv b) (syn_cdm (.cv f)))
        (.classMem (.cv z) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv z) (syn_cdm (.cv f))) p0185 p0190
    have p0193 := @g_fveq1i (.cv b) (syn_ccnv (syn_ccnv (.cv f))) (.cv f) p0038
    have p0195 := @g_fveq1i (.cv z) (syn_ccnv (syn_ccnv (.cv f))) (.cv f) p0038
    have p0196 :=
      @g_breq12i (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b)) (syn_cfv (.cv f) (.cv b))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv z)) (syn_cfv (.cv f) (.cv z)) (.cv r)
        p0193 p0195
    have p0197 :=
      @g_anbi12i syntaxFormula0016 syntaxFormula0024 syntaxFormula0018
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z))) p0191 p0196
    have p0198 :=
      @g_syl6bb
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0019 syntaxFormula0021 syntaxFormula0025 p0180 p0197
    have p0199 :=
      @g_syl5bbr
        (syn_wbr (.cv b) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (.cv z))
        syntaxFormula0019
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0025 p0149 p0198
    have p0200 :=
      @g_syl5bb (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
        (syn_wbr (.cv b) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (.cv z))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0025 p0146 p0199
    have p0201 :=
      @g_eleq2d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_cdm (.cv f)) (.cv x) (.cv b) p0101
    have p0202 :=
      @g_eleq2d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_cdm (.cv f)) (.cv x) (.cv z) p0101
    have p0203 :=
      @g_anbi12d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv b) (syn_cdm (.cv f))) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (syn_cdm (.cv f))) (.classMem (.cv z) (.cv x)) p0201 p0202
    have p0204 :=
      @g_anbi1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0024 (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv z) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z))) p0203
    have p0205 :=
      @g_biid (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
    have p0206 :=
      @g_anbi2i (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
        (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv z) (.cv x))) p0205
    have p0207 :=
      @g_a1ii
        (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
          (syn_wb syntaxFormula0025 syntaxFormula0026))
        (syn_wb syntaxFormula0026 syntaxFormula0026) p0204 p0206
    have p0208 :=
      @g_bitrd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) syntaxFormula0025
        syntaxFormula0026 p0200 p0207
    have p0209 :=
      @g_biimpd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) syntaxFormula0026 p0208
    have p0210 :=
      @g_syl5 syntaxFormula0014 (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0026 p0144 p0209
    have p0211 :=
      @g_simpr (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv z) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
    have p0212 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014 syntaxFormula0026
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z))) p0210 p0211
    have p0214 :=
      @g_simpl (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
    have p0215 :=
      @g_syl syntaxFormula0014 syntaxFormula0013
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b)) p0142 p0214
    have p0217 :=
      @g_breqi (.cv a) (.cv b) (syn_cpwpull (.cv f) (.cv r))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p0220 :=
      @g_breqi (.cv a) (.cv b)
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p0230 :=
      @g_breqd (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g)))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
        (.cv a) (.cv b) p0055
    have p0237 :=
      @g_anbi12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (.classMem (.cv a) (syn_crn (.cv g)))
        (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv b) (syn_crn (.cv g)))
        (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f)))) p0059 p0162
    have p0244 :=
      @g_breq12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_cfv (syn_ccnv (.cv g)) (.cv a))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a))
        (syn_cfv (syn_ccnv (.cv g)) (.cv b))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b)) (.cv r) p0066 p0169
    have p0245 :=
      @g_anbi12d (.classEq (.cv g) (syn_ccnv (.cv f))) syntaxFormula0027 syntaxFormula0028
        syntaxFormula0029 syntaxFormula0030 p0237 p0244
    have p0246 :=
      @g_bibi12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_wbr (.cv a) (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g))) (.cv b))
        syntaxFormula0031 syntaxFormula0032 syntaxFormula0033 p0230 p0245
    have p0247 :=
      @g_imbi12d (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfun (syn_ccnv (.cv g)))
        (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0034 syntaxFormula0035 p0050
        p0246
    have p0248 := @g_hwtrnbrd a b g r dv_cache_0016 dv_cache_0035
    have p0249 :=
      @g_vtoclg (.imp (syn_wfun (syn_ccnv (.cv g))) syntaxFormula0034)
        (.imp (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0035) g
        (syn_ccnv (.cv f)) (syn_cvv) dv_cache_0017 dv_cache_0038 p0247 p0248
    have p0250 := Nominal.mp p0047 p0249
    have p0251 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0035 p0045 p0250
    have p0262 :=
      @g_anbi12i (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv a) (syn_cdm (.cv f)))
        (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv b) (syn_cdm (.cv f))) p0082 p0185
    have p0267 :=
      @g_breq12i (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (syn_cfv (.cv f) (.cv a))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b)) (syn_cfv (.cv f) (.cv b)) (.cv r)
        p0090 p0193
    have p0268 :=
      @g_anbi12i syntaxFormula0028 syntaxFormula0036 syntaxFormula0030
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))) p0262 p0267
    have p0269 :=
      @g_syl6bb
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0031 syntaxFormula0033 syntaxFormula0037 p0251 p0268
    have p0270 :=
      @g_syl5bbr
        (syn_wbr (.cv a) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (.cv b))
        syntaxFormula0031
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0037 p0220 p0269
    have p0271 :=
      @g_syl5bb (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv a) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (.cv b))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0037 p0217 p0270
    have p0272 :=
      @g_anbi12d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv a) (.cv x))
        (.classMem (.cv b) (syn_cdm (.cv f))) (.classMem (.cv b) (.cv x)) p0102 p0201
    have p0273 :=
      @g_anbi1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0036 (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))) p0272
    have p0274 :=
      @g_biid (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
    have p0275 :=
      @g_anbi2i (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) p0274
    have p0276 :=
      @g_a1ii
        (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
          (syn_wb syntaxFormula0037 syntaxFormula0038))
        (syn_wb syntaxFormula0038 syntaxFormula0038) p0273 p0275
    have p0277 :=
      @g_bitrd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b)) syntaxFormula0037
        syntaxFormula0038 p0271 p0276
    have p0278 :=
      @g_biimpd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b)) syntaxFormula0038 p0277
    have p0279 :=
      @g_syl5 syntaxFormula0014 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0038 p0215 p0278
    have p0280 :=
      @g_simpr (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
    have p0281 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014 syntaxFormula0038
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))) p0279 p0280
    have p0282 :=
      @g_a1dd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z))) p0281
    have p0283 :=
      @g_ancom (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
    have p0284 := @g_wppwepo (.cv y) (.cv r)
    have p0285 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cpartial) (.cv y)) p0004
        p0284
    have p0286 := @g_porta (.cv y) (.cv r)
    have p0287 :=
      @g_simp2bi (syn_wbr (.cv r) (syn_cpartial) (.cv y))
        (syn_wbr (.cv r) (syn_cref) (.cv y)) (syn_wbr (.cv r) (syn_ctrans) (.cv y))
        (syn_wbr (.cv r) (syn_cantisym) (.cv y)) p0286
    have p0288 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv r) (syn_cpartial) (.cv y)) (syn_wbr (.cv r) (syn_ctrans) (.cv y))
        p0285 p0287
    have p0289 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv r) (syn_ctrans) (.cv y)) syntaxFormula0014 p0288
    have p0290 := @g_brex (.cv r) (.cv y) (syn_ctrans)
    have p0291 := @g_breq (.cv c) (.cv d) (.cv g) (.cv r)
    have p0292 := @g_breq (.cv d) (.cv e) (.cv g) (.cv r)
    have p0293 :=
      @g_anbi12d (.classEq (.cv g) (.cv r)) (syn_wbr (.cv c) (.cv g) (.cv d))
        (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv g) (.cv e))
        (syn_wbr (.cv d) (.cv r) (.cv e)) p0291 p0292
    have p0294 := @g_breq (.cv c) (.cv e) (.cv g) (.cv r)
    exact
      continuation p0000 p0004 p0015 p0018 p0022 p0027 p0036 p0038 p0039 p0042 p0045 p0046
        p0047 p0049 p0050 p0055 p0058 p0059 p0066 p0081 p0082 p0090 p0101 p0102 p0113
        p0114 p0115 p0116 p0117 p0126 p0130 p0132 p0134 p0135 p0137 p0140 p0141 p0162
        p0165 p0169 p0172 p0185 p0190 p0193 p0195 p0201 p0202 p0212 p0277 p0278 p0282
        p0283 p0286 p0289 p0290 p0293 p0294

end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `ReplaySupport.WellOrderPullback2`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_pwpullwesetimpndv_stage2 (x : Var) (y : Var) (f : Var) (r : Var)
    (p0000 : _) (p0004 : _) (p0018 : _) (p0022 : _) (p0027 : _) (p0036 : _) (p0039 : _)
    (p0045 : _) (p0047 : _) (p0050 : _) (p0055 : _) (p0059 : _) (p0066 : _) (p0082 : _)
    (p0090 : _) (p0102 : _) (p0115 : _) (p0117 : _) (p0130 : _) (p0132 : _) (p0134 : _)
    (p0135 : _) (p0137 : _) (p0140 : _) (p0141 : _) (p0162 : _) (p0165 : _) (p0169 : _)
    (p0172 : _) (p0185 : _) (p0190 : _) (p0193 : _) (p0195 : _) (p0201 : _) (p0202 : _)
    (p0212 : _) (p0278 : _) (p0282 : _) (p0283 : _) (p0289 : _) (p0290 : _) (p0293 : _)
    (p0294 : _) {Result : Type}
    (continuation : _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → Result) :=
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
    let e : Var := freshVar proofSupport 6
    let h : Var := freshVar proofSupport 7
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
    have fresh_c_ne_y : c ≠ y := by
      intro h
      exact
        fresh_c
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
    have fresh_d_ne_y : d ≠ y := by
      intro h
      exact
        fresh_d
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
    have fresh_g_ne_y : g ≠ y := by
      intro h
      exact
        fresh_g
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
    have fresh_z_ne_x : z ≠ x := by
      intro h
      exact
        fresh_z
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_z_ne_y : z ≠ y := by
      intro h
      exact
        fresh_z
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_z_ne_f : z ≠ f := by
      intro h
      exact
        fresh_z
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_z_ne_r : z ≠ r := by
      intro h
      exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
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
    have fresh_e_ne_f : e ≠ f := by
      intro h
      exact
        fresh_e
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_e_ne_r : e ≠ r := by
      intro h
      exact fresh_e (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_h : h ∉ proofSupport :=
      by
      change freshVar proofSupport 7 ∉ proofSupport
      exact freshVar_not_mem proofSupport 7
    have fresh_h_ne_y : h ≠ y := by
      intro h
      exact
        fresh_h
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_h_ne_r : h ≠ r := by
      intro h
      exact fresh_h (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_a_ne_b : a ≠ b :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 1
      exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
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
    have fresh_a_ne_g : a ≠ g :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
    have fresh_g_ne_a : g ≠ a := Ne.symm fresh_a_ne_g
    have fresh_a_ne_z : a ≠ z :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
    have fresh_a_ne_e : a ≠ e :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
    have fresh_e_ne_a : e ≠ a := Ne.symm fresh_a_ne_e
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
    have fresh_b_ne_e : b ≠ e :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
    have fresh_e_ne_b : e ≠ b := Ne.symm fresh_b_ne_e
    have fresh_c_ne_d : c ≠ d :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
    have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
    have fresh_c_ne_g : c ≠ g :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
    have fresh_g_ne_c : g ≠ c := Ne.symm fresh_c_ne_g
    have fresh_c_ne_z : c ≠ z :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
    have fresh_z_ne_c : z ≠ c := Ne.symm fresh_c_ne_z
    have fresh_c_ne_e : c ≠ e :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
    have fresh_e_ne_c : e ≠ c := Ne.symm fresh_c_ne_e
    have fresh_c_ne_h : c ≠ h :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 2) (j := 7) (by decide)
    have fresh_h_ne_c : h ≠ c := Ne.symm fresh_c_ne_h
    have fresh_d_ne_g : d ≠ g :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
    have fresh_g_ne_d : g ≠ d := Ne.symm fresh_d_ne_g
    have fresh_d_ne_z : d ≠ z :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
    have fresh_z_ne_d : z ≠ d := Ne.symm fresh_d_ne_z
    have fresh_d_ne_e : d ≠ e :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
    have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
    have fresh_d_ne_h : d ≠ h :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
    have fresh_h_ne_d : h ≠ d := Ne.symm fresh_d_ne_h
    have fresh_g_ne_z : g ≠ z :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
    have fresh_g_ne_e : g ≠ e :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
    have fresh_e_ne_g : e ≠ g := Ne.symm fresh_g_ne_e
    have fresh_g_ne_h : g ≠ h :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
    have fresh_h_ne_g : h ≠ g := Ne.symm fresh_g_ne_h
    have fresh_z_ne_e : z ≠ e :=
      by
      change freshVar proofSupport 5 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
    have fresh_e_ne_z : e ≠ z := Ne.symm fresh_z_ne_e
    have fresh_e_ne_h : e ≠ h :=
      by
      change freshVar proofSupport 6 ≠ freshVar proofSupport 7
      exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
    have fresh_h_ne_e : h ≠ e := Ne.symm fresh_e_ne_h
    have dv_cache_0002 : b ∉ ((Class.cv d)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_d, not_false_eq_true])
    have dv_cache_0004 : d ≠ c := by exact (show d ≠ c from (by exact fresh_d_ne_c))
    have dv_cache_0005 : d ≠ b := by exact (show d ≠ b from (by exact fresh_d_ne_b))
    have dv_cache_0006 : c ≠ b := by exact (show c ≠ b from (by exact fresh_c_ne_b))
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
    have dv_cache_0013 : c ≠ d := by exact (show c ≠ d from (by exact fresh_c_ne_d))
    have dv_cache_0016 : g ≠ a := by exact (show g ≠ a from (by exact fresh_g_ne_a))
    have dv_cache_0017 : g ∉ ((syn_ccnv (.cv f))).fv := by
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
        ((syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))).fv :=
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
    have dv_cache_0020 : a ∉ (syn_wtru).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0023 : a ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_x, not_false_eq_true])
    have dv_cache_0024 : c ≠ a := by exact (show c ≠ a from (by exact fresh_c_ne_a))
    have dv_cache_0027 : c ∉ ((syn_cpwpull (.cv f) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_f, fresh_c_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0028 : b ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_x, not_false_eq_true])
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
    have dv_cache_0036 : g ≠ z := by exact (show g ≠ z from (by exact fresh_g_ne_z))
    have dv_cache_0039 : e ∉ ((Wff.classEq (.cv g) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_e_ne_g, fresh_e_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0040 : c ∉ ((Wff.classEq (.cv g) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_g, fresh_c_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0041 : d ∉ ((Wff.classEq (.cv g) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_g, fresh_d_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0042 : e ∉ ((Class.cv h)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_e_ne_h, not_false_eq_true])
    have dv_cache_0043 : e ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_e_ne_y, not_false_eq_true])
    have dv_cache_0044 : d ∉ ((Class.cv h)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_d_ne_h, not_false_eq_true])
    have dv_cache_0045 : c ∉ ((Class.cv h)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_h, not_false_eq_true])
    have dv_cache_0046 : h ≠ g := by exact (show h ≠ g from (by exact fresh_h_ne_g))
    have dv_cache_0047 : h ≠ c := by exact (show h ≠ c from (by exact fresh_h_ne_c))
    have dv_cache_0048 : h ≠ d := by exact (show h ≠ d from (by exact fresh_h_ne_d))
    have dv_cache_0049 : h ≠ e := by exact (show h ≠ e from (by exact fresh_h_ne_e))
    have dv_cache_0050 : g ≠ c := by exact (show g ≠ c from (by exact fresh_g_ne_c))
    have dv_cache_0051 : g ≠ d := by exact (show g ≠ d from (by exact fresh_g_ne_d))
    have dv_cache_0052 : g ≠ e := by exact (show g ≠ e from (by exact fresh_g_ne_e))
    have dv_cache_0053 : c ≠ e := by exact (show c ≠ e from (by exact fresh_c_ne_e))
    have dv_cache_0054 : d ≠ e := by exact (show d ≠ e from (by exact fresh_d_ne_e))
    have dv_cache_0055 : g ∉ ((Class.cv r)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_g_ne_r, not_false_eq_true])
    have dv_cache_0056 : h ∉ ((Class.cv r)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_h_ne_r, not_false_eq_true])
    have dv_cache_0057 : g ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_g_ne_y, not_false_eq_true])
    have dv_cache_0058 : h ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_h_ne_y, not_false_eq_true])
    have dv_cache_0059 :
      g ∉
        ((syn_wral c (.cv y) (syn_wral d (.cv y) (syn_wral e (.cv y) (.imp
                  (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv e)))
                  (syn_wbr (.cv c) (.cv r) (.cv e))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_g_ne_y, fresh_g_ne_c,
            fresh_g_ne_d, fresh_g_ne_r, fresh_g_ne_e, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0060 :
      h ∉
        ((syn_wral c (.cv y) (syn_wral d (.cv y) (syn_wral e (.cv y) (.imp
                  (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv e)))
                  (syn_wbr (.cv c) (.cv r) (.cv e))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : h ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_h_ne_y, fresh_h_ne_c,
            fresh_h_ne_d, fresh_h_ne_r, fresh_h_ne_e, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0061 : g ≠ h := by exact (show g ≠ h from (by exact fresh_g_ne_h))
    have dv_cache_0062 : c ∉ ((syn_cfv (.cv f) (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0063 : d ∉ ((syn_cfv (.cv f) (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0064 : e ∉ ((syn_cfv (.cv f) (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_e_ne_a, fresh_e_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0065 : d ∉ ((syn_cfv (.cv f) (.cv b))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_b, fresh_d_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0066 : e ∉ ((syn_cfv (.cv f) (.cv b))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_e_ne_b, fresh_e_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0067 : e ∉ ((syn_cfv (.cv f) (.cv z))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_e_ne_z, fresh_e_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0068 :
      c ∉
        ((Wff.imp (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
              (syn_wbr (.cv d) (.cv r) (.cv e)))
            (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv e)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_f, fresh_c_ne_d, fresh_c_ne_r,
            fresh_c_ne_e, or_false, not_false_eq_true])
    have dv_cache_0069 :
      e ∉
        ((Wff.imp (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
              (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z))))
            (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_e_ne_a, fresh_e_ne_f, fresh_e_ne_b, fresh_e_ne_r,
            fresh_e_ne_z, or_false, not_false_eq_true])
    have dv_cache_0070 :
      d ∉
        ((Wff.imp (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
              (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (.cv e)))
            (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv e)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_f, fresh_d_ne_b, fresh_d_ne_r,
            fresh_d_ne_e, or_false, not_false_eq_true])
    have dv_cache_0071 :
      g ∉
        ((Wff.imp (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) (syn_wb (syn_wbr (.cv a)
                (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
                (.cv z)) (syn_wa (syn_wa (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
                  (.classMem (.cv z) (syn_crn (syn_ccnv (.cv f)))))
                (syn_wbr (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (.cv r)
                  (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv z))))))).fv :=
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
            Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_a, fresh_g_ne_z, fresh_g_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0072 :
      z ∉
        ((syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_f, fresh_z_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0073 :
      b ∉
        ((syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))).fv :=
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
    have dv_cache_0074 : b ∉ (syn_wtru).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0075 : a ≠ b := by exact (show a ≠ b from (by exact fresh_a_ne_b))
    have dv_cache_0076 : z ∉ ((Wff.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_c, fresh_z_ne_f, fresh_z_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0077 : a ∉ ((Wff.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_c, fresh_a_ne_f, fresh_a_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0078 : b ∉ ((Wff.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_c, fresh_b_ne_f, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0079 : z ∉ ((Class.cv d)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_z_ne_d, not_false_eq_true])
    have dv_cache_0080 : z ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_z_ne_x, not_false_eq_true])
    have dv_cache_0081 : a ∉ ((Class.cv d)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_d, not_false_eq_true])
    have dv_cache_0082 : d ≠ a := by exact (show d ≠ a from (by exact fresh_d_ne_a))
    have dv_cache_0083 : d ≠ z := by exact (show d ≠ z from (by exact fresh_d_ne_z))
    have dv_cache_0084 : c ≠ z := by exact (show c ≠ z from (by exact fresh_c_ne_z))
    have dv_cache_0085 : a ≠ z := by exact (show a ≠ z from (by exact fresh_a_ne_z))
    have dv_cache_0086 : b ≠ z := by exact (show b ≠ z from (by exact fresh_b_ne_z))
    have dv_cache_0087 : d ∉ ((syn_cpwpull (.cv f) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_f, fresh_d_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0088 : d ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_d_ne_x, not_false_eq_true])
    have dv_cache_0089 :
      c ∉
        ((syn_wral a (.cv x) (syn_wral b (.cv x) (syn_wral z (.cv x) (.imp
                  (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
                    (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z)))
                  (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_a,
            fresh_c_ne_b, fresh_c_ne_f, fresh_c_ne_r, fresh_c_ne_z, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0090 :
      d ∉
        ((syn_wral a (.cv x) (syn_wral b (.cv x) (syn_wral z (.cv x) (.imp
                  (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
                    (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z)))
                  (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_x, fresh_d_ne_a,
            fresh_d_ne_b, fresh_d_ne_f, fresh_d_ne_r, fresh_d_ne_z, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0091 :
      g ∉
        ((Wff.imp (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) (syn_wb (syn_wbr (.cv b)
                (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
                (.cv a)) (syn_wa (syn_wa (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f))))
                  (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f)))))
                (syn_wbr (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b)) (.cv r)
                  (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a))))))).fv :=
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
            Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_b, fresh_g_ne_a, fresh_g_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0092 : c ∉ ((Wff.classEq (.cv e) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_e, fresh_c_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0093 : d ∉ ((Wff.classEq (.cv e) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_e, fresh_d_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0094 : d ∉ ((Class.cv g)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_d_ne_g, not_false_eq_true])
    have dv_cache_0095 : c ∉ ((Class.cv g)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_g, not_false_eq_true])
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
    have dv_cache_0099 :
      e ∉
        ((syn_wral c (.cv y) (syn_wral d (.cv y) (.imp (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d))
                  (syn_wbr (.cv d) (.cv r) (.cv c))) (.objEq c d))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_y, fresh_e_ne_c,
            fresh_e_ne_d, fresh_e_ne_r, or_false, and_false, not_false_eq_true])
    have dv_cache_0100 :
      g ∉
        ((syn_wral c (.cv y) (syn_wral d (.cv y) (.imp (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d))
                  (syn_wbr (.cv d) (.cv r) (.cv c))) (.objEq c d))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_g_ne_y, fresh_g_ne_c,
            fresh_g_ne_d, fresh_g_ne_r, or_false, and_false, not_false_eq_true])
    have dv_cache_0101 : e ≠ g := by exact (show e ≠ g from (by exact fresh_e_ne_g))
    have dv_cache_0102 :
      c ∉
        ((Wff.imp (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
              (syn_wbr (.cv d) (.cv r) (syn_cfv (.cv f) (.cv a))))
            (.classEq (syn_cfv (.cv f) (.cv a)) (.cv d)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_f, fresh_c_ne_d, fresh_c_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0103 :
      d ∉
        ((Wff.imp (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
              (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))))
            (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_f, fresh_d_ne_b, fresh_d_ne_r,
            or_false, not_false_eq_true])
    let syntaxFormula0012 : Wff :=
      (syn_w3a (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (.cv x)))
    let syntaxFormula0013 : Wff :=
      (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z)))
    let syntaxFormula0014 : Wff := (syn_w3a syn_wtru syntaxFormula0012 syntaxFormula0013)
    let syntaxFormula0038 : Wff :=
      (syn_wa (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
    let syntaxFormula0039 : Wff :=
      (.imp (syn_wa (syn_wbr (.cv c) (.cv g) (.cv d)) (syn_wbr (.cv d) (.cv g) (.cv e)))
        (syn_wbr (.cv c) (.cv g) (.cv e)))
    let syntaxFormula0040 : Wff :=
      (.imp (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv e)))
        (syn_wbr (.cv c) (.cv r) (.cv e)))
    let syntaxFormula0041 : Wff := (syn_wral e (.cv h) syntaxFormula0040)
    let syntaxFormula0042 : Wff := (syn_wral e (.cv y) syntaxFormula0040)
    let syntaxFormula0043 : Wff := (syn_wral d (.cv y) syntaxFormula0042)
    let syntaxFormula0044 : Wff := (syn_wral c (.cv y) syntaxFormula0043)
    let syntaxFormula0045 : Wff :=
      (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (syn_wbr (.cv d) (.cv r) (.cv e)))
    let syntaxFormula0046 : Wff :=
      (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (.cv e)))
    let syntaxFormula0047 : Wff :=
      (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z))))
    let syntaxFormula0048 : Wff :=
      (.imp syntaxFormula0047
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))))
    let syntaxFormula0049 : Wff :=
      (syn_wa (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))))
    let syntaxFormula0050 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_crn (.cv g))) (.classMem (.cv z) (syn_crn (.cv g))))
    let syntaxFormula0051 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv z) (syn_crn (syn_ccnv (.cv f)))))
    let syntaxFormula0052 : Wff :=
      (syn_wbr (syn_cfv (syn_ccnv (.cv g)) (.cv a)) (.cv r)
        (syn_cfv (syn_ccnv (.cv g)) (.cv z)))
    let syntaxFormula0053 : Wff :=
      (syn_wbr (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (.cv r)
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv z)))
    let syntaxFormula0054 : Wff :=
      (syn_wbr (.cv a)
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f)))) (.cv z))
    let syntaxFormula0055 : Wff := (syn_wa syntaxFormula0050 syntaxFormula0052)
    let syntaxFormula0056 : Wff := (syn_wa syntaxFormula0051 syntaxFormula0053)
    let syntaxFormula0057 : Wff :=
      (syn_wb (syn_wbr (.cv a) (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g))) (.cv z))
        syntaxFormula0055)
    let syntaxFormula0058 : Wff := (syn_wb syntaxFormula0054 syntaxFormula0056)
    let syntaxFormula0059 : Wff :=
      (syn_wa (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv z) (syn_cdm (.cv f))))
    let syntaxFormula0060 : Wff :=
      (syn_wa syntaxFormula0059
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))))
    let syntaxFormula0061 : Wff :=
      (.imp syntaxFormula0013 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)))
    let syntaxFormula0062 : Wff := (.imp (.classMem (.cv z) (.cv x)) syntaxFormula0061)
    let syntaxFormula0063 : Wff :=
      (.imp (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) syntaxFormula0062)
    let syntaxFormula0064 : Wff := (.all z syntaxFormula0062)
    let syntaxFormula0065 : Wff :=
      (.imp (.all z (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
        syntaxFormula0064)
    let syntaxFormula0066 : Wff :=
      (.imp (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) syntaxFormula0064)
    let syntaxFormula0067 : Wff := (syn_wral z (.cv x) syntaxFormula0061)
    let syntaxFormula0068 : Wff :=
      (.imp (syn_wa (syn_wbr (.cv a) (.cv c) (.cv b)) (syn_wbr (.cv b) (.cv c) (.cv z)))
        (syn_wbr (.cv a) (.cv c) (.cv z)))
    let syntaxFormula0069 : Wff := (syn_wral z (.cv d) syntaxFormula0061)
    let syntaxFormula0070 : Wff := (syn_wral b (.cv d) syntaxFormula0069)
    let syntaxFormula0071 : Wff := (syn_wral b (.cv x) syntaxFormula0067)
    let syntaxFormula0072 : Wff := (syn_wral a (.cv x) syntaxFormula0071)
    let syntaxFormula0073 : Wff :=
      (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
    let syntaxFormula0074 : Wff :=
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0073)
    let syntaxFormula0075 : Wff :=
      (syn_wa (.classMem (.cv b) (syn_crn (.cv g))) (.classMem (.cv a) (syn_crn (.cv g))))
    let syntaxFormula0076 : Wff :=
      (syn_wa (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f)))))
    let syntaxFormula0077 : Wff :=
      (syn_wbr (syn_cfv (syn_ccnv (.cv g)) (.cv b)) (.cv r)
        (syn_cfv (syn_ccnv (.cv g)) (.cv a)))
    let syntaxFormula0078 : Wff :=
      (syn_wbr (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b)) (.cv r)
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)))
    let syntaxFormula0079 : Wff :=
      (syn_wbr (.cv b)
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f)))) (.cv a))
    let syntaxFormula0080 : Wff := (syn_wa syntaxFormula0075 syntaxFormula0077)
    let syntaxFormula0081 : Wff := (syn_wa syntaxFormula0076 syntaxFormula0078)
    let syntaxFormula0082 : Wff :=
      (syn_wb (syn_wbr (.cv b) (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g))) (.cv a))
        syntaxFormula0080)
    let syntaxFormula0083 : Wff := (syn_wb syntaxFormula0079 syntaxFormula0081)
    let syntaxFormula0084 : Wff :=
      (syn_wa (.classMem (.cv b) (syn_cdm (.cv f))) (.classMem (.cv a) (syn_cdm (.cv f))))
    let syntaxFormula0085 : Wff :=
      (syn_wa syntaxFormula0084
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))))
    let syntaxFormula0086 : Wff :=
      (syn_wa (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))))
    let syntaxFormula0087 : Wff :=
      (.imp (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
        (.classEq (.cv c) (.cv d)))
    let syntaxFormula0088 : Wff := (syn_wral d (.cv y) syntaxFormula0087)
    let syntaxFormula0089 : Wff := (syn_wral c (.cv y) syntaxFormula0088)
    let syntaxFormula0090 : Wff :=
      (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (syn_wbr (.cv d) (.cv r) (syn_cfv (.cv f) (.cv a))))
    let syntaxFormula0091 : Wff :=
      (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))))
    let syntaxFormula0092 : Wff :=
      (.imp syntaxFormula0091 (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b))))
    let syntaxFormula0093 : Wff := (.imp syntaxFormula0089 syntaxFormula0092)
    let syntaxFormula0094 : Wff :=
      (syn_wa (syn_wf1 (.cv f) (.cv x) (.cv y))
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
    have p0295 :=
      @g_imbi12d (.classEq (.cv g) (.cv r))
        (syn_wa (syn_wbr (.cv c) (.cv g) (.cv d)) (syn_wbr (.cv d) (.cv g) (.cv e)))
        (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv e)))
        (syn_wbr (.cv c) (.cv g) (.cv e)) (syn_wbr (.cv c) (.cv r) (.cv e)) p0293 p0294
    have p0296 :=
      @g_ralbidv (.classEq (.cv g) (.cv r)) syntaxFormula0039 syntaxFormula0040 e (.cv h)
        dv_cache_0039 p0295
    have p0297 :=
      @g_n_2ralbidv (.classEq (.cv g) (.cv r)) (syn_wral e (.cv h) syntaxFormula0039)
        syntaxFormula0041 c d (.cv h) (.cv h) dv_cache_0040 dv_cache_0041 p0296
    have p0298 := @g_raleq syntaxFormula0040 e (.cv h) (.cv y) dv_cache_0042 dv_cache_0043
    have p0299 :=
      @g_raleqbi1dv syntaxFormula0041 syntaxFormula0042 d (.cv h) (.cv y) dv_cache_0044
        dv_cache_0010 p0298
    have p0300 :=
      @g_raleqbi1dv (syn_wral d (.cv h) syntaxFormula0041) syntaxFormula0043 c (.cv h)
        (.cv y) dv_cache_0045 dv_cache_0009 p0299
    have p0301 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans c d e g h
        dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050
        dv_cache_0051 dv_cache_0052 dv_cache_0013 dv_cache_0053 dv_cache_0054
    have p0302 :=
      @g_brabg
        (syn_wral c (.cv h) (syn_wral d (.cv h) (syn_wral e (.cv h) syntaxFormula0039)))
        (syn_wral c (.cv h) (syn_wral d (.cv h) syntaxFormula0041)) syntaxFormula0044 g h
        (.cv r) (.cv y) (syn_cvv) (syn_cvv) (syn_ctrans) dv_cache_0055 dv_cache_0056
        dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 p0297 p0300
        p0301
    have p0303 :=
      @g_syl (syn_wbr (.cv r) (syn_ctrans) (.cv y))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
        (syn_wb (syn_wbr (.cv r) (syn_ctrans) (.cv y)) syntaxFormula0044) p0290 p0302
    have p0304 := @g_ibi (syn_wbr (.cv r) (syn_ctrans) (.cv y)) syntaxFormula0044 p0303
    have p0305 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014 (syn_wbr (.cv r) (syn_ctrans) (.cv y)) syntaxFormula0044 p0289
        p0304
    have p0309 :=
      @g_syl5 syntaxFormula0014 (.classMem (.cv a) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y)) p0137 p0027
    have p0311 :=
      @g_simp2 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (.cv x))
    have p0312 :=
      @g_syl syntaxFormula0014 syntaxFormula0012 (.classMem (.cv b) (.cv x)) p0135 p0311
    have p0313 := @g_id (.classMem (.cv b) (.cv x))
    have p0314 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf (.cv f) (.cv x) (.cv y)) (.classMem (.cv b) (.cv x)) p0022
    have p0315 := @g_ffvelrn (.cv x) (.cv y) (.cv b) (.cv f)
    have p0316 :=
      @g_ex (syn_wf (.cv f) (.cv x) (.cv y)) (.classMem (.cv b) (.cv x))
        (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y)) p0315
    have p0317 :=
      @g_syl56 (.classMem (.cv b) (.cv x)) (.classMem (.cv b) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf (.cv f) (.cv x) (.cv y))
        (.imp (.classMem (.cv b) (.cv x)) (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y)))
        p0313 p0314 p0316
    have p0318 :=
      @g_pm2_43d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv b) (.cv x)) (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y)) p0317
    have p0319 :=
      @g_syl5 syntaxFormula0014 (.classMem (.cv b) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y)) p0312 p0318
    have p0323 := @g_id (.classMem (.cv z) (.cv x))
    have p0324 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf (.cv f) (.cv x) (.cv y)) (.classMem (.cv z) (.cv x)) p0022
    have p0325 := @g_ffvelrn (.cv x) (.cv y) (.cv z) (.cv f)
    have p0326 :=
      @g_ex (syn_wf (.cv f) (.cv x) (.cv y)) (.classMem (.cv z) (.cv x))
        (.classMem (syn_cfv (.cv f) (.cv z)) (.cv y)) p0325
    have p0327 :=
      @g_syl56 (.classMem (.cv z) (.cv x)) (.classMem (.cv z) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf (.cv f) (.cv x) (.cv y))
        (.imp (.classMem (.cv z) (.cv x)) (.classMem (syn_cfv (.cv f) (.cv z)) (.cv y)))
        p0323 p0324 p0326
    have p0328 :=
      @g_pm2_43d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv z) (.cv x)) (.classMem (syn_cfv (.cv f) (.cv z)) (.cv y)) p0327
    have p0329 :=
      @g_syl5 syntaxFormula0014 (.classMem (.cv z) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (syn_cfv (.cv f) (.cv z)) (.cv y)) p0140 p0328
    have p0330 :=
      @g_n_3jcad
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014 (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y))
        (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y))
        (.classMem (syn_cfv (.cv f) (.cv z)) (.cv y)) p0309 p0319 p0329
    have p0331 := @g_breq1 (.cv c) (syn_cfv (.cv f) (.cv a)) (.cv d) (.cv r)
    have p0332 :=
      @g_anbi1d (.classEq (.cv c) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (.cv c) (.cv r) (.cv d))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (syn_wbr (.cv d) (.cv r) (.cv e)) p0331
    have p0333 := @g_breq1 (.cv c) (syn_cfv (.cv f) (.cv a)) (.cv e) (.cv r)
    have p0334 :=
      @g_imbi12d (.classEq (.cv c) (syn_cfv (.cv f) (.cv a)))
        (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv e)))
        syntaxFormula0045 (syn_wbr (.cv c) (.cv r) (.cv e))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv e)) p0332 p0333
    have p0335 :=
      @g_breq2 (.cv d) (syn_cfv (.cv f) (.cv b)) (syn_cfv (.cv f) (.cv a)) (.cv r)
    have p0336 := @g_breq1 (.cv d) (syn_cfv (.cv f) (.cv b)) (.cv e) (.cv r)
    have p0337 :=
      @g_anbi12d (.classEq (.cv d) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (.cv d) (.cv r) (.cv e))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (.cv e)) p0335 p0336
    have p0338 :=
      @g_imbi1d (.classEq (.cv d) (syn_cfv (.cv f) (.cv b))) syntaxFormula0045
        syntaxFormula0046 (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv e)) p0337
    have p0339 :=
      @g_breq2 (.cv e) (syn_cfv (.cv f) (.cv z)) (syn_cfv (.cv f) (.cv b)) (.cv r)
    have p0340 :=
      @g_anbi2d (.classEq (.cv e) (syn_cfv (.cv f) (.cv z)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (.cv e))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))) p0339
    have p0341 :=
      @g_breq2 (.cv e) (syn_cfv (.cv f) (.cv z)) (syn_cfv (.cv f) (.cv a)) (.cv r)
    have p0342 :=
      @g_imbi12d (.classEq (.cv e) (syn_cfv (.cv f) (.cv z))) syntaxFormula0046
        syntaxFormula0047 (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv e))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))) p0340 p0341
    have p0343 :=
      @g_rspc3v syntaxFormula0040 syntaxFormula0048
        (.imp syntaxFormula0045 (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv e)))
        (.imp syntaxFormula0046 (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv e))) c d e
        (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)) (syn_cfv (.cv f) (.cv z))
        (.cv y) (.cv y) (.cv y) dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
        dv_cache_0066 dv_cache_0067 dv_cache_0009 dv_cache_0009 dv_cache_0010
        dv_cache_0009 dv_cache_0010 dv_cache_0043 dv_cache_0068 dv_cache_0069
        dv_cache_0070 dv_cache_0013 dv_cache_0053 dv_cache_0054 p0334 p0338 p0342
    have p0344 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014
        (syn_w3a (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y))
          (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y))
          (.classMem (syn_cfv (.cv f) (.cv z)) (.cv y)))
        (.imp syntaxFormula0044 syntaxFormula0048) p0330 p0343
    have p0345 :=
      @g_mpdd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014 syntaxFormula0044 syntaxFormula0048 p0305 p0344
    have p0346 :=
      @g_syl7bi
        (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
          (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
        syntaxFormula0047
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))) p0283 p0345
    have p0347 :=
      @g_exp4a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))) p0346
    have p0348 :=
      Nominal.ax2 (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z)))
    have p0349 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014
        (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
          (.imp (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
            (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z)))))
        (.imp (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
            (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
          (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
            (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z)))))
        p0347 p0348
    have p0350 :=
      @g_mpdd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014
        (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
          (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
        (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
          (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))))
        p0282 p0349
    have p0351 :=
      @g_mpdd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv z)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))) p0212 p0350
    have p0352 :=
      @g_pm3_2 (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z)))
    have p0353 :=
      @g_syl9
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z)))
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x))) syntaxFormula0049
        p0351 p0352
    have p0354 :=
      @g_syl5 syntaxFormula0014
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x)))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.imp syntaxFormula0014 syntaxFormula0049) p0141 p0353
    have p0355 :=
      @g_pm2_43d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014 syntaxFormula0049 p0354
    have p0357 :=
      @g_breqi (.cv a) (.cv z) (syn_cpwpull (.cv f) (.cv r))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p0360 :=
      @g_breqi (.cv a) (.cv z)
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p0370 :=
      @g_breqd (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g)))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
        (.cv a) (.cv z) p0055
    have p0377 :=
      @g_anbi12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (.classMem (.cv a) (syn_crn (.cv g)))
        (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv z) (syn_crn (.cv g)))
        (.classMem (.cv z) (syn_crn (syn_ccnv (.cv f)))) p0059 p0165
    have p0384 :=
      @g_breq12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_cfv (syn_ccnv (.cv g)) (.cv a))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a))
        (syn_cfv (syn_ccnv (.cv g)) (.cv z))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv z)) (.cv r) p0066 p0172
    have p0385 :=
      @g_anbi12d (.classEq (.cv g) (syn_ccnv (.cv f))) syntaxFormula0050 syntaxFormula0051
        syntaxFormula0052 syntaxFormula0053 p0377 p0384
    have p0386 :=
      @g_bibi12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_wbr (.cv a) (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g))) (.cv z))
        syntaxFormula0054 syntaxFormula0055 syntaxFormula0056 p0370 p0385
    have p0387 :=
      @g_imbi12d (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfun (syn_ccnv (.cv g)))
        (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0057 syntaxFormula0058 p0050
        p0386
    have p0388 := @g_hwtrnbrd a z g r dv_cache_0016 dv_cache_0036
    have p0389 :=
      @g_vtoclg (.imp (syn_wfun (syn_ccnv (.cv g))) syntaxFormula0057)
        (.imp (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0058) g
        (syn_ccnv (.cv f)) (syn_cvv) dv_cache_0017 dv_cache_0071 p0387 p0388
    have p0390 := Nominal.mp p0047 p0389
    have p0391 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0058 p0045 p0390
    have p0402 :=
      @g_anbi12i (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv a) (syn_cdm (.cv f)))
        (.classMem (.cv z) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv z) (syn_cdm (.cv f))) p0082 p0190
    have p0407 :=
      @g_breq12i (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (syn_cfv (.cv f) (.cv a))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv z)) (syn_cfv (.cv f) (.cv z)) (.cv r)
        p0090 p0195
    have p0408 :=
      @g_anbi12i syntaxFormula0051 syntaxFormula0059 syntaxFormula0053
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))) p0402 p0407
    have p0409 :=
      @g_syl6bb
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0054 syntaxFormula0056 syntaxFormula0060 p0391 p0408
    have p0410 :=
      @g_syl5bbr
        (syn_wbr (.cv a) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (.cv z))
        syntaxFormula0054
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0060 p0360 p0409
    have p0411 :=
      @g_syl5bb (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
        (syn_wbr (.cv a) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (.cv z))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0060 p0357 p0410
    have p0412 :=
      @g_anbi12d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv a) (.cv x))
        (.classMem (.cv z) (syn_cdm (.cv f))) (.classMem (.cv z) (.cv x)) p0102 p0202
    have p0413 :=
      @g_anbi1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0059 (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z))) p0412
    have p0414 :=
      @g_biid (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z)))
    have p0415 :=
      @g_anbi2i (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv z)))
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x))) p0414
    have p0416 :=
      @g_a1ii
        (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
          (syn_wb syntaxFormula0060 syntaxFormula0049))
        (syn_wb syntaxFormula0049 syntaxFormula0049) p0413 p0415
    have p0417 :=
      @g_bitrd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) syntaxFormula0060
        syntaxFormula0049 p0411 p0416
    have p0418 :=
      @g_sylibrd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0014 syntaxFormula0049
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) p0355 p0417
    have p0419 :=
      @g_n_3expd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0012 syntaxFormula0013
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) p0418
    have p0420 :=
      @g_syl7
        (syn_wa (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
          (.classMem (.cv z) (.cv x)))
        syntaxFormula0012
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0061 p0134 p0419
    have p0421 :=
      @g_exp4a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv z) (.cv x)) syntaxFormula0061 p0420
    have p0422 :=
      @g_alimdv
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0063 z dv_cache_0072 p0421
    have p0423 :=
      @g_alim (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0062 z
    have p0424 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.all z syn_wtru) (.all z syntaxFormula0063) syntaxFormula0065 p0422 p0423
    have p0425 :=
      @g_syl5 syn_wtru (.all z syn_wtru)
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0065 p0132 p0424
    have p0426 :=
      @g_a1dd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0065
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) p0425
    have p0427 :=
      Nominal.ax2 (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.all z (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
        syntaxFormula0064
    have p0428 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru
        (.imp (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
          syntaxFormula0065)
        (.imp (.imp (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
            (.all z (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))))
          syntaxFormula0066)
        p0426 p0427
    have p0429 :=
      @g_mpdi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru
        (.imp (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
          (.all z (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))))
        syntaxFormula0066 p0130 p0428
    have p0430 := (Nominal.biimpRefl syntaxFormula0067)
    have p0431 := @g_biimpri syntaxFormula0067 syntaxFormula0064 p0430
    have p0432 :=
      @g_syl8
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0064 syntaxFormula0067 p0429 p0431
    have p0433 :=
      @g_ralrimdvv
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0067 a b (.cv x) (.cv x) dv_cache_0028 dv_cache_0019
        dv_cache_0073 dv_cache_0020 dv_cache_0074 dv_cache_0075 p0432
    have p0437 := @g_breq (.cv a) (.cv b) (.cv c) (syn_cpwpull (.cv f) (.cv r))
    have p0438 := @g_breq (.cv b) (.cv z) (.cv c) (syn_cpwpull (.cv f) (.cv r))
    have p0439 :=
      @g_anbi12d (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wbr (.cv a) (.cv c) (.cv b))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (.cv c) (.cv z))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) p0437 p0438
    have p0440 := @g_breq (.cv a) (.cv z) (.cv c) (syn_cpwpull (.cv f) (.cv r))
    have p0441 :=
      @g_imbi12d (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wa (syn_wbr (.cv a) (.cv c) (.cv b)) (syn_wbr (.cv b) (.cv c) (.cv z)))
        syntaxFormula0013 (syn_wbr (.cv a) (.cv c) (.cv z))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) p0439 p0440
    have p0442 :=
      @g_ralbidv (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r))) syntaxFormula0068
        syntaxFormula0061 z (.cv d) dv_cache_0076 p0441
    have p0443 :=
      @g_n_2ralbidv (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wral z (.cv d) syntaxFormula0068) syntaxFormula0069 a b (.cv d) (.cv d)
        dv_cache_0077 dv_cache_0078 p0442
    have p0444 := @g_raleq syntaxFormula0061 z (.cv d) (.cv x) dv_cache_0079 dv_cache_0080
    have p0445 :=
      @g_raleqbi1dv syntaxFormula0069 syntaxFormula0067 b (.cv d) (.cv x) dv_cache_0002
        dv_cache_0028 p0444
    have p0446 :=
      @g_raleqbi1dv syntaxFormula0070 syntaxFormula0071 a (.cv d) (.cv x) dv_cache_0081
        dv_cache_0023 p0445
    have p0447 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_trans a b z c d
        dv_cache_0004 dv_cache_0082 dv_cache_0005 dv_cache_0083 dv_cache_0024
        dv_cache_0006 dv_cache_0084 dv_cache_0075 dv_cache_0085 dv_cache_0086
    have p0448 :=
      @g_brabg
        (syn_wral a (.cv d) (syn_wral b (.cv d) (syn_wral z (.cv d) syntaxFormula0068)))
        (syn_wral a (.cv d) syntaxFormula0070) syntaxFormula0072 c d
        (syn_cpwpull (.cv f) (.cv r)) (.cv x) (syn_cvv) (syn_cvv) (syn_ctrans)
        dv_cache_0027 dv_cache_0087 dv_cache_0029 dv_cache_0088 dv_cache_0089
        dv_cache_0090 dv_cache_0013 p0443 p0446 p0447
    have p0449 :=
      @g_syl2anc syn_wtru (.classMem (syn_cpwpull (.cv f) (.cv r)) (syn_cvv))
        (.classMem (.cv x) (syn_cvv))
        (syn_wb (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_ctrans) (.cv x)) syntaxFormula0072)
        p0115 p0117 p0448
    have p0450 :=
      @g_biimprd syn_wtru (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_ctrans) (.cv x))
        syntaxFormula0072 p0449
    have p0451 :=
      @g_sylcom
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0072
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_ctrans) (.cv x)) p0433 p0450
    have p0452 :=
      @g_mpi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_ctrans) (.cv x)) p0000 p0451
    have p0454 :=
      @g_simp3 syn_wtru (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0073
    have p0455 :=
      @g_simprd syntaxFormula0074 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p0454
    have p0457 :=
      @g_breqi (.cv b) (.cv a) (syn_cpwpull (.cv f) (.cv r))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p0460 :=
      @g_breqi (.cv b) (.cv a)
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p0470 :=
      @g_breqd (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g)))
        (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (syn_ccnv (syn_ccnv (.cv f))))
        (.cv b) (.cv a) p0055
    have p0477 :=
      @g_anbi12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (.classMem (.cv b) (syn_crn (.cv g)))
        (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv a) (syn_crn (.cv g)))
        (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f)))) p0162 p0059
    have p0484 :=
      @g_breq12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_cfv (syn_ccnv (.cv g)) (.cv b))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b))
        (syn_cfv (syn_ccnv (.cv g)) (.cv a))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (.cv r) p0169 p0066
    have p0485 :=
      @g_anbi12d (.classEq (.cv g) (syn_ccnv (.cv f))) syntaxFormula0075 syntaxFormula0076
        syntaxFormula0077 syntaxFormula0078 p0477 p0484
    have p0486 :=
      @g_bibi12d (.classEq (.cv g) (syn_ccnv (.cv f)))
        (syn_wbr (.cv b) (syn_ccom (syn_ccom (.cv g) (.cv r)) (syn_ccnv (.cv g))) (.cv a))
        syntaxFormula0079 syntaxFormula0080 syntaxFormula0081 p0470 p0485
    have p0487 :=
      @g_imbi12d (.classEq (.cv g) (syn_ccnv (.cv f))) (syn_wfun (syn_ccnv (.cv g)))
        (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0082 syntaxFormula0083 p0050
        p0486
    have p0488 := @g_hwtrnbrd b a g r dv_cache_0035 dv_cache_0016
    have p0489 :=
      @g_vtoclg (.imp (syn_wfun (syn_ccnv (.cv g))) syntaxFormula0082)
        (.imp (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0083) g
        (syn_ccnv (.cv f)) (syn_cvv) dv_cache_0017 dv_cache_0091 p0487 p0488
    have p0490 := Nominal.mp p0047 p0489
    have p0491 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfun (syn_ccnv (syn_ccnv (.cv f)))) syntaxFormula0083 p0045 p0490
    have p0502 :=
      @g_anbi12i (.classMem (.cv b) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv b) (syn_cdm (.cv f)))
        (.classMem (.cv a) (syn_crn (syn_ccnv (.cv f))))
        (.classMem (.cv a) (syn_cdm (.cv f))) p0185 p0082
    have p0507 :=
      @g_breq12i (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv b)) (syn_cfv (.cv f) (.cv b))
        (syn_cfv (syn_ccnv (syn_ccnv (.cv f))) (.cv a)) (syn_cfv (.cv f) (.cv a)) (.cv r)
        p0193 p0090
    have p0508 :=
      @g_anbi12i syntaxFormula0076 syntaxFormula0084 syntaxFormula0078
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))) p0502 p0507
    have p0509 :=
      @g_syl6bb
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0079 syntaxFormula0081 syntaxFormula0085 p0491 p0508
    have p0510 :=
      @g_syl5bbr
        (syn_wbr (.cv b) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (.cv a))
        syntaxFormula0079
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0085 p0460 p0509
    have p0511 :=
      @g_syl5bb (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (syn_wbr (.cv b) (syn_ccom (syn_ccom (syn_ccnv (.cv f)) (.cv r)) (.cv f)) (.cv a))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0085 p0457 p0510
    have p0512 :=
      @g_anbi12d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv b) (syn_cdm (.cv f))) (.classMem (.cv b) (.cv x))
        (.classMem (.cv a) (syn_cdm (.cv f))) (.classMem (.cv a) (.cv x)) p0201 p0102
    have p0513 :=
      @g_anbi1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0084 (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))) p0512
    have p0514 :=
      @g_biid (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
    have p0515 :=
      @g_anbi2i (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x))) p0514
    have p0516 :=
      @g_a1ii
        (.imp (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
          (syn_wb syntaxFormula0085 syntaxFormula0086))
        (syn_wb syntaxFormula0086 syntaxFormula0086) p0513 p0515
    have p0517 :=
      @g_bitrd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) syntaxFormula0085
        syntaxFormula0086 p0511 p0516
    have p0518 :=
      @g_biimpd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) syntaxFormula0086 p0517
    have p0519 :=
      @g_syl5 syntaxFormula0074 (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0086 p0455 p0518
    have p0520 :=
      @g_ancom (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
    have p0521 :=
      @g_syl6ib
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074 syntaxFormula0086
        (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
          (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x))))
        p0519 p0520
    have p0522 :=
      @g_simpl (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
    have p0523 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074
        (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
          (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x))))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))) p0521 p0522
    have p0525 :=
      @g_simpld syntaxFormula0074 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p0454
    have p0526 :=
      @g_syl5 syntaxFormula0074 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0038 p0525 p0278
    have p0527 :=
      @g_ancom (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
    have p0528 :=
      @g_syl6ib
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074 syntaxFormula0038
        (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
          (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
        p0526 p0527
    have p0529 :=
      @g_simpl (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
    have p0530 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074
        (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
          (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))) p0528 p0529
    have p0531 :=
      @g_a1dd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))) p0530
    have p0532 :=
      @g_ancom (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
    have p0533 := @g_wppweantisym (.cv y) (.cv r)
    have p0534 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cantisym) (.cv y)) p0004
        p0533
    have p0535 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv r) (syn_cantisym) (.cv y)) syntaxFormula0074 p0534
    have p0536 := @g_brex (.cv r) (.cv y) (syn_cantisym)
    have p0537 := @g_breq (.cv c) (.cv d) (.cv e) (.cv r)
    have p0538 := @g_breq (.cv d) (.cv c) (.cv e) (.cv r)
    have p0539 :=
      @g_anbi12d (.classEq (.cv e) (.cv r)) (syn_wbr (.cv c) (.cv e) (.cv d))
        (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv e) (.cv c))
        (syn_wbr (.cv d) (.cv r) (.cv c)) p0537 p0538
    have p0540 :=
      @g_imbi1d (.classEq (.cv e) (.cv r))
        (syn_wa (syn_wbr (.cv c) (.cv e) (.cv d)) (syn_wbr (.cv d) (.cv e) (.cv c)))
        (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
        (.objEq c d) p0539
    have p0541 :=
      @g_n_2ralbidv (.classEq (.cv e) (.cv r))
        (.imp (syn_wa (syn_wbr (.cv c) (.cv e) (.cv d)) (syn_wbr (.cv d) (.cv e) (.cv c)))
          (.objEq c d))
        (.imp (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
          (.objEq c d))
        c d (.cv g) (.cv g) dv_cache_0092 dv_cache_0093 p0540
    have p0542 :=
      @g_raleq
        (.imp (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
          (.objEq c d))
        d (.cv g) (.cv y) dv_cache_0094 dv_cache_0010
    have p0543 :=
      @g_raleqbi1dv
        (syn_wral d (.cv g) (.imp
            (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
            (.objEq c d)))
        (syn_wral d (.cv y) (.imp
            (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
            (.objEq c d)))
        c (.cv g) (.cv y) dv_cache_0095 dv_cache_0009 p0542
    have p0544 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_antisym c d e g
        dv_cache_0052 dv_cache_0050 dv_cache_0051 dv_cache_0096 dv_cache_0097
        dv_cache_0013
    have p0545 :=
      @g_brabg
        (syn_wral c (.cv g) (syn_wral d (.cv g) (.imp
              (syn_wa (syn_wbr (.cv c) (.cv e) (.cv d)) (syn_wbr (.cv d) (.cv e) (.cv c)))
              (.objEq c d))))
        (syn_wral c (.cv g) (syn_wral d (.cv g) (.imp
              (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
              (.objEq c d))))
        (syn_wral c (.cv y) (syn_wral d (.cv y) (.imp
              (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
              (.objEq c d))))
        e g (.cv r) (.cv y) (syn_cvv) (syn_cvv) (syn_cantisym) dv_cache_0098 dv_cache_0055
        dv_cache_0043 dv_cache_0057 dv_cache_0099 dv_cache_0100 dv_cache_0101 p0541 p0543
        p0544
    have p0546 :=
      @g_syl (syn_wbr (.cv r) (syn_cantisym) (.cv y))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
        (syn_wb (syn_wbr (.cv r) (syn_cantisym) (.cv y)) (syn_wral c (.cv y) (syn_wral d (.cv y)
              (.imp (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
                (.objEq c d)))))
        p0536 p0545
    have p0547 :=
      @g_ibi (syn_wbr (.cv r) (syn_cantisym) (.cv y))
        (syn_wral c (.cv y) (syn_wral d (.cv y) (.imp
              (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
              (.objEq c d))))
        p0546
    have p0548_e01_recanon :
      Nominal.NPrf (.imp (syn_wbr (.cv r) (syn_cantisym) (.cv y)) syntaxFormula0089) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_wbr, syn_cop, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl,
            syn_wrex, syn_wex, syn_cphi, syn_cantisym, syn_copab, syn_wral]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
        p0547
    have p0548 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074 (syn_wbr (.cv r) (syn_cantisym) (.cv y)) syntaxFormula0089 p0535
        p0548_e01_recanon
    have p0549 :=
      @g_simp2 syn_wtru (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0073
    have p0550 :=
      @g_simpld syntaxFormula0074 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        p0549
    have p0551 :=
      @g_syl5 syntaxFormula0074 (.classMem (.cv a) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y)) p0550 p0027
    have p0553 :=
      @g_simprd syntaxFormula0074 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        p0549
    have p0554 :=
      @g_syl5 syntaxFormula0074 (.classMem (.cv b) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y)) p0553 p0318
    have p0555 := @g_breq1 (.cv c) (syn_cfv (.cv f) (.cv a)) (.cv d) (.cv r)
    have p0556 := @g_breq2 (.cv c) (syn_cfv (.cv f) (.cv a)) (.cv d) (.cv r)
    have p0557 :=
      @g_anbi12d (.classEq (.cv c) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (.cv c) (.cv r) (.cv d))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (syn_wbr (.cv d) (.cv r) (.cv c))
        (syn_wbr (.cv d) (.cv r) (syn_cfv (.cv f) (.cv a))) p0555 p0556
    have p0558 := @g_eqeq1 (.cv c) (syn_cfv (.cv f) (.cv a)) (.cv d)
    have p0559_e01_recanon :
      Nominal.NPrf
        (.imp (.classEq (.cv c) (syn_cfv (.cv f) (.cv a)))
          (syn_wb (.objEq c d) (.classEq (syn_cfv (.cv f) (.cv a)) (.cv d)))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_cfv, syn_cio, syn_cuni, syn_wex, syn_wa, syn_csn, syn_wbr,
            syn_cop, syn_cun, syn_cnin, syn_wnan, syn_ccompl, syn_wrex, syn_cphi, syn_wb]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
        p0558
    have p0559 :=
      @g_imbi12d (.classEq (.cv c) (syn_cfv (.cv f) (.cv a)))
        (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
        syntaxFormula0090 (.objEq c d) (.classEq (syn_cfv (.cv f) (.cv a)) (.cv d)) p0557
        p0559_e01_recanon
    have p0560 :=
      @g_breq2 (.cv d) (syn_cfv (.cv f) (.cv b)) (syn_cfv (.cv f) (.cv a)) (.cv r)
    have p0561 :=
      @g_breq1 (.cv d) (syn_cfv (.cv f) (.cv b)) (syn_cfv (.cv f) (.cv a)) (.cv r)
    have p0562 :=
      @g_anbi12d (.classEq (.cv d) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (.cv d) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))) p0560 p0561
    have p0563 := @g_eqeq2 (.cv d) (syn_cfv (.cv f) (.cv b)) (syn_cfv (.cv f) (.cv a))
    have p0564 :=
      @g_imbi12d (.classEq (.cv d) (syn_cfv (.cv f) (.cv b))) syntaxFormula0090
        syntaxFormula0091 (.classEq (syn_cfv (.cv f) (.cv a)) (.cv d))
        (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b))) p0562 p0563
    have p0565 :=
      @g_rspc2v
        (.imp (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
          (.objEq c d))
        syntaxFormula0092
        (.imp syntaxFormula0090 (.classEq (syn_cfv (.cv f) (.cv a)) (.cv d))) c d
        (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)) (.cv y) (.cv y) dv_cache_0062
        dv_cache_0063 dv_cache_0065 dv_cache_0009 dv_cache_0009 dv_cache_0010
        dv_cache_0102 dv_cache_0103 dv_cache_0013 p0559 p0564
    have p0566 :=
      @g_ex (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y))
        (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y))
        (.imp (syn_wral c (.cv y) (syn_wral d (.cv y) (.imp
                (syn_wa (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
                (.objEq c d)))) syntaxFormula0092)
        p0565
    have p0567_e02_recanon :
      Nominal.NPrf
        (.imp (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y))
          (.imp (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0093)) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_cfv, syn_cio, syn_cuni, syn_wex, syn_wa, syn_csn, syn_wbr,
            syn_cop, syn_cun, syn_cnin, syn_wnan, syn_ccompl, syn_wrex, syn_cphi,
            syn_wral]
          simp (config :=
            {
              failIfUnchanged :=
                false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.all
                  apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                    · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                    · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0566
    have p0567 :=
      @g_syl6c
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074 (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y))
        (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0093 p0551 p0554
        p0567_e02_recanon
    have p0568 :=
      @g_mpdd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074 syntaxFormula0089 syntaxFormula0092 p0548 p0567
    have p0569 :=
      @g_syl7bi
        (syn_wa (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
          (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
        syntaxFormula0091
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074 (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)))
        p0532 p0568
    have p0570 :=
      @g_exp4a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b))) p0569
    have p0571 :=
      Nominal.ax2 (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)))
    have p0572 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074
        (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
          (.imp (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
            (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)))))
        (.imp (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
            (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
          (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
            (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)))))
        p0570 p0571
    have p0573 :=
      @g_mpdd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074
        (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
          (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
        (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
          (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b))))
        p0531 p0572
    have p0574 :=
      @g_mpdd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b))) p0523 p0573
    have p0575 := @g_f1of1 (.cv x) (.cv y) (.cv f)
    have p0576 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wf1 (.cv f) (.cv x) (.cv y)) p0018 p0575
    have p0577 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf1 (.cv f) (.cv x) (.cv y)) syntaxFormula0074 p0576
    have p0579 :=
      @g_pm3_2 (syn_wf1 (.cv f) (.cv x) (.cv y))
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
    have p0580 :=
      @g_syl5 syntaxFormula0074
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wf1 (.cv f) (.cv x) (.cv y)) syntaxFormula0094 p0549 p0579
    have p0581 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074 (syn_wf1 (.cv f) (.cv x) (.cv y))
        (.imp syntaxFormula0074 syntaxFormula0094) p0577 p0580
    exact
      continuation p0318 p0331 p0335 p0437 p0440 p0452 p0517 p0537 p0538 p0556 p0561 p0574
        p0581

end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `ReplaySupport.WellOrderPullback3`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_pwpullwesetimpndv_stage3 (x : Var) (y : Var) (f : Var) (r : Var)
    (p0000 : _) (p0004 : _) (p0022 : _) (p0027 : _) (p0042 : _) (p0046 : _) (p0101 : _)
    (p0113 : _) (p0115 : _) (p0116 : _) (p0117 : _) (p0126 : _) (p0277 : _) (p0318 : _)
    (p0331 : _) (p0335 : _) (p0437 : _) (p0452 : _) (p0517 : _) (p0537 : _) (p0538 : _)
    (p0556 : _) (p0561 : _) (p0574 : _) (p0581 : _) {Result : Type}
    (continuation : _ → _ → _ →
            _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → _ → Result) :=
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
    let e : Var := freshVar proofSupport 6
    let h : Var := freshVar proofSupport 7
    let u : Var := freshVar proofSupport 8
    let v : Var := freshVar proofSupport 9
    let w : Var := freshVar proofSupport 10
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
    have fresh_c_ne_y : c ≠ y := by
      intro h
      exact
        fresh_c
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
    have fresh_d_ne_y : d ≠ y := by
      intro h
      exact
        fresh_d
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
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
    have fresh_g_ne_y : g ≠ y := by
      intro h
      exact
        fresh_g
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
    have fresh_g_ne_r : g ≠ r := by
      intro h
      exact fresh_g (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
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
    have fresh_v_ne_r : v ≠ r := by
      intro h
      exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_w : w ∉ proofSupport :=
      by
      change freshVar proofSupport 10 ∉ proofSupport
      exact freshVar_not_mem proofSupport 10
    have fresh_w_ne_r : w ≠ r := by
      intro h
      exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_a_ne_b : a ≠ b :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 1
      exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
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
    have fresh_a_ne_u : a ≠ u :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 8
      exact freshVar_injective proofSupport (i := 0) (j := 8) (by decide)
    have fresh_u_ne_a : u ≠ a := Ne.symm fresh_a_ne_u
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
    have fresh_b_ne_v : b ≠ v :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
    have fresh_b_ne_w : b ≠ w :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 1) (j := 10) (by decide)
    have fresh_c_ne_d : c ≠ d :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 3
      exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
    have fresh_d_ne_c : d ≠ c := Ne.symm fresh_c_ne_d
    have fresh_c_ne_g : c ≠ g :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
    have fresh_g_ne_c : g ≠ c := Ne.symm fresh_c_ne_g
    have fresh_c_ne_e : c ≠ e :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
    have fresh_e_ne_c : e ≠ c := Ne.symm fresh_c_ne_e
    have fresh_c_ne_u : c ≠ u :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 8
      exact freshVar_injective proofSupport (i := 2) (j := 8) (by decide)
    have fresh_u_ne_c : u ≠ c := Ne.symm fresh_c_ne_u
    have fresh_c_ne_v : c ≠ v :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 2) (j := 9) (by decide)
    have fresh_c_ne_w : c ≠ w :=
      by
      change freshVar proofSupport 2 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 2) (j := 10) (by decide)
    have fresh_d_ne_g : d ≠ g :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 4
      exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
    have fresh_g_ne_d : g ≠ d := Ne.symm fresh_d_ne_g
    have fresh_d_ne_e : d ≠ e :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
    have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
    have fresh_d_ne_v : d ≠ v :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 3) (j := 9) (by decide)
    have fresh_v_ne_d : v ≠ d := Ne.symm fresh_d_ne_v
    have fresh_d_ne_w : d ≠ w :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 3) (j := 10) (by decide)
    have fresh_w_ne_d : w ≠ d := Ne.symm fresh_d_ne_w
    have fresh_g_ne_e : g ≠ e :=
      by
      change freshVar proofSupport 4 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
    have fresh_e_ne_g : e ≠ g := Ne.symm fresh_g_ne_e
    have fresh_v_ne_w : v ≠ w :=
      by
      change freshVar proofSupport 9 ≠ freshVar proofSupport 10
      exact freshVar_injective proofSupport (i := 9) (j := 10) (by decide)
    have fresh_w_ne_v : w ≠ v := Ne.symm fresh_v_ne_w
    have dv_cache_0002 : b ∉ ((Class.cv d)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_d, not_false_eq_true])
    have dv_cache_0004 : d ≠ c := by exact (show d ≠ c from (by exact fresh_d_ne_c))
    have dv_cache_0005 : d ≠ b := by exact (show d ≠ b from (by exact fresh_d_ne_b))
    have dv_cache_0006 : c ≠ b := by exact (show c ≠ b from (by exact fresh_c_ne_b))
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
    have dv_cache_0013 : c ≠ d := by exact (show c ≠ d from (by exact fresh_c_ne_d))
    have dv_cache_0019 :
      a ∉
        ((syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))).fv :=
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
    have dv_cache_0020 : a ∉ (syn_wtru).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0023 : a ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_x, not_false_eq_true])
    have dv_cache_0024 : c ≠ a := by exact (show c ≠ a from (by exact fresh_c_ne_a))
    have dv_cache_0027 : c ∉ ((syn_cpwpull (.cv f) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_f, fresh_c_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0028 : b ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_x, not_false_eq_true])
    have dv_cache_0029 : c ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_x, not_false_eq_true])
    have dv_cache_0043 : e ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_e_ne_y, not_false_eq_true])
    have dv_cache_0050 : g ≠ c := by exact (show g ≠ c from (by exact fresh_g_ne_c))
    have dv_cache_0051 : g ≠ d := by exact (show g ≠ d from (by exact fresh_g_ne_d))
    have dv_cache_0052 : g ≠ e := by exact (show g ≠ e from (by exact fresh_g_ne_e))
    have dv_cache_0055 : g ∉ ((Class.cv r)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_g_ne_r, not_false_eq_true])
    have dv_cache_0057 : g ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_g_ne_y, not_false_eq_true])
    have dv_cache_0062 : c ∉ ((syn_cfv (.cv f) (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0063 : d ∉ ((syn_cfv (.cv f) (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0065 : d ∉ ((syn_cfv (.cv f) (.cv b))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_b, fresh_d_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0073 :
      b ∉
        ((syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))).fv :=
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
    have dv_cache_0074 : b ∉ (syn_wtru).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0075 : a ≠ b := by exact (show a ≠ b from (by exact fresh_a_ne_b))
    have dv_cache_0077 : a ∉ ((Wff.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_c, fresh_a_ne_f, fresh_a_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0078 : b ∉ ((Wff.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_c, fresh_b_ne_f, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0081 : a ∉ ((Class.cv d)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_d, not_false_eq_true])
    have dv_cache_0082 : d ≠ a := by exact (show d ≠ a from (by exact fresh_d_ne_a))
    have dv_cache_0087 : d ∉ ((syn_cpwpull (.cv f) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_f, fresh_d_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0088 : d ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_d_ne_x, not_false_eq_true])
    have dv_cache_0092 : c ∉ ((Wff.classEq (.cv e) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_e, fresh_c_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0093 : d ∉ ((Wff.classEq (.cv e) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_e, fresh_d_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0094 : d ∉ ((Class.cv g)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_d_ne_g, not_false_eq_true])
    have dv_cache_0095 : c ∉ ((Class.cv g)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_g, not_false_eq_true])
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
    have dv_cache_0101 : e ≠ g := by exact (show e ≠ g from (by exact fresh_e_ne_g))
    have dv_cache_0104 :
      c ∉
        ((syn_wral a (.cv x) (syn_wral b (.cv x) (.imp
                (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
                  (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
                (.objEq a b))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_a,
            fresh_c_ne_b, fresh_c_ne_f, fresh_c_ne_r, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0105 :
      d ∉
        ((syn_wral a (.cv x) (syn_wral b (.cv x) (.imp
                (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
                  (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
                (.objEq a b))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_x, fresh_d_ne_a,
            fresh_d_ne_b, fresh_d_ne_f, fresh_d_ne_r, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0106 :
      e ∉
        ((syn_wral c (.cv y) (syn_wral d (.cv y) (syn_wo (syn_wbr (.cv c) (.cv r) (.cv d))
                (syn_wbr (.cv d) (.cv r) (.cv c)))))).fv :=
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
            Finset.mem_erase, Finset.mem_singleton, fresh_e_ne_y, fresh_e_ne_c,
            fresh_e_ne_d, fresh_e_ne_r, or_false, and_false, not_false_eq_true])
    have dv_cache_0107 :
      g ∉
        ((syn_wral c (.cv y) (syn_wral d (.cv y) (syn_wo (syn_wbr (.cv c) (.cv r) (.cv d))
                (syn_wbr (.cv d) (.cv r) (.cv c)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_g_ne_y, fresh_g_ne_c,
            fresh_g_ne_d, fresh_g_ne_r, or_false, and_false, not_false_eq_true])
    have dv_cache_0108 :
      c ∉
        ((syn_wo (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
            (syn_wbr (.cv d) (.cv r) (syn_cfv (.cv f) (.cv a))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_f, fresh_c_ne_d, fresh_c_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0109 :
      d ∉
        ((syn_wo (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
            (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_f, fresh_d_ne_b, fresh_d_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0110 :
      c ∉
        ((syn_wral a (.cv x) (syn_wral b (.cv x)
              (syn_wo (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
                (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_a,
            fresh_c_ne_b, fresh_c_ne_f, fresh_c_ne_r, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0111 :
      d ∉
        ((syn_wral a (.cv x) (syn_wral b (.cv x)
              (syn_wo (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
                (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))))).fv :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_x, fresh_d_ne_a,
            fresh_d_ne_b, fresh_d_ne_f, fresh_d_ne_r, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0112 : c ∉ ((Class.cv a)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_a, not_false_eq_true])
    have dv_cache_0113 :
      c ∉
        ((syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_x, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0114 : u ∉ ((syn_cfv (.cv f) (.cv c))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_u_ne_c, fresh_u_ne_f, or_false,
            not_false_eq_true])
    have dv_cache_0115 : u ∉ ((Class.cv y)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_u_ne_y, not_false_eq_true])
    have dv_cache_0116 :
      u ∉ ((Wff.classMem (syn_cfv (.cv f) (.cv c)) (syn_cima (.cv f) (.cv a)))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
            Finset.mem_singleton, fresh_u_ne_c, fresh_u_ne_f, fresh_u_ne_a, or_false,
            not_false_eq_true])
    have dv_cache_0117 :
      c ∉
        ((syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_x, fresh_c_ne_y, fresh_c_ne_f, fresh_c_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0118 :
      c ∉ ((syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_y, fresh_c_ne_u,
            fresh_c_ne_f, fresh_c_ne_a, or_false, and_false, not_false_eq_true])
    have dv_cache_0119 : u ∉ ((syn_cima (.cv f) (.cv a))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_u_ne_f, fresh_u_ne_a, or_false,
            not_false_eq_true])
    have dv_cache_0120 : v ∉ ((Wff.classEq (.cv d) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_v_ne_d, fresh_v_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0121 : w ∉ ((Wff.classEq (.cv d) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_w_ne_d, fresh_w_ne_r, or_false,
            not_false_eq_true])
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
    have dv_cache_0123 : b ∉ ((Wff.classEq (.cv c) (.cv y))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_c, fresh_b_ne_y, or_false,
            not_false_eq_true])
    have dv_cache_0124 : c ≠ w := by exact (show c ≠ w from (by exact fresh_c_ne_w))
    have dv_cache_0125 : c ≠ v := by exact (show c ≠ v from (by exact fresh_c_ne_v))
    have dv_cache_0126 : d ≠ w := by exact (show d ≠ w from (by exact fresh_d_ne_w))
    have dv_cache_0127 : d ≠ v := by exact (show d ≠ v from (by exact fresh_d_ne_v))
    have dv_cache_0128 : b ≠ w := by exact (show b ≠ w from (by exact fresh_b_ne_w))
    have dv_cache_0129 : b ≠ v := by exact (show b ≠ v from (by exact fresh_b_ne_v))
    have dv_cache_0130 : w ≠ v := by exact (show w ≠ v from (by exact fresh_w_ne_v))
    let syntaxFormula0038 : Wff :=
      (syn_wa (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
    let syntaxFormula0073 : Wff :=
      (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
    let syntaxFormula0074 : Wff :=
      (syn_w3a syn_wtru (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0073)
    let syntaxFormula0086 : Wff :=
      (syn_wa (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))))
    let syntaxFormula0094 : Wff :=
      (syn_wa (syn_wf1 (.cv f) (.cv x) (.cv y))
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
    let syntaxFormula0095 : Wff := (.imp syntaxFormula0073 (.classEq (.cv a) (.cv b)))
    let syntaxFormula0096 : Wff := (syn_wral b (.cv x) syntaxFormula0095)
    let syntaxFormula0097 : Wff := (syn_wral a (.cv x) syntaxFormula0096)
    let syntaxFormula0098 : Wff :=
      (syn_wral d (.cv y)
        (syn_wo (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c))))
    let syntaxFormula0099 : Wff := (syn_wral c (.cv y) syntaxFormula0098)
    let syntaxFormula0100 : Wff :=
      (syn_wo (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))))
    let syntaxFormula0101 : Wff := (.imp syntaxFormula0099 syntaxFormula0100)
    let syntaxFormula0102 : Wff :=
      (syn_wa (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))))
    let syntaxFormula0103 : Wff :=
      (syn_wa (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))))
    let syntaxFormula0104 : Wff :=
      (syn_wo (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
    let syntaxFormula0105 : Wff := (.imp syntaxFormula0100 syntaxFormula0104)
    let syntaxFormula0106 : Wff := (syn_wral b (.cv x) syntaxFormula0104)
    let syntaxFormula0107 : Wff := (syn_wral a (.cv x) syntaxFormula0106)
    let syntaxFormula0108 : Wff :=
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.classMem (.cv c) (.cv a)))
    let syntaxFormula0109 : Wff :=
      (syn_wa (.classMem (.cv c) (.cv a))
        (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))))
    let syntaxFormula0110 : Wff := (.imp (.classMem (.cv c) (.cv a)) syntaxFormula0109)
    let syntaxFormula0111 : Wff := (syn_wex c syntaxFormula0109)
    let syntaxFormula0112 : Wff :=
      (syn_wrex c (.cv a) (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))))
    let syntaxFormula0113 : Wff :=
      (syn_wa (.classMem (.cv u) (.cv y)) (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))
    let syntaxClass0114 : Class := (.cab u syntaxFormula0113)
    let syntaxFormula0115 : Wff := (syn_wne syntaxClass0114 (syn_c0))
    let syntaxFormula0116 : Wff := (syn_wss syntaxClass0114 (.cv y))
    let syntaxFormula0117 : Wff :=
      (.classMem (syn_cin (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) (.cv y))
        (syn_cvv))
    let syntaxFormula0118 : Wff := (.classMem syntaxClass0114 (syn_cvv))
    have p0582 :=
      @g_pm2_43d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074 syntaxFormula0094 p0581
    have p0583 := @g_f1fveq (.cv x) (.cv y) (.cv a) (.cv b) (.cv f)
    have p0584 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074 syntaxFormula0094
        (syn_wb (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)))
          (.classEq (.cv a) (.cv b)))
        p0582 p0583
    have p0585 :=
      @g_bi1 (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)))
        (.classEq (.cv a) (.cv b))
    have p0586 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074
        (syn_wb (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)))
          (.classEq (.cv a) (.cv b)))
        (.imp (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)))
          (.classEq (.cv a) (.cv b)))
        p0584 p0585
    have p0587 :=
      @g_mpdd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0074 (.classEq (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)))
        (.classEq (.cv a) (.cv b)) p0574 p0586
    have p0588 :=
      @g_n_3expd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0073 (.classEq (.cv a) (.cv b)) p0587
    have p0589 :=
      @g_imp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0095 p0588
    have p0590 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0095 p0589
    have p0591 :=
      @g_ralrimdvv
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0095 a b (.cv x) (.cv x) dv_cache_0028 dv_cache_0019
        dv_cache_0073 dv_cache_0020 dv_cache_0074 dv_cache_0075 p0590
    have p0592 := @g_pwpullex (.cv r) (.cv f) p0046 p0113
    have p0593 :=
      @g_a1i (.classMem (syn_cpwpull (.cv f) (.cv r)) (syn_cvv)) syn_wtru p0592
    have p0594 := @g_a1i (.classMem (.cv x) (syn_cvv)) syn_wtru p0116
    have p0595 := @g_breq (.cv a) (.cv b) (.cv c) (syn_cpwpull (.cv f) (.cv r))
    have p0596 := @g_breq (.cv b) (.cv a) (.cv c) (syn_cpwpull (.cv f) (.cv r))
    have p0597 :=
      @g_anbi12d (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wbr (.cv a) (.cv c) (.cv b))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (.cv c) (.cv a))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p0595 p0596
    have p0598 :=
      @g_imbi1d (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wa (syn_wbr (.cv a) (.cv c) (.cv b)) (syn_wbr (.cv b) (.cv c) (.cv a)))
        syntaxFormula0073 (.objEq a b) p0597
    have p0599 :=
      @g_n_2ralbidv (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))
        (.imp (syn_wa (syn_wbr (.cv a) (.cv c) (.cv b)) (syn_wbr (.cv b) (.cv c) (.cv a)))
          (.objEq a b))
        (.imp syntaxFormula0073 (.objEq a b)) a b (.cv d) (.cv d) dv_cache_0077
        dv_cache_0078 p0598
    have p0600 :=
      @g_raleq (.imp syntaxFormula0073 (.objEq a b)) b (.cv d) (.cv x) dv_cache_0002
        dv_cache_0028
    have p0601 :=
      @g_raleqbi1dv (syn_wral b (.cv d) (.imp syntaxFormula0073 (.objEq a b)))
        (syn_wral b (.cv x) (.imp syntaxFormula0073 (.objEq a b))) a (.cv d) (.cv x)
        dv_cache_0081 dv_cache_0023 p0600
    have p0602 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_antisym a b c d
        dv_cache_0004 dv_cache_0082 dv_cache_0005 dv_cache_0024 dv_cache_0006
        dv_cache_0075
    have p0603 :=
      @g_brabg
        (syn_wral a (.cv d) (syn_wral b (.cv d) (.imp
              (syn_wa (syn_wbr (.cv a) (.cv c) (.cv b)) (syn_wbr (.cv b) (.cv c) (.cv a)))
              (.objEq a b))))
        (syn_wral a (.cv d) (syn_wral b (.cv d) (.imp syntaxFormula0073 (.objEq a b))))
        (syn_wral a (.cv x) (syn_wral b (.cv x) (.imp syntaxFormula0073 (.objEq a b)))) c
        d (syn_cpwpull (.cv f) (.cv r)) (.cv x) (syn_cvv) (syn_cvv) (syn_cantisym)
        dv_cache_0027 dv_cache_0087 dv_cache_0029 dv_cache_0088 dv_cache_0104
        dv_cache_0105 dv_cache_0013 p0599 p0601 p0602
    have p0604 :=
      @g_syl2anc syn_wtru (.classMem (syn_cpwpull (.cv f) (.cv r)) (syn_cvv))
        (.classMem (.cv x) (syn_cvv))
        (syn_wb (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x))
          (syn_wral a (.cv x) (syn_wral b (.cv x) (.imp syntaxFormula0073 (.objEq a b)))))
        p0593 p0594 p0603
    have p0605 :=
      @g_biimprd syn_wtru (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x))
        (syn_wral a (.cv x) (syn_wral b (.cv x) (.imp syntaxFormula0073 (.objEq a b))))
        p0604
    have p0606_e01_recanon :
      Nominal.NPrf
        (.imp syn_wtru (.imp syntaxFormula0097
            (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x)))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_wtru, syn_wral, syn_wbr, syn_cop, syn_cun, syn_cnin, syn_wnan,
            syn_wa, syn_ccompl, syn_wrex, syn_wex, syn_cphi, syn_cpwpull, syn_ccom,
            syn_copab, syn_cantisym]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.all
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · apply Nominal.RecanonTransportDev.TRecanonWff.all
                apply Nominal.RecanonTransportDev.TRecanonWff.imp
                · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                · apply Nominal.RecanonTransportDev.TRecanonWff.imp
                  · exact Nominal.RecanonTransportDev.TRecanonWff.same _
                  · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
        p0605
    have p0606 :=
      @g_sylcom
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0097
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x)) p0591
        p0606_e01_recanon
    have p0607 :=
      @g_mpi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x)) p0000
        p0606
    have p0608 :=
      @g_n_3jca
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cref) (.cv x))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_ctrans) (.cv x))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x)) p0126 p0452 p0607
    have p0609 := @g_porta (.cv x) (syn_cpwpull (.cv f) (.cv r))
    have p0610 :=
      @g_sylibr
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_w3a (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cref) (.cv x))
          (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_ctrans) (.cv x))
          (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cpartial) (.cv x)) p0608 p0609
    have p0612 := @g_wppweconnex (.cv y) (.cv r)
    have p0613 :=
      @g_syl
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cconnex) (.cv y)) p0004
        p0612
    have p0614 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv r) (syn_cconnex) (.cv y))
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) p0613
    have p0615 := @g_brex (.cv r) (.cv y) (syn_cconnex)
    have p0618 :=
      @g_orbi12d (.classEq (.cv e) (.cv r)) (syn_wbr (.cv c) (.cv e) (.cv d))
        (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv e) (.cv c))
        (syn_wbr (.cv d) (.cv r) (.cv c)) p0537 p0538
    have p0619 :=
      @g_n_2ralbidv (.classEq (.cv e) (.cv r))
        (syn_wo (syn_wbr (.cv c) (.cv e) (.cv d)) (syn_wbr (.cv d) (.cv e) (.cv c)))
        (syn_wo (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c))) c d
        (.cv g) (.cv g) dv_cache_0092 dv_cache_0093 p0618
    have p0620 :=
      @g_raleq
        (syn_wo (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c))) d
        (.cv g) (.cv y) dv_cache_0094 dv_cache_0010
    have p0621 :=
      @g_raleqbi1dv
        (syn_wral d (.cv g)
          (syn_wo (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c))))
        syntaxFormula0098 c (.cv g) (.cv y) dv_cache_0095 dv_cache_0009 p0620
    have p0622 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_connex c d e g
        dv_cache_0052 dv_cache_0050 dv_cache_0051 dv_cache_0096 dv_cache_0097
        dv_cache_0013
    have p0623 :=
      @g_brabg
        (syn_wral c (.cv g) (syn_wral d (.cv g)
            (syn_wo (syn_wbr (.cv c) (.cv e) (.cv d)) (syn_wbr (.cv d) (.cv e) (.cv c)))))
        (syn_wral c (.cv g) (syn_wral d (.cv g)
            (syn_wo (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))))
        syntaxFormula0099 e g (.cv r) (.cv y) (syn_cvv) (syn_cvv) (syn_cconnex)
        dv_cache_0098 dv_cache_0055 dv_cache_0043 dv_cache_0057 dv_cache_0106
        dv_cache_0107 dv_cache_0101 p0619 p0621 p0622
    have p0624 :=
      @g_syl (syn_wbr (.cv r) (syn_cconnex) (.cv y))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
        (syn_wb (syn_wbr (.cv r) (syn_cconnex) (.cv y)) syntaxFormula0099) p0615 p0623
    have p0625 := @g_ibi (syn_wbr (.cv r) (syn_cconnex) (.cv y)) syntaxFormula0099 p0624
    have p0626 :=
      @g_simp2 syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
    have p0627 :=
      @g_syl5 (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv a) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y)) p0626 p0027
    have p0628 :=
      @g_simp3 syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
    have p0629 :=
      @g_syl5 (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv b) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y)) p0628 p0318
    have p0632 :=
      @g_orbi12d (.classEq (.cv c) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (.cv c) (.cv r) (.cv d))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (syn_wbr (.cv d) (.cv r) (.cv c))
        (syn_wbr (.cv d) (.cv r) (syn_cfv (.cv f) (.cv a))) p0331 p0556
    have p0635 :=
      @g_orbi12d (.classEq (.cv d) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (.cv d) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))) p0335 p0561
    have p0636 :=
      @g_rspc2v
        (syn_wo (syn_wbr (.cv c) (.cv r) (.cv d)) (syn_wbr (.cv d) (.cv r) (.cv c)))
        syntaxFormula0100
        (syn_wo (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (.cv d))
          (syn_wbr (.cv d) (.cv r) (syn_cfv (.cv f) (.cv a))))
        c d (syn_cfv (.cv f) (.cv a)) (syn_cfv (.cv f) (.cv b)) (.cv y) (.cv y)
        dv_cache_0062 dv_cache_0063 dv_cache_0065 dv_cache_0009 dv_cache_0009
        dv_cache_0010 dv_cache_0108 dv_cache_0109 dv_cache_0013 p0632 p0635
    have p0637 :=
      @g_ex (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y))
        (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0101 p0636
    have p0638 :=
      @g_syl6c
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (syn_cfv (.cv f) (.cv a)) (.cv y))
        (.classMem (syn_cfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0101 p0627 p0629 p0637
    have p0639 :=
      @g_syl7 (syn_wbr (.cv r) (syn_cconnex) (.cv y)) syntaxFormula0099
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0100 p0625 p0638
    have p0640 :=
      @g_mpdd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (.cv r) (syn_cconnex) (.cv y)) syntaxFormula0100 p0614 p0639
    have p0641 :=
      @g_simpl (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
    have p0643 :=
      @g_syl syntaxFormula0102
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv a) (.cv x)) p0641 p0626
    have p0646 :=
      @g_syl syntaxFormula0102
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv b) (.cv x)) p0641 p0628
    have p0647 :=
      @g_jca syntaxFormula0102 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        p0643 p0646
    have p0648 :=
      @g_simpr (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
    have p0649 :=
      @g_jca syntaxFormula0102
        (syn_wa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b))) p0647 p0648
    have p0650 :=
      @g_syl5ibr syntaxFormula0102 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0038 p0649 p0277
    have p0651 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b)) p0650
    have p0652 :=
      @g_simpl (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
    have p0654 :=
      @g_syl syntaxFormula0103
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv b) (.cv x)) p0652 p0628
    have p0657 :=
      @g_syl syntaxFormula0103
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv a) (.cv x)) p0652 p0626
    have p0658 :=
      @g_jca syntaxFormula0103 (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x))
        p0654 p0657
    have p0659 :=
      @g_simpr (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
    have p0660 :=
      @g_jca syntaxFormula0103
        (syn_wa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a))) p0658 p0659
    have p0661 :=
      @g_syl5ibr syntaxFormula0103 (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0086 p0660 p0517
    have p0662 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p0661
    have p0663 :=
      @g_pm3_48 (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
    have p0664 :=
      @g_ex
        (.imp (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
          (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b)))
        (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
          (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
        syntaxFormula0105 p0663
    have p0665 :=
      @g_syl6c
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.imp (syn_wbr (syn_cfv (.cv f) (.cv a)) (.cv r) (syn_cfv (.cv f) (.cv b)))
          (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b)))
        (.imp (syn_wbr (syn_cfv (.cv f) (.cv b)) (.cv r) (syn_cfv (.cv f) (.cv a)))
          (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
        syntaxFormula0105 p0651 p0662 p0664
    have p0666 :=
      @g_mpdd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_w3a syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0100 syntaxFormula0104 p0640 p0665
    have p0667 :=
      @g_n_3expd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)) syntaxFormula0104
        p0666
    have p0668 :=
      @g_imp4a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)) syntaxFormula0104
        p0667
    have p0669 :=
      @g_ralrimdvv
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0104 a b (.cv x) (.cv x) dv_cache_0028 dv_cache_0019
        dv_cache_0073 dv_cache_0020 dv_cache_0074 dv_cache_0075 p0668
    have p0675 :=
      @g_orbi12d (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wbr (.cv a) (.cv c) (.cv b))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv b) (.cv c) (.cv a))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p0437 p0596
    have p0676 :=
      @g_n_2ralbidv (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wo (syn_wbr (.cv a) (.cv c) (.cv b)) (syn_wbr (.cv b) (.cv c) (.cv a)))
        syntaxFormula0104 a b (.cv d) (.cv d) dv_cache_0077 dv_cache_0078 p0675
    have p0677 := @g_raleq syntaxFormula0104 b (.cv d) (.cv x) dv_cache_0002 dv_cache_0028
    have p0678 :=
      @g_raleqbi1dv (syn_wral b (.cv d) syntaxFormula0104) syntaxFormula0106 a (.cv d)
        (.cv x) dv_cache_0081 dv_cache_0023 p0677
    have p0679 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_connex a b c d
        dv_cache_0004 dv_cache_0082 dv_cache_0005 dv_cache_0024 dv_cache_0006
        dv_cache_0075
    have p0680 :=
      @g_brabg
        (syn_wral a (.cv d) (syn_wral b (.cv d)
            (syn_wo (syn_wbr (.cv a) (.cv c) (.cv b)) (syn_wbr (.cv b) (.cv c) (.cv a)))))
        (syn_wral a (.cv d) (syn_wral b (.cv d) syntaxFormula0104)) syntaxFormula0107 c d
        (syn_cpwpull (.cv f) (.cv r)) (.cv x) (syn_cvv) (syn_cvv) (syn_cconnex)
        dv_cache_0027 dv_cache_0087 dv_cache_0029 dv_cache_0088 dv_cache_0110
        dv_cache_0111 dv_cache_0013 p0676 p0678 p0679
    have p0681 :=
      @g_syl2anc syn_wtru (.classMem (syn_cpwpull (.cv f) (.cv r)) (syn_cvv))
        (.classMem (.cv x) (syn_cvv))
        (syn_wb (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cconnex) (.cv x)) syntaxFormula0107)
        p0115 p0117 p0680
    have p0682 :=
      @g_biimprd syn_wtru (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cconnex) (.cv x))
        syntaxFormula0107 p0681
    have p0683 :=
      @g_sylcom
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0107
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cconnex) (.cv x)) p0669 p0682
    have p0684 :=
      @g_mpi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cconnex) (.cv x)) p0000 p0683
    have p0685 :=
      @g_jca
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cpartial) (.cv x))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cconnex) (.cv x)) p0610 p0684
    have p0686 := @g_sopc (.cv x) (syn_cpwpull (.cv f) (.cv r))
    have p0687 :=
      @g_sylibr
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cpartial) (.cv x))
          (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cconnex) (.cv x)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cstrict) (.cv x)) p0685 p0686
    have p0689 :=
      @g_simpr syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))
    have p0690 :=
      @g_simprd
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)) p0689
    have p0692 :=
      @g_simpld
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)) p0689
    have p0693 :=
      @g_a1d
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)) p0692
    have p0694 := @g_ancom (syn_wne (.cv u) (syn_c0)) (syn_wss (.cv u) (.cv x))
    have p0695 := @g_vex u
    have p0696 :=
      @g_a1i (.classMem (.cv u) (syn_cvv))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        p0695
    have p0698 :=
      @g_id
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
    have p0699 :=
      @g_simpr syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
    have p0700 := @g_simpr (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))
    have p0701 :=
      @g_syl
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
        (syn_wne (.cv a) (syn_c0)) p0699 p0700
    have p0702 :=
      @g_jca
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wne (.cv a) (syn_c0)) p0698 p0701
    have p0703 := @g_n0 c (.cv a) dv_cache_0112
    have p0704 :=
      @g_biimpi (syn_wne (.cv a) (syn_c0)) (syn_wex c (.classMem (.cv c) (.cv a))) p0703
    have p0705 :=
      Nominal.ax17
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))) c
        dv_cache_0113
    have p0706 :=
      @g_simpl
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.classMem (.cv c) (.cv a))
    have p0708 := @g_simpl (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))
    have p0709 :=
      @g_syl
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
        (syn_wss (.cv a) (.cv x)) p0699 p0708
    have p0710 :=
      @g_syl syntaxFormula0108
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wss (.cv a) (.cv x)) p0706 p0709
    have p0711 :=
      @g_simpr
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.classMem (.cv c) (.cv a))
    have p0712 :=
      @g_jca syntaxFormula0108 (syn_wss (.cv a) (.cv x)) (.classMem (.cv c) (.cv a)) p0710
        p0711
    have p0713 := @g_ssel2 (.cv a) (.cv x) (.cv c)
    have p0714 :=
      @g_syl syntaxFormula0108
        (syn_wa (syn_wss (.cv a) (.cv x)) (.classMem (.cv c) (.cv a)))
        (.classMem (.cv c) (.cv x)) p0712 p0713
    have p0715 := @g_id (.classMem (.cv c) (.cv x))
    have p0716 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf (.cv f) (.cv x) (.cv y)) (.classMem (.cv c) (.cv x)) p0022
    have p0717 := @g_ffvelrn (.cv x) (.cv y) (.cv c) (.cv f)
    have p0718 :=
      @g_ex (syn_wf (.cv f) (.cv x) (.cv y)) (.classMem (.cv c) (.cv x))
        (.classMem (syn_cfv (.cv f) (.cv c)) (.cv y)) p0717
    have p0719 :=
      @g_syl56 (.classMem (.cv c) (.cv x)) (.classMem (.cv c) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wf (.cv f) (.cv x) (.cv y))
        (.imp (.classMem (.cv c) (.cv x)) (.classMem (syn_cfv (.cv f) (.cv c)) (.cv y)))
        p0715 p0716 p0718
    have p0720 :=
      @g_pm2_43d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv c) (.cv x)) (.classMem (syn_cfv (.cv f) (.cv c)) (.cv y)) p0719
    have p0721 :=
      @g_syl5 syntaxFormula0108 (.classMem (.cv c) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (syn_cfv (.cv f) (.cv c)) (.cv y)) p0714 p0720
    have p0723 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wfun (.cv f)) syntaxFormula0108 p0042
    have p0733 :=
      @g_eleq2d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_cdm (.cv f)) (.cv x) (.cv c) p0101
    have p0734 :=
      @g_biimprd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv c) (syn_cdm (.cv f))) (.classMem (.cv c) (.cv x)) p0733
    have p0735 :=
      @g_syl5 syntaxFormula0108 (.classMem (.cv c) (.cv x))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.classMem (.cv c) (syn_cdm (.cv f))) p0714 p0734
    have p0736 :=
      @g_jcad
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0108 (syn_wfun (.cv f)) (.classMem (.cv c) (syn_cdm (.cv f))) p0723
        p0735
    have p0737 := @g_funfvima (.cv a) (.cv c) (.cv f)
    have p0738 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0108
        (syn_wa (syn_wfun (.cv f)) (.classMem (.cv c) (syn_cdm (.cv f))))
        (.imp (.classMem (.cv c) (.cv a))
          (.classMem (syn_cfv (.cv f) (.cv c)) (syn_cima (.cv f) (.cv a))))
        p0736 p0737
    have p0739 :=
      @g_mpdi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0108 (.classMem (.cv c) (.cv a))
        (.classMem (syn_cfv (.cv f) (.cv c)) (syn_cima (.cv f) (.cv a))) p0711 p0738
    have p0740 :=
      @g_jcad
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0108 (.classMem (syn_cfv (.cv f) (.cv c)) (.cv y))
        (.classMem (syn_cfv (.cv f) (.cv c)) (syn_cima (.cv f) (.cv a))) p0721 p0739
    have p0741 := @g_eleq1 (.cv u) (syn_cfv (.cv f) (.cv c)) (syn_cima (.cv f) (.cv a))
    have p0742 :=
      @g_rspcev (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))
        (.classMem (syn_cfv (.cv f) (.cv c)) (syn_cima (.cv f) (.cv a))) u
        (syn_cfv (.cv f) (.cv c)) (.cv y) dv_cache_0114 dv_cache_0115 dv_cache_0116 p0741
    have p0743 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0108
        (syn_wa (.classMem (syn_cfv (.cv f) (.cv c)) (.cv y))
          (.classMem (syn_cfv (.cv f) (.cv c)) (syn_cima (.cv f) (.cv a))))
        (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) p0740 p0742
    have p0744 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.classMem (.cv c) (.cv a))
        (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) p0743
    have p0745 :=
      @g_idd
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.classMem (.cv c) (.cv a))
    have p0746 :=
      @g_pm3_2 (.classMem (.cv c) (.cv a))
        (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))
    have p0747 :=
      @g_syl6
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.classMem (.cv c) (.cv a)) (.classMem (.cv c) (.cv a))
        (.imp (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))
          syntaxFormula0109)
        p0745 p0746
    have p0748 :=
      @g_a2d
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.classMem (.cv c) (.cv a))
        (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))
        syntaxFormula0109 p0747
    have p0749 :=
      @g_sylcom
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.imp (.classMem (.cv c) (.cv a))
          (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))))
        syntaxFormula0110 p0744 p0748
    have p0750 :=
      @g_alimdv
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        syntaxFormula0110 c dv_cache_0117 p0749
    have p0751 :=
      @g_syl5
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.all c (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.all c syntaxFormula0110) p0705 p0750
    have p0752 := @g_exim (.classMem (.cv c) (.cv a)) syntaxFormula0109 c
    have p0753 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.all c syntaxFormula0110)
        (.imp (syn_wex c (.classMem (.cv c) (.cv a))) syntaxFormula0111) p0751 p0752
    have p0754 :=
      @g_imp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wex c (.classMem (.cv c) (.cv a))) syntaxFormula0111 p0753
    have p0755 :=
      @g_sylan2i (syn_wne (.cv a) (syn_c0))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wex c (.classMem (.cv c) (.cv a))) syntaxFormula0111 p0704 p0754
    have p0756 := (Nominal.biimpRefl syntaxFormula0112)
    have p0757 :=
      @g_syl6ibr
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
          (syn_wne (.cv a) (syn_c0)))
        syntaxFormula0111 syntaxFormula0112 p0755 p0756
    have p0758 :=
      @g_syl5
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
          (syn_wne (.cv a) (syn_c0)))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0112 p0702 p0757
    have p0759 :=
      @g_id (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))
    have p0760 :=
      @g_a1i
        (.imp (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))
          (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))))
        (.classMem (.cv c) (.cv a)) p0759
    have p0761 :=
      @g_rexlimiv (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))
        (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) c (.cv a)
        dv_cache_0118 p0760
    have p0762 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        syntaxFormula0112
        (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) p0758 p0761
    have p0763 :=
      (Nominal.biimpRefl (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))))
    have p0764 :=
      @g_syl6ib
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wrex u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))
        (syn_wex u syntaxFormula0113) p0762 p0763
    have p0765 := @g_abn0 syntaxFormula0113 u
    have p0766 :=
      @g_syl6ibr
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wex u syntaxFormula0113) syntaxFormula0115 p0764 p0765
    have p0767 :=
      @g_ssab2 (.classMem (.cv u) (syn_cima (.cv f) (.cv a))) u (.cv y) dv_cache_0115
    have p0768 :=
      @g_a1i syntaxFormula0116
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        p0767
    have p0769 :=
      @g_a1d
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        syntaxFormula0116 syntaxFormula0115 p0768
    have p0770 := @g_ancom syntaxFormula0115 syntaxFormula0116
    have p0771 := @g_abid2 u (syn_cima (.cv f) (.cv a)) dv_cache_0119
    have p0772 := @g_vex a
    have p0773 := @g_imaex (.cv f) (.cv a) p0046 p0772
    have p0774 :=
      @g_eqeltri (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))
        (syn_cima (.cv f) (.cv a)) (syn_cvv) p0771 p0773
    have p0775 :=
      @g_a1i (.classMem (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) (syn_cvv))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        p0774
    have p0776 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (.cv r) (syn_cwe) (.cv y))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        p0004
    have p0777 := (Nominal.classEqRefl (syn_cwe))
    have p0778 :=
      @g_breqi (.cv r) (.cv y) (syn_cwe) (syn_cin (syn_cstrict) (syn_cfound)) p0777
    have p0779 := @g_brin (.cv r) (.cv y) (syn_cstrict) (syn_cfound)
    have p0780 :=
      @g_bitri (syn_wbr (.cv r) (syn_cwe) (.cv y))
        (syn_wbr (.cv r) (syn_cin (syn_cstrict) (syn_cfound)) (.cv y))
        (syn_wa (syn_wbr (.cv r) (syn_cstrict) (.cv y)) (syn_wbr (.cv r) (syn_cfound) (.cv y)))
        p0778 p0779
    have p0781 :=
      @g_simprbi (syn_wbr (.cv r) (syn_cwe) (.cv y))
        (syn_wbr (.cv r) (syn_cstrict) (.cv y)) (syn_wbr (.cv r) (syn_cfound) (.cv y))
        p0780
    have p0782 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wbr (.cv r) (syn_cwe) (.cv y)) (syn_wbr (.cv r) (syn_cfound) (.cv y)) p0776
        p0781
    have p0783 := @g_brex (.cv r) (.cv y) (syn_cfound)
    have p0784 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wbr (.cv r) (syn_cfound) (.cv y))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (.cv y) (syn_cvv))) p0782 p0783
    have p0785 := @g_ancom (.classMem (.cv r) (syn_cvv)) (.classMem (.cv y) (syn_cvv))
    have p0786 :=
      @g_syl6ib
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wa (.classMem (.cv r) (syn_cvv)) (.classMem (.cv y) (syn_cvv)))
        (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv r) (syn_cvv))) p0784 p0785
    have p0787 := @g_simpl (.classMem (.cv y) (syn_cvv)) (.classMem (.cv r) (syn_cvv))
    have p0788 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv r) (syn_cvv)))
        (.classMem (.cv y) (syn_cvv)) p0786 p0787
    have p0789 :=
      @g_inexg (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) (.cv y) (syn_cvv)
        (syn_cvv)
    have p0790 :=
      @g_ex (.classMem (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) (syn_cvv))
        (.classMem (.cv y) (syn_cvv)) syntaxFormula0117 p0789
    have p0791 :=
      @g_syl9
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.classMem (.cv y) (syn_cvv))
        (.classMem (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) (syn_cvv))
        syntaxFormula0117 p0788 p0790
    have p0792 :=
      @g_syl5
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        (.classMem (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) (syn_cvv))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.imp (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
          syntaxFormula0117)
        p0775 p0791
    have p0793 :=
      @g_pm2_43d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        syntaxFormula0117 p0792
    have p0794 :=
      @g_dfrab2 (.classMem (.cv u) (syn_cima (.cv f) (.cv a))) u (.cv y) dv_cache_0115
    have p0795 :=
      (Nominal.classEqRefl (syn_crab u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))))
    have p0796 :=
      @g_eqtr3i (syn_crab u (.cv y) (.classMem (.cv u) (syn_cima (.cv f) (.cv a))))
        (syn_cin (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) (.cv y))
        syntaxClass0114 p0794 p0795
    have p0797 :=
      @g_eqcomi (syn_cin (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) (.cv y))
        syntaxClass0114 p0796
    have p0798 :=
      @g_a1i
        (.classEq syntaxClass0114
          (syn_cin (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        p0797
    have p0799 :=
      @g_eleq1d
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        syntaxClass0114
        (syn_cin (.cab u (.classMem (.cv u) (syn_cima (.cv f) (.cv a)))) (.cv y))
        (syn_cvv) p0798
    have p0800 :=
      @g_biimprd
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        syntaxFormula0118 syntaxFormula0117 p0799
    have p0801 :=
      @g_sylcom
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))))
        syntaxFormula0117 syntaxFormula0118 p0793 p0800
    have p0802 := @g_brex (.cv r) (.cv y) (syn_cfound)
    have p0803 := @g_breq (.cv w) (.cv v) (.cv d) (.cv r)
    have p0804 :=
      @g_imbi1d (.classEq (.cv d) (.cv r)) (syn_wbr (.cv w) (.cv d) (.cv v))
        (syn_wbr (.cv w) (.cv r) (.cv v)) (.objEq w v) p0803
    have p0805 :=
      @g_rexralbidv (.classEq (.cv d) (.cv r))
        (.imp (syn_wbr (.cv w) (.cv d) (.cv v)) (.objEq w v))
        (.imp (syn_wbr (.cv w) (.cv r) (.cv v)) (.objEq w v)) v w (.cv b) (.cv b)
        dv_cache_0120 dv_cache_0121 p0804
    have p0806 :=
      @g_imbi2d (.classEq (.cv d) (.cv r))
        (syn_wrex v (.cv b)
          (syn_wral w (.cv b) (.imp (syn_wbr (.cv w) (.cv d) (.cv v)) (.objEq w v))))
        (syn_wrex v (.cv b)
          (syn_wral w (.cv b) (.imp (syn_wbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))
        (syn_wa (syn_wss (.cv b) (.cv c)) (syn_wne (.cv b) (syn_c0))) p0805
    have p0807 :=
      @g_albidv (.classEq (.cv d) (.cv r))
        (.imp (syn_wa (syn_wss (.cv b) (.cv c)) (syn_wne (.cv b) (syn_c0))) (syn_wrex v (.cv b)
            (syn_wral w (.cv b) (.imp (syn_wbr (.cv w) (.cv d) (.cv v)) (.objEq w v)))))
        (.imp (syn_wa (syn_wss (.cv b) (.cv c)) (syn_wne (.cv b) (syn_c0))) (syn_wrex v (.cv b)
            (syn_wral w (.cv b) (.imp (syn_wbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))))
        b dv_cache_0122 p0806
    have p0808 := @g_sseq2 (.cv c) (.cv y) (.cv b)
    have p0809 :=
      @g_anbi1d (.classEq (.cv c) (.cv y)) (syn_wss (.cv b) (.cv c))
        (syn_wss (.cv b) (.cv y)) (syn_wne (.cv b) (syn_c0)) p0808
    have p0810 :=
      @g_imbi1d (.classEq (.cv c) (.cv y))
        (syn_wa (syn_wss (.cv b) (.cv c)) (syn_wne (.cv b) (syn_c0)))
        (syn_wa (syn_wss (.cv b) (.cv y)) (syn_wne (.cv b) (syn_c0)))
        (syn_wrex v (.cv b)
          (syn_wral w (.cv b) (.imp (syn_wbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))
        p0809
    have p0811 :=
      @g_albidv (.classEq (.cv c) (.cv y))
        (.imp (syn_wa (syn_wss (.cv b) (.cv c)) (syn_wne (.cv b) (syn_c0))) (syn_wrex v (.cv b)
            (syn_wral w (.cv b) (.imp (syn_wbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))))
        (.imp (syn_wa (syn_wss (.cv b) (.cv y)) (syn_wne (.cv b) (syn_c0))) (syn_wrex v (.cv b)
            (syn_wral w (.cv b) (.imp (syn_wbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))))
        b dv_cache_0123 p0810
    have p0812 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_found b w v d c
        dv_cache_0013 dv_cache_0006 dv_cache_0124 dv_cache_0125 dv_cache_0005
        dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130
    exact
      continuation p0607 p0615 p0687 p0690 p0693 p0694 p0696 p0709 p0766 p0769 p0770 p0776
        p0777 p0780 p0782 p0801 p0802 p0807 p0811 p0812

end NFChoice.DirectNominalPrf.WPPReplay

end
