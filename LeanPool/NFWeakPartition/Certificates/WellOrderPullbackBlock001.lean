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

/-- Checked nominal proof certificate identified upstream as `g_pwpullwesetimpndv_stage1`. -/
@[expose]
noncomputable def gPwpullwesetimpndvStage1 (x : Var) (y : Var) (f : Var) (r : Var)
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
      c ∉ ((synWral b (.cv y) (synWbr (.cv b) (.cv r) (.cv b)))).fv := by
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
      d ∉ ((synWral b (.cv y) (synWbr (.cv b) (.cv r) (.cv b)))).fv := by
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
    have dv_cache_0014 : b ∉ ((synCfv (.cv f) (.cv a))).fv := by
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
      b ∉ ((synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a)))).fv := by
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
    have dv_cache_0018 :
      g ∉
        ((Wff.imp (synWfun (synCcnv (synCcnv (.cv f)))) (synWb (synWbr (.cv a)
                (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
                (.cv a)) (synWa (synWa (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
                  (.classMem (.cv a) (synCrn (synCcnv (.cv f)))))
                (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (.cv r)
                  (synCfv (synCcnv (synCcnv (.cv f))) (.cv a))))))).fv :=
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
    have dv_cache_0021 : a ∉ ((Wff.classEq (.cv b) (synCpwpull (.cv f) (.cv r)))).fv :=
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
    have dv_cache_0026 : b ∉ ((synCpwpull (.cv f) (.cv r))).fv := by
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
    have dv_cache_0027 : c ∉ ((synCpwpull (.cv f) (.cv r))).fv := by
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
        ((synWral a (.cv x) (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)))).fv :=
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
        ((synWral a (.cv x) (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)))).fv :=
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
      z ∉ ((synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))).fv := by
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
    have dv_cache_0034 : z ∉ (synWtru).fv := by
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
        ((Wff.imp (synWfun (synCcnv (synCcnv (.cv f)))) (synWb (synWbr (.cv b)
                (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
                (.cv z)) (synWa (synWa (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
                  (.classMem (.cv z) (synCrn (synCcnv (.cv f)))))
                (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (.cv r)
                  (synCfv (synCcnv (synCcnv (.cv f))) (.cv z))))))).fv :=
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
        ((Wff.imp (synWfun (synCcnv (synCcnv (.cv f)))) (synWb (synWbr (.cv a)
                (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
                (.cv b)) (synWa (synWa (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
                  (.classMem (.cv b) (synCrn (synCcnv (.cv f)))))
                (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (.cv r)
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
            Finset.mem_singleton, fresh_g_ne_f, fresh_g_ne_a, fresh_g_ne_b, fresh_g_ne_r,
            or_false, not_false_eq_true])
    let syntaxFormula0000 : Wff :=
      (synWa (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a))))
    let syntaxFormula0001 : Wff :=
      (synWa (.classMem (.cv a) (synCrn (.cv g))) (.classMem (.cv a) (synCrn (.cv g))))
    let syntaxFormula0002 : Wff :=
      (synWa (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv a) (synCrn (synCcnv (.cv f)))))
    let syntaxFormula0003 : Wff :=
      (synWbr (synCfv (synCcnv (.cv g)) (.cv a)) (.cv r)
        (synCfv (synCcnv (.cv g)) (.cv a)))
    let syntaxFormula0004 : Wff :=
      (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (.cv r)
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)))
    let syntaxFormula0005 : Wff :=
      (synWbr (.cv a)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f)))) (.cv a))
    let syntaxFormula0006 : Wff := (synWa syntaxFormula0001 syntaxFormula0003)
    let syntaxFormula0007 : Wff := (synWa syntaxFormula0002 syntaxFormula0004)
    let syntaxFormula0008 : Wff :=
      (synWb (synWbr (.cv a) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv a))
        syntaxFormula0006)
    let syntaxFormula0009 : Wff := (synWb syntaxFormula0005 syntaxFormula0007)
    let syntaxFormula0010 : Wff :=
      (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv a) (synCdm (.cv f))))
    let syntaxFormula0011 : Wff :=
      (synWa syntaxFormula0010
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a))))
    let syntaxFormula0012 : Wff :=
      (synW3a (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (.cv x)))
    let syntaxFormula0013 : Wff :=
      (synWa (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z)))
    let syntaxFormula0014 : Wff := (synW3a synWtru syntaxFormula0012 syntaxFormula0013)
    let syntaxFormula0015 : Wff :=
      (synWa (.classMem (.cv b) (synCrn (.cv g))) (.classMem (.cv z) (synCrn (.cv g))))
    let syntaxFormula0016 : Wff :=
      (synWa (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv z) (synCrn (synCcnv (.cv f)))))
    let syntaxFormula0017 : Wff :=
      (synWbr (synCfv (synCcnv (.cv g)) (.cv b)) (.cv r)
        (synCfv (synCcnv (.cv g)) (.cv z)))
    let syntaxFormula0018 : Wff :=
      (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (.cv r)
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv z)))
    let syntaxFormula0019 : Wff :=
      (synWbr (.cv b)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f)))) (.cv z))
    let syntaxFormula0020 : Wff := (synWa syntaxFormula0015 syntaxFormula0017)
    let syntaxFormula0021 : Wff := (synWa syntaxFormula0016 syntaxFormula0018)
    let syntaxFormula0022 : Wff :=
      (synWb (synWbr (.cv b) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv z))
        syntaxFormula0020)
    let syntaxFormula0023 : Wff := (synWb syntaxFormula0019 syntaxFormula0021)
    let syntaxFormula0024 : Wff :=
      (synWa (.classMem (.cv b) (synCdm (.cv f))) (.classMem (.cv z) (synCdm (.cv f))))
    let syntaxFormula0025 : Wff :=
      (synWa syntaxFormula0024
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z))))
    let syntaxFormula0026 : Wff :=
      (synWa (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv z) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z))))
    let syntaxFormula0027 : Wff :=
      (synWa (.classMem (.cv a) (synCrn (.cv g))) (.classMem (.cv b) (synCrn (.cv g))))
    let syntaxFormula0028 : Wff :=
      (synWa (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv b) (synCrn (synCcnv (.cv f)))))
    let syntaxFormula0029 : Wff :=
      (synWbr (synCfv (synCcnv (.cv g)) (.cv a)) (.cv r)
        (synCfv (synCcnv (.cv g)) (.cv b)))
    let syntaxFormula0030 : Wff :=
      (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (.cv r)
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)))
    let syntaxFormula0031 : Wff :=
      (synWbr (.cv a)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f)))) (.cv b))
    let syntaxFormula0032 : Wff := (synWa syntaxFormula0027 syntaxFormula0029)
    let syntaxFormula0033 : Wff := (synWa syntaxFormula0028 syntaxFormula0030)
    let syntaxFormula0034 : Wff :=
      (synWb (synWbr (.cv a) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv b))
        syntaxFormula0032)
    let syntaxFormula0035 : Wff := (synWb syntaxFormula0031 syntaxFormula0033)
    let syntaxFormula0036 : Wff :=
      (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv b) (synCdm (.cv f))))
    let syntaxFormula0037 : Wff :=
      (synWa syntaxFormula0036
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
    let syntaxFormula0038 : Wff :=
      (synWa (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
    have p0000 := @gTru
    have p0001 := @gId (.classMem (.cv a) (.cv x))
    have p0003 :=
      @gJca (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x))
        (.classMem (.cv a) (.cv x)) p0001 p0001
    have p0004 :=
      @gSimpr (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y))
    have p0005 := @gWppweref (.cv y) (.cv r)
    have p0006 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCref) (.cv y)) p0004
        p0005
    have p0007 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv r) (synCref) (.cv y)) (.classMem (.cv a) (.cv x)) p0006
    have p0008 := @gBrex (.cv r) (.cv y) (synCref)
    have p0009 := @gBreq (.cv b) (.cv b) (.cv c) (.cv r)
    have p0010 :=
      @gRalbidv (.classEq (.cv c) (.cv r)) (synWbr (.cv b) (.cv c) (.cv b))
        (synWbr (.cv b) (.cv r) (.cv b)) b (.cv d) dv_cache_0001 p0009
    have p0011 :=
      @gRaleq (synWbr (.cv b) (.cv r) (.cv b)) b (.cv d) (.cv y) dv_cache_0002
        dv_cache_0003
    have p0012 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfRef b c d
        dv_cache_0004 dv_cache_0005 dv_cache_0006
    have p0013 :=
      @gBrabg (synWral b (.cv d) (synWbr (.cv b) (.cv c) (.cv b)))
        (synWral b (.cv d) (synWbr (.cv b) (.cv r) (.cv b)))
        (synWral b (.cv y) (synWbr (.cv b) (.cv r) (.cv b))) c d (.cv r) (.cv y)
        (synCvv) (synCvv) (synCref) dv_cache_0007 dv_cache_0008 dv_cache_0009
        dv_cache_0010 dv_cache_0011 dv_cache_0012 dv_cache_0013 p0010 p0011 p0012
    have p0014 :=
      @gSyl (synWbr (.cv r) (synCref) (.cv y))
        (synWa (.classMem (.cv r) (synCvv)) (.classMem (.cv y) (synCvv)))
        (synWb (synWbr (.cv r) (synCref) (.cv y))
          (synWral b (.cv y) (synWbr (.cv b) (.cv r) (.cv b))))
        p0008 p0013
    have p0015 :=
      @gIbi (synWbr (.cv r) (synCref) (.cv y))
        (synWral b (.cv y) (synWbr (.cv b) (.cv r) (.cv b))) p0014
    have p0016 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv a) (.cv x)) (synWbr (.cv r) (synCref) (.cv y))
        (synWral b (.cv y) (synWbr (.cv b) (.cv r) (.cv b))) p0007 p0015
    have p0018 :=
      @gSimpl (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y))
    have p0019 := @gF1ofo (.cv x) (.cv y) (.cv f)
    have p0020 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf1o (.cv f) (.cv x) (.cv y)) (synWfo (.cv f) (.cv x) (.cv y)) p0018 p0019
    have p0021 := @gFof (.cv x) (.cv y) (.cv f)
    have p0022 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfo (.cv f) (.cv x) (.cv y)) (synWf (.cv f) (.cv x) (.cv y)) p0020 p0021
    have p0023 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf (.cv f) (.cv x) (.cv y)) (.classMem (.cv a) (.cv x)) p0022
    have p0024 := @gFfvelrn (.cv x) (.cv y) (.cv a) (.cv f)
    have p0025 :=
      @gEx (synWf (.cv f) (.cv x) (.cv y)) (.classMem (.cv a) (.cv x))
        (.classMem (synCfv (.cv f) (.cv a)) (.cv y)) p0024
    have p0026 :=
      @gSyl56 (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf (.cv f) (.cv x) (.cv y))
        (.imp (.classMem (.cv a) (.cv x)) (.classMem (synCfv (.cv f) (.cv a)) (.cv y)))
        p0001 p0023 p0025
    have p0027 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv a) (.cv x)) (.classMem (synCfv (.cv f) (.cv a)) (.cv y)) p0026
    have p0028 := @gId (.classEq (.cv b) (synCfv (.cv f) (.cv a)))
    have p0029 :=
      @gBreq12d (.classEq (.cv b) (synCfv (.cv f) (.cv a))) (.cv b)
        (synCfv (.cv f) (.cv a)) (.cv b) (synCfv (.cv f) (.cv a)) (.cv r) p0028 p0028
    have p0030 :=
      @gRspccv (synWbr (.cv b) (.cv r) (.cv b))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a))) b
        (synCfv (.cv f) (.cv a)) (.cv y) dv_cache_0014 dv_cache_0003 dv_cache_0015 p0029
    have p0031 :=
      @gSyl6c
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv a) (.cv x)) (synWral b (.cv y) (synWbr (.cv b) (.cv r) (.cv b)))
        (.classMem (synCfv (.cv f) (.cv a)) (.cv y))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a))) p0016 p0027
        p0030
    have p0032 :=
      @g_pm3_2 (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a)))
    have p0033 :=
      @gSyl9
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv a) (.cv x))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x))) syntaxFormula0000
        p0031 p0032
    have p0034 :=
      @gSyl5 (.classMem (.cv a) (.cv x))
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x)))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.imp (.classMem (.cv a) (.cv x)) syntaxFormula0000) p0003 p0033
    have p0035 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv a) (.cv x)) syntaxFormula0000 p0034
    have p0036 := (Nominal.classEqRefl (synCpwpull (.cv f) (.cv r)))
    have p0037 :=
      @gBreqi (.cv a) (.cv a) (synCpwpull (.cv f) (.cv r))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p0038 := @gCnvcnv (.cv f)
    have p0039 :=
      @gCoeq2i (synCcnv (synCcnv (.cv f))) (.cv f)
        (synCcom (synCcnv (.cv f)) (.cv r)) p0038
    have p0040 :=
      @gBreqi (.cv a) (.cv a)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p0041 := @gFofun (.cv x) (.cv y) (.cv f)
    have p0042 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfo (.cv f) (.cv x) (.cv y)) (synWfun (.cv f)) p0020 p0041
    have p0044 := @gFuneqi (synCcnv (synCcnv (.cv f))) (.cv f) p0038
    have p0045 :=
      @gSylibr
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (.cv f)) (synWfun (synCcnv (synCcnv (.cv f)))) p0042 p0044
    have p0046 := @gVex f
    have p0047 := @gCnvex (.cv f) p0046
    have p0048 := @gId (.classEq (.cv g) (synCcnv (.cv f)))
    have p0049 :=
      @gCnveqd (.classEq (.cv g) (synCcnv (.cv f))) (.cv g) (synCcnv (.cv f)) p0048
    have p0050 :=
      @gFuneqd (.classEq (.cv g) (synCcnv (.cv f))) (synCcnv (.cv g))
        (synCcnv (synCcnv (.cv f))) p0049
    have p0052 :=
      @gCoeq1d (.classEq (.cv g) (synCcnv (.cv f))) (.cv g) (synCcnv (.cv f)) (.cv r)
        p0048
    have p0055 :=
      @gCoeq12d (.classEq (.cv g) (synCcnv (.cv f))) (synCcom (.cv g) (.cv r))
        (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (.cv g))
        (synCcnv (synCcnv (.cv f))) p0052 p0049
    have p0056 :=
      @gBreqd (.classEq (.cv g) (synCcnv (.cv f)))
        (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g)))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (.cv a) (.cv a) p0055
    have p0058 :=
      @gRneqd (.classEq (.cv g) (synCcnv (.cv f))) (.cv g) (synCcnv (.cv f)) p0048
    have p0059 :=
      @gEleq2d (.classEq (.cv g) (synCcnv (.cv f))) (synCrn (.cv g))
        (synCrn (synCcnv (.cv f))) (.cv a) p0058
    have p0063 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (.classMem (.cv a) (synCrn (.cv g)))
        (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv a) (synCrn (.cv g)))
        (.classMem (.cv a) (synCrn (synCcnv (.cv f)))) p0059 p0059
    have p0066 :=
      @gFveq1d (.classEq (.cv g) (synCcnv (.cv f))) (.cv a) (synCcnv (.cv g))
        (synCcnv (synCcnv (.cv f))) p0049
    have p0070 :=
      @gBreq12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synCfv (synCcnv (.cv g)) (.cv a))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv a))
        (synCfv (synCcnv (.cv g)) (.cv a))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (.cv r) p0066 p0066
    have p0071 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f))) syntaxFormula0001 syntaxFormula0002
        syntaxFormula0003 syntaxFormula0004 p0063 p0070
    have p0072 :=
      @gBibi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synWbr (.cv a) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv a))
        syntaxFormula0005 syntaxFormula0006 syntaxFormula0007 p0056 p0071
    have p0073 :=
      @gImbi12d (.classEq (.cv g) (synCcnv (.cv f))) (synWfun (synCcnv (.cv g)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0008 syntaxFormula0009 p0050
        p0072
    have p0074 := @gHwtrnbrd a a g r dv_cache_0016 dv_cache_0016
    have p0075 :=
      @gVtoclg (.imp (synWfun (synCcnv (.cv g))) syntaxFormula0008)
        (.imp (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0009) g
        (synCcnv (.cv f)) (synCvv) dv_cache_0017 dv_cache_0018 p0073 p0074
    have p0076 := Nominal.mp p0047 p0075
    have p0077 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0009 p0045 p0076
    have p0078 := @gDfrn4 (synCcnv (.cv f))
    have p0080 := @gDmeqi (synCcnv (synCcnv (.cv f))) (.cv f) p0038
    have p0081 :=
      @gEqtri (synCrn (synCcnv (.cv f))) (synCdm (synCcnv (synCcnv (.cv f))))
        (synCdm (.cv f)) p0078 p0080
    have p0082 := @gEleq2i (synCrn (synCcnv (.cv f))) (synCdm (.cv f)) (.cv a) p0081
    have p0088 :=
      @gAnbi12i (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv a) (synCdm (.cv f)))
        (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv a) (synCdm (.cv f))) p0082 p0082
    have p0090 := @gFveq1i (.cv a) (synCcnv (synCcnv (.cv f))) (.cv f) p0038
    have p0093 :=
      @gBreq12i (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (synCfv (.cv f) (.cv a))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (synCfv (.cv f) (.cv a)) (.cv r)
        p0090 p0090
    have p0094 :=
      @gAnbi12i syntaxFormula0002 syntaxFormula0010 syntaxFormula0004
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a))) p0088 p0093
    have p0095 :=
      @gSyl6bb
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0005 syntaxFormula0007 syntaxFormula0011 p0077 p0094
    have p0096 :=
      @gSyl5bbr
        (synWbr (.cv a) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv a))
        syntaxFormula0005
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0011 p0040 p0095
    have p0097 :=
      @gSyl5bb (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a))
        (synWbr (.cv a) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv a))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0011 p0037 p0096
    have p0098 := @gFofn (.cv x) (.cv y) (.cv f)
    have p0099 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfo (.cv f) (.cv x) (.cv y)) (synWfn (.cv f) (.cv x)) p0020 p0098
    have p0100 := @gFndm (.cv x) (.cv f)
    have p0101 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfn (.cv f) (.cv x)) (.classEq (synCdm (.cv f)) (.cv x)) p0099 p0100
    have p0102 :=
      @gEleq2d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synCdm (.cv f)) (.cv x) (.cv a) p0101
    have p0103 :=
      @gAnbi12d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv a) (.cv x))
        (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv a) (.cv x)) p0102 p0102
    have p0104 :=
      @gAnbi1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0010 (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a))) p0103
    have p0105 :=
      @gBiid (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a)))
    have p0106 :=
      @gAnbi2i (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv a) (.cv x))) p0105
    have p0107 :=
      @gA1ii
        (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
          (synWb syntaxFormula0011 syntaxFormula0000))
        (synWb syntaxFormula0000 syntaxFormula0000) p0104 p0106
    have p0108 :=
      @gBitrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)) syntaxFormula0011
        syntaxFormula0000 p0097 p0107
    have p0109 :=
      @gSylibrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv a) (.cv x)) syntaxFormula0000
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)) p0035 p0108
    have p0110 :=
      @gAdantld
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv a) (.cv x))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)) synWtru p0109
    have p0111 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (.classMem (.cv a) (.cv x))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)) p0110
    have p0112 :=
      @gRalrimdv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)) a (.cv x)
        dv_cache_0019 dv_cache_0020 p0111
    have p0113 := @gVex r
    have p0114 := @gPwpullex (.cv r) (.cv f) p0046 p0113
    have p0115 :=
      @gA1i (.classMem (synCpwpull (.cv f) (.cv r)) (synCvv)) synWtru p0114
    have p0116 := @gVex x
    have p0117 := @gA1i (.classMem (.cv x) (synCvv)) synWtru p0116
    have p0118 := @gBreq (.cv a) (.cv a) (.cv b) (synCpwpull (.cv f) (.cv r))
    have p0119 :=
      @gRalbidv (.classEq (.cv b) (synCpwpull (.cv f) (.cv r)))
        (synWbr (.cv a) (.cv b) (.cv a))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)) a (.cv c) dv_cache_0021
        p0118
    have p0120 :=
      @gRaleq (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)) a (.cv c) (.cv x)
        dv_cache_0022 dv_cache_0023
    have p0121 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfRef a b c
        dv_cache_0006 dv_cache_0024 dv_cache_0025
    have p0122 :=
      @gBrabg (synWral a (.cv c) (synWbr (.cv a) (.cv b) (.cv a)))
        (synWral a (.cv c) (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)))
        (synWral a (.cv x) (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a))) b c
        (synCpwpull (.cv f) (.cv r)) (.cv x) (synCvv) (synCvv) (synCref) dv_cache_0026
        dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0031
        dv_cache_0032 p0119 p0120 p0121
    have p0123 :=
      @gSyl2anc synWtru (.classMem (synCpwpull (.cv f) (.cv r)) (synCvv))
        (.classMem (.cv x) (synCvv))
        (synWb (synWbr (synCpwpull (.cv f) (.cv r)) (synCref) (.cv x))
          (synWral a (.cv x) (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a))))
        p0115 p0117 p0122
    have p0124 :=
      @gBiimprd synWtru (synWbr (synCpwpull (.cv f) (.cv r)) (synCref) (.cv x))
        (synWral a (.cv x) (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a))) p0123
    have p0125 :=
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru
        (synWral a (.cv x) (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv a)))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCref) (.cv x)) p0112 p0124
    have p0126 :=
      @gMpi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWbr (synCpwpull (.cv f) (.cv r)) (synCref) (.cv x)) p0000 p0125
    have p0128 :=
      @gNfv (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) z
        dv_cache_0033
    have p0129 :=
      @gA1i (synWnf z (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
        synWtru p0128
    have p0130 :=
      @gNfrd synWtru (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) z
        p0129
    have p0131 := @gNfv synWtru z dv_cache_0034
    have p0132 := @gNfri synWtru z p0131
    have p0133 := (Nominal.biimpRefl syntaxFormula0012)
    have p0134 :=
      @gBiimpri syntaxFormula0012
        (synWa (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
          (.classMem (.cv z) (.cv x)))
        p0133
    have p0135 := @gSimp2 synWtru syntaxFormula0012 syntaxFormula0013
    have p0136 :=
      @gSimp1 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (.cv x))
    have p0137 :=
      @gSyl syntaxFormula0014 syntaxFormula0012 (.classMem (.cv a) (.cv x)) p0135 p0136
    have p0139 :=
      @gSimp3 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (.cv x))
    have p0140 :=
      @gSyl syntaxFormula0014 syntaxFormula0012 (.classMem (.cv z) (.cv x)) p0135 p0139
    have p0141 :=
      @gJca syntaxFormula0014 (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x))
        p0137 p0140
    have p0142 := @gSimp3 synWtru syntaxFormula0012 syntaxFormula0013
    have p0143 :=
      @gSimpr (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z))
    have p0144 :=
      @gSyl syntaxFormula0014 syntaxFormula0013
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z)) p0142 p0143
    have p0146 :=
      @gBreqi (.cv b) (.cv z) (synCpwpull (.cv f) (.cv r))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p0149 :=
      @gBreqi (.cv b) (.cv z)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p0159 :=
      @gBreqd (.classEq (.cv g) (synCcnv (.cv f)))
        (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g)))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (.cv b) (.cv z) p0055
    have p0162 :=
      @gEleq2d (.classEq (.cv g) (synCcnv (.cv f))) (synCrn (.cv g))
        (synCrn (synCcnv (.cv f))) (.cv b) p0058
    have p0165 :=
      @gEleq2d (.classEq (.cv g) (synCcnv (.cv f))) (synCrn (.cv g))
        (synCrn (synCcnv (.cv f))) (.cv z) p0058
    have p0166 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (.classMem (.cv b) (synCrn (.cv g)))
        (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv z) (synCrn (.cv g)))
        (.classMem (.cv z) (synCrn (synCcnv (.cv f)))) p0162 p0165
    have p0169 :=
      @gFveq1d (.classEq (.cv g) (synCcnv (.cv f))) (.cv b) (synCcnv (.cv g))
        (synCcnv (synCcnv (.cv f))) p0049
    have p0172 :=
      @gFveq1d (.classEq (.cv g) (synCcnv (.cv f))) (.cv z) (synCcnv (.cv g))
        (synCcnv (synCcnv (.cv f))) p0049
    have p0173 :=
      @gBreq12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synCfv (synCcnv (.cv g)) (.cv b))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv b))
        (synCfv (synCcnv (.cv g)) (.cv z))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv z)) (.cv r) p0169 p0172
    have p0174 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f))) syntaxFormula0015 syntaxFormula0016
        syntaxFormula0017 syntaxFormula0018 p0166 p0173
    have p0175 :=
      @gBibi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synWbr (.cv b) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv z))
        syntaxFormula0019 syntaxFormula0020 syntaxFormula0021 p0159 p0174
    have p0176 :=
      @gImbi12d (.classEq (.cv g) (synCcnv (.cv f))) (synWfun (synCcnv (.cv g)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0022 syntaxFormula0023 p0050
        p0175
    have p0177 := @gHwtrnbrd b z g r dv_cache_0035 dv_cache_0036
    have p0178 :=
      @gVtoclg (.imp (synWfun (synCcnv (.cv g))) syntaxFormula0022)
        (.imp (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0023) g
        (synCcnv (.cv f)) (synCvv) dv_cache_0017 dv_cache_0037 p0176 p0177
    have p0179 := Nominal.mp p0047 p0178
    have p0180 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0023 p0045 p0179
    have p0185 := @gEleq2i (synCrn (synCcnv (.cv f))) (synCdm (.cv f)) (.cv b) p0081
    have p0190 := @gEleq2i (synCrn (synCcnv (.cv f))) (synCdm (.cv f)) (.cv z) p0081
    have p0191 :=
      @gAnbi12i (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv b) (synCdm (.cv f)))
        (.classMem (.cv z) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv z) (synCdm (.cv f))) p0185 p0190
    have p0193 := @gFveq1i (.cv b) (synCcnv (synCcnv (.cv f))) (.cv f) p0038
    have p0195 := @gFveq1i (.cv z) (synCcnv (synCcnv (.cv f))) (.cv f) p0038
    have p0196 :=
      @gBreq12i (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (synCfv (.cv f) (.cv b))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv z)) (synCfv (.cv f) (.cv z)) (.cv r)
        p0193 p0195
    have p0197 :=
      @gAnbi12i syntaxFormula0016 syntaxFormula0024 syntaxFormula0018
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z))) p0191 p0196
    have p0198 :=
      @gSyl6bb
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0019 syntaxFormula0021 syntaxFormula0025 p0180 p0197
    have p0199 :=
      @gSyl5bbr
        (synWbr (.cv b) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv z))
        syntaxFormula0019
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0025 p0149 p0198
    have p0200 :=
      @gSyl5bb (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z))
        (synWbr (.cv b) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv z))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0025 p0146 p0199
    have p0201 :=
      @gEleq2d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synCdm (.cv f)) (.cv x) (.cv b) p0101
    have p0202 :=
      @gEleq2d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synCdm (.cv f)) (.cv x) (.cv z) p0101
    have p0203 :=
      @gAnbi12d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv b) (synCdm (.cv f))) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (synCdm (.cv f))) (.classMem (.cv z) (.cv x)) p0201 p0202
    have p0204 :=
      @gAnbi1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0024 (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv z) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z))) p0203
    have p0205 :=
      @gBiid (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
    have p0206 :=
      @gAnbi2i (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
        (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv z) (.cv x))) p0205
    have p0207 :=
      @gA1ii
        (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
          (synWb syntaxFormula0025 syntaxFormula0026))
        (synWb syntaxFormula0026 syntaxFormula0026) p0204 p0206
    have p0208 :=
      @gBitrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z)) syntaxFormula0025
        syntaxFormula0026 p0200 p0207
    have p0209 :=
      @gBiimpd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z)) syntaxFormula0026 p0208
    have p0210 :=
      @gSyl5 syntaxFormula0014 (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0026 p0144 p0209
    have p0211 :=
      @gSimpr (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv z) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
    have p0212 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014 syntaxFormula0026
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z))) p0210 p0211
    have p0214 :=
      @gSimpl (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z))
    have p0215 :=
      @gSyl syntaxFormula0014 syntaxFormula0013
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b)) p0142 p0214
    have p0217 :=
      @gBreqi (.cv a) (.cv b) (synCpwpull (.cv f) (.cv r))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p0220 :=
      @gBreqi (.cv a) (.cv b)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p0230 :=
      @gBreqd (.classEq (.cv g) (synCcnv (.cv f)))
        (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g)))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (.cv a) (.cv b) p0055
    have p0237 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (.classMem (.cv a) (synCrn (.cv g)))
        (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv b) (synCrn (.cv g)))
        (.classMem (.cv b) (synCrn (synCcnv (.cv f)))) p0059 p0162
    have p0244 :=
      @gBreq12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synCfv (synCcnv (.cv g)) (.cv a))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv a))
        (synCfv (synCcnv (.cv g)) (.cv b))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (.cv r) p0066 p0169
    have p0245 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f))) syntaxFormula0027 syntaxFormula0028
        syntaxFormula0029 syntaxFormula0030 p0237 p0244
    have p0246 :=
      @gBibi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synWbr (.cv a) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv b))
        syntaxFormula0031 syntaxFormula0032 syntaxFormula0033 p0230 p0245
    have p0247 :=
      @gImbi12d (.classEq (.cv g) (synCcnv (.cv f))) (synWfun (synCcnv (.cv g)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0034 syntaxFormula0035 p0050
        p0246
    have p0248 := @gHwtrnbrd a b g r dv_cache_0016 dv_cache_0035
    have p0249 :=
      @gVtoclg (.imp (synWfun (synCcnv (.cv g))) syntaxFormula0034)
        (.imp (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0035) g
        (synCcnv (.cv f)) (synCvv) dv_cache_0017 dv_cache_0038 p0247 p0248
    have p0250 := Nominal.mp p0047 p0249
    have p0251 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0035 p0045 p0250
    have p0262 :=
      @gAnbi12i (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv a) (synCdm (.cv f)))
        (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv b) (synCdm (.cv f))) p0082 p0185
    have p0267 :=
      @gBreq12i (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (synCfv (.cv f) (.cv a))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (synCfv (.cv f) (.cv b)) (.cv r)
        p0090 p0193
    have p0268 :=
      @gAnbi12i syntaxFormula0028 syntaxFormula0036 syntaxFormula0030
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))) p0262 p0267
    have p0269 :=
      @gSyl6bb
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0031 syntaxFormula0033 syntaxFormula0037 p0251 p0268
    have p0270 :=
      @gSyl5bbr
        (synWbr (.cv a) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv b))
        syntaxFormula0031
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0037 p0220 p0269
    have p0271 :=
      @gSyl5bb (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv a) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv b))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0037 p0217 p0270
    have p0272 :=
      @gAnbi12d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv a) (.cv x))
        (.classMem (.cv b) (synCdm (.cv f))) (.classMem (.cv b) (.cv x)) p0102 p0201
    have p0273 :=
      @gAnbi1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0036 (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))) p0272
    have p0274 :=
      @gBiid (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
    have p0275 :=
      @gAnbi2i (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) p0274
    have p0276 :=
      @gA1ii
        (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
          (synWb syntaxFormula0037 syntaxFormula0038))
        (synWb syntaxFormula0038 syntaxFormula0038) p0273 p0275
    have p0277 :=
      @gBitrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b)) syntaxFormula0037
        syntaxFormula0038 p0271 p0276
    have p0278 :=
      @gBiimpd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b)) syntaxFormula0038 p0277
    have p0279 :=
      @gSyl5 syntaxFormula0014 (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0038 p0215 p0278
    have p0280 :=
      @gSimpr (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
    have p0281 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014 syntaxFormula0038
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))) p0279 p0280
    have p0282 :=
      @gA1dd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z))) p0281
    have p0283 :=
      @gAncom (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
    have p0284 := @gWppwepo (.cv y) (.cv r)
    have p0285 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCpartial) (.cv y)) p0004
        p0284
    have p0286 := @gPorta (.cv y) (.cv r)
    have p0287 :=
      @gSimp2bi (synWbr (.cv r) (synCpartial) (.cv y))
        (synWbr (.cv r) (synCref) (.cv y)) (synWbr (.cv r) (synCtrans) (.cv y))
        (synWbr (.cv r) (synCantisym) (.cv y)) p0286
    have p0288 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv r) (synCpartial) (.cv y)) (synWbr (.cv r) (synCtrans) (.cv y))
        p0285 p0287
    have p0289 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv r) (synCtrans) (.cv y)) syntaxFormula0014 p0288
    have p0290 := @gBrex (.cv r) (.cv y) (synCtrans)
    have p0291 := @gBreq (.cv c) (.cv d) (.cv g) (.cv r)
    have p0292 := @gBreq (.cv d) (.cv e) (.cv g) (.cv r)
    have p0293 :=
      @gAnbi12d (.classEq (.cv g) (.cv r)) (synWbr (.cv c) (.cv g) (.cv d))
        (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv g) (.cv e))
        (synWbr (.cv d) (.cv r) (.cv e)) p0291 p0292
    have p0294 := @gBreq (.cv c) (.cv e) (.cv g) (.cv r)
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

/-- Checked nominal proof certificate identified upstream as `g_pwpullwesetimpndv_stage2`. -/
@[expose]
noncomputable def gPwpullwesetimpndvStage2 (x : Var) (y : Var) (f : Var) (r : Var)
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
    have dv_cache_0027 : c ∉ ((synCpwpull (.cv f) (.cv r))).fv := by
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
        ((synWral c (.cv y) (synWral d (.cv y) (synWral e (.cv y) (.imp
                  (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv e)))
                  (synWbr (.cv c) (.cv r) (.cv e))))))).fv :=
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
        ((synWral c (.cv y) (synWral d (.cv y) (synWral e (.cv y) (.imp
                  (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv e)))
                  (synWbr (.cv c) (.cv r) (.cv e))))))).fv :=
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
    have dv_cache_0062 : c ∉ ((synCfv (.cv f) (.cv a))).fv := by
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
    have dv_cache_0063 : d ∉ ((synCfv (.cv f) (.cv a))).fv := by
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
    have dv_cache_0064 : e ∉ ((synCfv (.cv f) (.cv a))).fv := by
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
    have dv_cache_0065 : d ∉ ((synCfv (.cv f) (.cv b))).fv := by
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
    have dv_cache_0066 : e ∉ ((synCfv (.cv f) (.cv b))).fv := by
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
    have dv_cache_0067 : e ∉ ((synCfv (.cv f) (.cv z))).fv := by
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
        ((Wff.imp (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
              (synWbr (.cv d) (.cv r) (.cv e)))
            (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv e)))).fv :=
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
        ((Wff.imp (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
              (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z))))
            (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))))).fv :=
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
        ((Wff.imp (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
              (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (.cv e)))
            (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv e)))).fv :=
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
        ((Wff.imp (synWfun (synCcnv (synCcnv (.cv f)))) (synWb (synWbr (.cv a)
                (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
                (.cv z)) (synWa (synWa (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
                  (.classMem (.cv z) (synCrn (synCcnv (.cv f)))))
                (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (.cv r)
                  (synCfv (synCcnv (synCcnv (.cv f))) (.cv z))))))).fv :=
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
        ((synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))).fv :=
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
    have dv_cache_0074 : b ∉ (synWtru).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0075 : a ≠ b := by exact (show a ≠ b from (by exact fresh_a_ne_b))
    have dv_cache_0076 : z ∉ ((Wff.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))).fv :=
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
    have dv_cache_0077 : a ∉ ((Wff.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))).fv :=
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
    have dv_cache_0078 : b ∉ ((Wff.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))).fv :=
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
    have dv_cache_0087 : d ∉ ((synCpwpull (.cv f) (.cv r))).fv := by
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
        ((synWral a (.cv x) (synWral b (.cv x) (synWral z (.cv x) (.imp
                  (synWa (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
                    (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z)))
                  (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv z))))))).fv :=
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
        ((synWral a (.cv x) (synWral b (.cv x) (synWral z (.cv x) (.imp
                  (synWa (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
                    (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z)))
                  (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv z))))))).fv :=
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
        ((Wff.imp (synWfun (synCcnv (synCcnv (.cv f)))) (synWb (synWbr (.cv b)
                (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
                (.cv a)) (synWa (synWa (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
                  (.classMem (.cv a) (synCrn (synCcnv (.cv f)))))
                (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (.cv r)
                  (synCfv (synCcnv (synCcnv (.cv f))) (.cv a))))))).fv :=
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
        ((synWral c (.cv y) (synWral d (.cv y) (.imp (synWa (synWbr (.cv c) (.cv r) (.cv d))
                  (synWbr (.cv d) (.cv r) (.cv c))) (.objEq c d))))).fv :=
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
        ((synWral c (.cv y) (synWral d (.cv y) (.imp (synWa (synWbr (.cv c) (.cv r) (.cv d))
                  (synWbr (.cv d) (.cv r) (.cv c))) (.objEq c d))))).fv :=
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
        ((Wff.imp (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
              (synWbr (.cv d) (.cv r) (synCfv (.cv f) (.cv a))))
            (.classEq (synCfv (.cv f) (.cv a)) (.cv d)))).fv :=
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
        ((Wff.imp (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
              (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))))
            (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b))))).fv :=
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
      (synW3a (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (.cv x)))
    let syntaxFormula0013 : Wff :=
      (synWa (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z)))
    let syntaxFormula0014 : Wff := (synW3a synWtru syntaxFormula0012 syntaxFormula0013)
    let syntaxFormula0038 : Wff :=
      (synWa (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
    let syntaxFormula0039 : Wff :=
      (.imp (synWa (synWbr (.cv c) (.cv g) (.cv d)) (synWbr (.cv d) (.cv g) (.cv e)))
        (synWbr (.cv c) (.cv g) (.cv e)))
    let syntaxFormula0040 : Wff :=
      (.imp (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv e)))
        (synWbr (.cv c) (.cv r) (.cv e)))
    let syntaxFormula0041 : Wff := (synWral e (.cv h) syntaxFormula0040)
    let syntaxFormula0042 : Wff := (synWral e (.cv y) syntaxFormula0040)
    let syntaxFormula0043 : Wff := (synWral d (.cv y) syntaxFormula0042)
    let syntaxFormula0044 : Wff := (synWral c (.cv y) syntaxFormula0043)
    let syntaxFormula0045 : Wff :=
      (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (synWbr (.cv d) (.cv r) (.cv e)))
    let syntaxFormula0046 : Wff :=
      (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (.cv e)))
    let syntaxFormula0047 : Wff :=
      (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z))))
    let syntaxFormula0048 : Wff :=
      (.imp syntaxFormula0047
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))))
    let syntaxFormula0049 : Wff :=
      (synWa (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))))
    let syntaxFormula0050 : Wff :=
      (synWa (.classMem (.cv a) (synCrn (.cv g))) (.classMem (.cv z) (synCrn (.cv g))))
    let syntaxFormula0051 : Wff :=
      (synWa (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv z) (synCrn (synCcnv (.cv f)))))
    let syntaxFormula0052 : Wff :=
      (synWbr (synCfv (synCcnv (.cv g)) (.cv a)) (.cv r)
        (synCfv (synCcnv (.cv g)) (.cv z)))
    let syntaxFormula0053 : Wff :=
      (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (.cv r)
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv z)))
    let syntaxFormula0054 : Wff :=
      (synWbr (.cv a)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f)))) (.cv z))
    let syntaxFormula0055 : Wff := (synWa syntaxFormula0050 syntaxFormula0052)
    let syntaxFormula0056 : Wff := (synWa syntaxFormula0051 syntaxFormula0053)
    let syntaxFormula0057 : Wff :=
      (synWb (synWbr (.cv a) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv z))
        syntaxFormula0055)
    let syntaxFormula0058 : Wff := (synWb syntaxFormula0054 syntaxFormula0056)
    let syntaxFormula0059 : Wff :=
      (synWa (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv z) (synCdm (.cv f))))
    let syntaxFormula0060 : Wff :=
      (synWa syntaxFormula0059
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))))
    let syntaxFormula0061 : Wff :=
      (.imp syntaxFormula0013 (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv z)))
    let syntaxFormula0062 : Wff := (.imp (.classMem (.cv z) (.cv x)) syntaxFormula0061)
    let syntaxFormula0063 : Wff :=
      (.imp (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) syntaxFormula0062)
    let syntaxFormula0064 : Wff := (.all z syntaxFormula0062)
    let syntaxFormula0065 : Wff :=
      (.imp (.all z (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
        syntaxFormula0064)
    let syntaxFormula0066 : Wff :=
      (.imp (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) syntaxFormula0064)
    let syntaxFormula0067 : Wff := (synWral z (.cv x) syntaxFormula0061)
    let syntaxFormula0068 : Wff :=
      (.imp (synWa (synWbr (.cv a) (.cv c) (.cv b)) (synWbr (.cv b) (.cv c) (.cv z)))
        (synWbr (.cv a) (.cv c) (.cv z)))
    let syntaxFormula0069 : Wff := (synWral z (.cv d) syntaxFormula0061)
    let syntaxFormula0070 : Wff := (synWral b (.cv d) syntaxFormula0069)
    let syntaxFormula0071 : Wff := (synWral b (.cv x) syntaxFormula0067)
    let syntaxFormula0072 : Wff := (synWral a (.cv x) syntaxFormula0071)
    let syntaxFormula0073 : Wff :=
      (synWa (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)))
    let syntaxFormula0074 : Wff :=
      (synW3a synWtru (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0073)
    let syntaxFormula0075 : Wff :=
      (synWa (.classMem (.cv b) (synCrn (.cv g))) (.classMem (.cv a) (synCrn (.cv g))))
    let syntaxFormula0076 : Wff :=
      (synWa (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv a) (synCrn (synCcnv (.cv f)))))
    let syntaxFormula0077 : Wff :=
      (synWbr (synCfv (synCcnv (.cv g)) (.cv b)) (.cv r)
        (synCfv (synCcnv (.cv g)) (.cv a)))
    let syntaxFormula0078 : Wff :=
      (synWbr (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (.cv r)
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)))
    let syntaxFormula0079 : Wff :=
      (synWbr (.cv b)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f)))) (.cv a))
    let syntaxFormula0080 : Wff := (synWa syntaxFormula0075 syntaxFormula0077)
    let syntaxFormula0081 : Wff := (synWa syntaxFormula0076 syntaxFormula0078)
    let syntaxFormula0082 : Wff :=
      (synWb (synWbr (.cv b) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv a))
        syntaxFormula0080)
    let syntaxFormula0083 : Wff := (synWb syntaxFormula0079 syntaxFormula0081)
    let syntaxFormula0084 : Wff :=
      (synWa (.classMem (.cv b) (synCdm (.cv f))) (.classMem (.cv a) (synCdm (.cv f))))
    let syntaxFormula0085 : Wff :=
      (synWa syntaxFormula0084
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))))
    let syntaxFormula0086 : Wff :=
      (synWa (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))))
    let syntaxFormula0087 : Wff :=
      (.imp (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
        (.classEq (.cv c) (.cv d)))
    let syntaxFormula0088 : Wff := (synWral d (.cv y) syntaxFormula0087)
    let syntaxFormula0089 : Wff := (synWral c (.cv y) syntaxFormula0088)
    let syntaxFormula0090 : Wff :=
      (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (synWbr (.cv d) (.cv r) (synCfv (.cv f) (.cv a))))
    let syntaxFormula0091 : Wff :=
      (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))))
    let syntaxFormula0092 : Wff :=
      (.imp syntaxFormula0091 (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b))))
    let syntaxFormula0093 : Wff := (.imp syntaxFormula0089 syntaxFormula0092)
    let syntaxFormula0094 : Wff :=
      (synWa (synWf1 (.cv f) (.cv x) (.cv y))
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
    have p0295 :=
      @gImbi12d (.classEq (.cv g) (.cv r))
        (synWa (synWbr (.cv c) (.cv g) (.cv d)) (synWbr (.cv d) (.cv g) (.cv e)))
        (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv e)))
        (synWbr (.cv c) (.cv g) (.cv e)) (synWbr (.cv c) (.cv r) (.cv e)) p0293 p0294
    have p0296 :=
      @gRalbidv (.classEq (.cv g) (.cv r)) syntaxFormula0039 syntaxFormula0040 e (.cv h)
        dv_cache_0039 p0295
    have p0297 :=
      @gN2ralbidv (.classEq (.cv g) (.cv r)) (synWral e (.cv h) syntaxFormula0039)
        syntaxFormula0041 c d (.cv h) (.cv h) dv_cache_0040 dv_cache_0041 p0296
    have p0298 := @gRaleq syntaxFormula0040 e (.cv h) (.cv y) dv_cache_0042 dv_cache_0043
    have p0299 :=
      @gRaleqbi1dv syntaxFormula0041 syntaxFormula0042 d (.cv h) (.cv y) dv_cache_0044
        dv_cache_0010 p0298
    have p0300 :=
      @gRaleqbi1dv (synWral d (.cv h) syntaxFormula0041) syntaxFormula0043 c (.cv h)
        (.cv y) dv_cache_0045 dv_cache_0009 p0299
    have p0301 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTrans c d e g h
        dv_cache_0046 dv_cache_0047 dv_cache_0048 dv_cache_0049 dv_cache_0050
        dv_cache_0051 dv_cache_0052 dv_cache_0013 dv_cache_0053 dv_cache_0054
    have p0302 :=
      @gBrabg
        (synWral c (.cv h) (synWral d (.cv h) (synWral e (.cv h) syntaxFormula0039)))
        (synWral c (.cv h) (synWral d (.cv h) syntaxFormula0041)) syntaxFormula0044 g h
        (.cv r) (.cv y) (synCvv) (synCvv) (synCtrans) dv_cache_0055 dv_cache_0056
        dv_cache_0057 dv_cache_0058 dv_cache_0059 dv_cache_0060 dv_cache_0061 p0297 p0300
        p0301
    have p0303 :=
      @gSyl (synWbr (.cv r) (synCtrans) (.cv y))
        (synWa (.classMem (.cv r) (synCvv)) (.classMem (.cv y) (synCvv)))
        (synWb (synWbr (.cv r) (synCtrans) (.cv y)) syntaxFormula0044) p0290 p0302
    have p0304 := @gIbi (synWbr (.cv r) (synCtrans) (.cv y)) syntaxFormula0044 p0303
    have p0305 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014 (synWbr (.cv r) (synCtrans) (.cv y)) syntaxFormula0044 p0289
        p0304
    have p0309 :=
      @gSyl5 syntaxFormula0014 (.classMem (.cv a) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (synCfv (.cv f) (.cv a)) (.cv y)) p0137 p0027
    have p0311 :=
      @gSimp2 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        (.classMem (.cv z) (.cv x))
    have p0312 :=
      @gSyl syntaxFormula0014 syntaxFormula0012 (.classMem (.cv b) (.cv x)) p0135 p0311
    have p0313 := @gId (.classMem (.cv b) (.cv x))
    have p0314 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf (.cv f) (.cv x) (.cv y)) (.classMem (.cv b) (.cv x)) p0022
    have p0315 := @gFfvelrn (.cv x) (.cv y) (.cv b) (.cv f)
    have p0316 :=
      @gEx (synWf (.cv f) (.cv x) (.cv y)) (.classMem (.cv b) (.cv x))
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) p0315
    have p0317 :=
      @gSyl56 (.classMem (.cv b) (.cv x)) (.classMem (.cv b) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf (.cv f) (.cv x) (.cv y))
        (.imp (.classMem (.cv b) (.cv x)) (.classMem (synCfv (.cv f) (.cv b)) (.cv y)))
        p0313 p0314 p0316
    have p0318 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv b) (.cv x)) (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) p0317
    have p0319 :=
      @gSyl5 syntaxFormula0014 (.classMem (.cv b) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) p0312 p0318
    have p0323 := @gId (.classMem (.cv z) (.cv x))
    have p0324 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf (.cv f) (.cv x) (.cv y)) (.classMem (.cv z) (.cv x)) p0022
    have p0325 := @gFfvelrn (.cv x) (.cv y) (.cv z) (.cv f)
    have p0326 :=
      @gEx (synWf (.cv f) (.cv x) (.cv y)) (.classMem (.cv z) (.cv x))
        (.classMem (synCfv (.cv f) (.cv z)) (.cv y)) p0325
    have p0327 :=
      @gSyl56 (.classMem (.cv z) (.cv x)) (.classMem (.cv z) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf (.cv f) (.cv x) (.cv y))
        (.imp (.classMem (.cv z) (.cv x)) (.classMem (synCfv (.cv f) (.cv z)) (.cv y)))
        p0323 p0324 p0326
    have p0328 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv z) (.cv x)) (.classMem (synCfv (.cv f) (.cv z)) (.cv y)) p0327
    have p0329 :=
      @gSyl5 syntaxFormula0014 (.classMem (.cv z) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (synCfv (.cv f) (.cv z)) (.cv y)) p0140 p0328
    have p0330 :=
      @gN3jcad
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014 (.classMem (synCfv (.cv f) (.cv a)) (.cv y))
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y))
        (.classMem (synCfv (.cv f) (.cv z)) (.cv y)) p0309 p0319 p0329
    have p0331 := @gBreq1 (.cv c) (synCfv (.cv f) (.cv a)) (.cv d) (.cv r)
    have p0332 :=
      @gAnbi1d (.classEq (.cv c) (synCfv (.cv f) (.cv a)))
        (synWbr (.cv c) (.cv r) (.cv d))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (synWbr (.cv d) (.cv r) (.cv e)) p0331
    have p0333 := @gBreq1 (.cv c) (synCfv (.cv f) (.cv a)) (.cv e) (.cv r)
    have p0334 :=
      @gImbi12d (.classEq (.cv c) (synCfv (.cv f) (.cv a)))
        (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv e)))
        syntaxFormula0045 (synWbr (.cv c) (.cv r) (.cv e))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv e)) p0332 p0333
    have p0335 :=
      @gBreq2 (.cv d) (synCfv (.cv f) (.cv b)) (synCfv (.cv f) (.cv a)) (.cv r)
    have p0336 := @gBreq1 (.cv d) (synCfv (.cv f) (.cv b)) (.cv e) (.cv r)
    have p0337 :=
      @gAnbi12d (.classEq (.cv d) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (.cv d) (.cv r) (.cv e))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (.cv e)) p0335 p0336
    have p0338 :=
      @gImbi1d (.classEq (.cv d) (synCfv (.cv f) (.cv b))) syntaxFormula0045
        syntaxFormula0046 (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv e)) p0337
    have p0339 :=
      @gBreq2 (.cv e) (synCfv (.cv f) (.cv z)) (synCfv (.cv f) (.cv b)) (.cv r)
    have p0340 :=
      @gAnbi2d (.classEq (.cv e) (synCfv (.cv f) (.cv z)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (.cv e))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))) p0339
    have p0341 :=
      @gBreq2 (.cv e) (synCfv (.cv f) (.cv z)) (synCfv (.cv f) (.cv a)) (.cv r)
    have p0342 :=
      @gImbi12d (.classEq (.cv e) (synCfv (.cv f) (.cv z))) syntaxFormula0046
        syntaxFormula0047 (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv e))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))) p0340 p0341
    have p0343 :=
      @gRspc3v syntaxFormula0040 syntaxFormula0048
        (.imp syntaxFormula0045 (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv e)))
        (.imp syntaxFormula0046 (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv e))) c d e
        (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)) (synCfv (.cv f) (.cv z))
        (.cv y) (.cv y) (.cv y) dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
        dv_cache_0066 dv_cache_0067 dv_cache_0009 dv_cache_0009 dv_cache_0010
        dv_cache_0009 dv_cache_0010 dv_cache_0043 dv_cache_0068 dv_cache_0069
        dv_cache_0070 dv_cache_0013 dv_cache_0053 dv_cache_0054 p0334 p0338 p0342
    have p0344 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014
        (synW3a (.classMem (synCfv (.cv f) (.cv a)) (.cv y))
          (.classMem (synCfv (.cv f) (.cv b)) (.cv y))
          (.classMem (synCfv (.cv f) (.cv z)) (.cv y)))
        (.imp syntaxFormula0044 syntaxFormula0048) p0330 p0343
    have p0345 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014 syntaxFormula0044 syntaxFormula0048 p0305 p0344
    have p0346 :=
      @gSyl7bi
        (synWa (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
          (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
        syntaxFormula0047
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))) p0283 p0345
    have p0347 :=
      @gExp4a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))) p0346
    have p0348 :=
      Nominal.ax2 (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z)))
    have p0349 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014
        (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
          (.imp (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
            (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z)))))
        (.imp (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
            (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
          (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
            (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z)))))
        p0347 p0348
    have p0350 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014
        (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
          (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
        (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
          (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))))
        p0282 p0349
    have p0351 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv z)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))) p0212 p0350
    have p0352 :=
      @g_pm3_2 (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z)))
    have p0353 :=
      @gSyl9
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z)))
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x))) syntaxFormula0049
        p0351 p0352
    have p0354 :=
      @gSyl5 syntaxFormula0014
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x)))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.imp syntaxFormula0014 syntaxFormula0049) p0141 p0353
    have p0355 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014 syntaxFormula0049 p0354
    have p0357 :=
      @gBreqi (.cv a) (.cv z) (synCpwpull (.cv f) (.cv r))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p0360 :=
      @gBreqi (.cv a) (.cv z)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p0370 :=
      @gBreqd (.classEq (.cv g) (synCcnv (.cv f)))
        (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g)))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (.cv a) (.cv z) p0055
    have p0377 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (.classMem (.cv a) (synCrn (.cv g)))
        (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv z) (synCrn (.cv g)))
        (.classMem (.cv z) (synCrn (synCcnv (.cv f)))) p0059 p0165
    have p0384 :=
      @gBreq12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synCfv (synCcnv (.cv g)) (.cv a))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv a))
        (synCfv (synCcnv (.cv g)) (.cv z))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv z)) (.cv r) p0066 p0172
    have p0385 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f))) syntaxFormula0050 syntaxFormula0051
        syntaxFormula0052 syntaxFormula0053 p0377 p0384
    have p0386 :=
      @gBibi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synWbr (.cv a) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv z))
        syntaxFormula0054 syntaxFormula0055 syntaxFormula0056 p0370 p0385
    have p0387 :=
      @gImbi12d (.classEq (.cv g) (synCcnv (.cv f))) (synWfun (synCcnv (.cv g)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0057 syntaxFormula0058 p0050
        p0386
    have p0388 := @gHwtrnbrd a z g r dv_cache_0016 dv_cache_0036
    have p0389 :=
      @gVtoclg (.imp (synWfun (synCcnv (.cv g))) syntaxFormula0057)
        (.imp (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0058) g
        (synCcnv (.cv f)) (synCvv) dv_cache_0017 dv_cache_0071 p0387 p0388
    have p0390 := Nominal.mp p0047 p0389
    have p0391 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0058 p0045 p0390
    have p0402 :=
      @gAnbi12i (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv a) (synCdm (.cv f)))
        (.classMem (.cv z) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv z) (synCdm (.cv f))) p0082 p0190
    have p0407 :=
      @gBreq12i (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (synCfv (.cv f) (.cv a))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv z)) (synCfv (.cv f) (.cv z)) (.cv r)
        p0090 p0195
    have p0408 :=
      @gAnbi12i syntaxFormula0051 syntaxFormula0059 syntaxFormula0053
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))) p0402 p0407
    have p0409 :=
      @gSyl6bb
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0054 syntaxFormula0056 syntaxFormula0060 p0391 p0408
    have p0410 :=
      @gSyl5bbr
        (synWbr (.cv a) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv z))
        syntaxFormula0054
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0060 p0360 p0409
    have p0411 :=
      @gSyl5bb (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv z))
        (synWbr (.cv a) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv z))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0060 p0357 p0410
    have p0412 :=
      @gAnbi12d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv a) (.cv x))
        (.classMem (.cv z) (synCdm (.cv f))) (.classMem (.cv z) (.cv x)) p0102 p0202
    have p0413 :=
      @gAnbi1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0059 (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z))) p0412
    have p0414 :=
      @gBiid (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z)))
    have p0415 :=
      @gAnbi2i (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv z)))
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x))) p0414
    have p0416 :=
      @gA1ii
        (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
          (synWb syntaxFormula0060 syntaxFormula0049))
        (synWb syntaxFormula0049 syntaxFormula0049) p0413 p0415
    have p0417 :=
      @gBitrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv z)) syntaxFormula0060
        syntaxFormula0049 p0411 p0416
    have p0418 :=
      @gSylibrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0014 syntaxFormula0049
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv z)) p0355 p0417
    have p0419 :=
      @gN3expd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0012 syntaxFormula0013
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv z)) p0418
    have p0420 :=
      @gSyl7
        (synWa (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
          (.classMem (.cv z) (.cv x)))
        syntaxFormula0012
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0061 p0134 p0419
    have p0421 :=
      @gExp4a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv z) (.cv x)) syntaxFormula0061 p0420
    have p0422 :=
      @gAlimdv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0063 z dv_cache_0072 p0421
    have p0423 :=
      @gAlim (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0062 z
    have p0424 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.all z synWtru) (.all z syntaxFormula0063) syntaxFormula0065 p0422 p0423
    have p0425 :=
      @gSyl5 synWtru (.all z synWtru)
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0065 p0132 p0424
    have p0426 :=
      @gA1dd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0065
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) p0425
    have p0427 :=
      Nominal.ax2 (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.all z (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
        syntaxFormula0064
    have p0428 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru
        (.imp (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
          syntaxFormula0065)
        (.imp (.imp (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
            (.all z (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))))
          syntaxFormula0066)
        p0426 p0427
    have p0429 :=
      @gMpdi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru
        (.imp (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
          (.all z (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))))
        syntaxFormula0066 p0130 p0428
    have p0430 := (Nominal.biimpRefl syntaxFormula0067)
    have p0431 := @gBiimpri syntaxFormula0067 syntaxFormula0064 p0430
    have p0432 :=
      @gSyl8
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0064 syntaxFormula0067 p0429 p0431
    have p0433 :=
      @gRalrimdvv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0067 a b (.cv x) (.cv x) dv_cache_0028 dv_cache_0019
        dv_cache_0073 dv_cache_0020 dv_cache_0074 dv_cache_0075 p0432
    have p0437 := @gBreq (.cv a) (.cv b) (.cv c) (synCpwpull (.cv f) (.cv r))
    have p0438 := @gBreq (.cv b) (.cv z) (.cv c) (synCpwpull (.cv f) (.cv r))
    have p0439 :=
      @gAnbi12d (.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))
        (synWbr (.cv a) (.cv c) (.cv b))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (.cv c) (.cv z))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv z)) p0437 p0438
    have p0440 := @gBreq (.cv a) (.cv z) (.cv c) (synCpwpull (.cv f) (.cv r))
    have p0441 :=
      @gImbi12d (.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))
        (synWa (synWbr (.cv a) (.cv c) (.cv b)) (synWbr (.cv b) (.cv c) (.cv z)))
        syntaxFormula0013 (synWbr (.cv a) (.cv c) (.cv z))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv z)) p0439 p0440
    have p0442 :=
      @gRalbidv (.classEq (.cv c) (synCpwpull (.cv f) (.cv r))) syntaxFormula0068
        syntaxFormula0061 z (.cv d) dv_cache_0076 p0441
    have p0443 :=
      @gN2ralbidv (.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))
        (synWral z (.cv d) syntaxFormula0068) syntaxFormula0069 a b (.cv d) (.cv d)
        dv_cache_0077 dv_cache_0078 p0442
    have p0444 := @gRaleq syntaxFormula0061 z (.cv d) (.cv x) dv_cache_0079 dv_cache_0080
    have p0445 :=
      @gRaleqbi1dv syntaxFormula0069 syntaxFormula0067 b (.cv d) (.cv x) dv_cache_0002
        dv_cache_0028 p0444
    have p0446 :=
      @gRaleqbi1dv syntaxFormula0070 syntaxFormula0071 a (.cv d) (.cv x) dv_cache_0081
        dv_cache_0023 p0445
    have p0447 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTrans a b z c d
        dv_cache_0004 dv_cache_0082 dv_cache_0005 dv_cache_0083 dv_cache_0024
        dv_cache_0006 dv_cache_0084 dv_cache_0075 dv_cache_0085 dv_cache_0086
    have p0448 :=
      @gBrabg
        (synWral a (.cv d) (synWral b (.cv d) (synWral z (.cv d) syntaxFormula0068)))
        (synWral a (.cv d) syntaxFormula0070) syntaxFormula0072 c d
        (synCpwpull (.cv f) (.cv r)) (.cv x) (synCvv) (synCvv) (synCtrans)
        dv_cache_0027 dv_cache_0087 dv_cache_0029 dv_cache_0088 dv_cache_0089
        dv_cache_0090 dv_cache_0013 p0443 p0446 p0447
    have p0449 :=
      @gSyl2anc synWtru (.classMem (synCpwpull (.cv f) (.cv r)) (synCvv))
        (.classMem (.cv x) (synCvv))
        (synWb (synWbr (synCpwpull (.cv f) (.cv r)) (synCtrans) (.cv x)) syntaxFormula0072)
        p0115 p0117 p0448
    have p0450 :=
      @gBiimprd synWtru (synWbr (synCpwpull (.cv f) (.cv r)) (synCtrans) (.cv x))
        syntaxFormula0072 p0449
    have p0451 :=
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0072
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCtrans) (.cv x)) p0433 p0450
    have p0452 :=
      @gMpi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWbr (synCpwpull (.cv f) (.cv r)) (synCtrans) (.cv x)) p0000 p0451
    have p0454 :=
      @gSimp3 synWtru (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0073
    have p0455 :=
      @gSimprd syntaxFormula0074 (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)) p0454
    have p0457 :=
      @gBreqi (.cv b) (.cv a) (synCpwpull (.cv f) (.cv r))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0036
    have p0460 :=
      @gBreqi (.cv b) (.cv a)
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) p0039
    have p0470 :=
      @gBreqd (.classEq (.cv g) (synCcnv (.cv f)))
        (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g)))
        (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (synCcnv (synCcnv (.cv f))))
        (.cv b) (.cv a) p0055
    have p0477 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (.classMem (.cv b) (synCrn (.cv g)))
        (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv a) (synCrn (.cv g)))
        (.classMem (.cv a) (synCrn (synCcnv (.cv f)))) p0162 p0059
    have p0484 :=
      @gBreq12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synCfv (synCcnv (.cv g)) (.cv b))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv b))
        (synCfv (synCcnv (.cv g)) (.cv a))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (.cv r) p0169 p0066
    have p0485 :=
      @gAnbi12d (.classEq (.cv g) (synCcnv (.cv f))) syntaxFormula0075 syntaxFormula0076
        syntaxFormula0077 syntaxFormula0078 p0477 p0484
    have p0486 :=
      @gBibi12d (.classEq (.cv g) (synCcnv (.cv f)))
        (synWbr (.cv b) (synCcom (synCcom (.cv g) (.cv r)) (synCcnv (.cv g))) (.cv a))
        syntaxFormula0079 syntaxFormula0080 syntaxFormula0081 p0470 p0485
    have p0487 :=
      @gImbi12d (.classEq (.cv g) (synCcnv (.cv f))) (synWfun (synCcnv (.cv g)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0082 syntaxFormula0083 p0050
        p0486
    have p0488 := @gHwtrnbrd b a g r dv_cache_0035 dv_cache_0016
    have p0489 :=
      @gVtoclg (.imp (synWfun (synCcnv (.cv g))) syntaxFormula0082)
        (.imp (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0083) g
        (synCcnv (.cv f)) (synCvv) dv_cache_0017 dv_cache_0091 p0487 p0488
    have p0490 := Nominal.mp p0047 p0489
    have p0491 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (synCcnv (synCcnv (.cv f)))) syntaxFormula0083 p0045 p0490
    have p0502 :=
      @gAnbi12i (.classMem (.cv b) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv b) (synCdm (.cv f)))
        (.classMem (.cv a) (synCrn (synCcnv (.cv f))))
        (.classMem (.cv a) (synCdm (.cv f))) p0185 p0082
    have p0507 :=
      @gBreq12i (synCfv (synCcnv (synCcnv (.cv f))) (.cv b)) (synCfv (.cv f) (.cv b))
        (synCfv (synCcnv (synCcnv (.cv f))) (.cv a)) (synCfv (.cv f) (.cv a)) (.cv r)
        p0193 p0090
    have p0508 :=
      @gAnbi12i syntaxFormula0076 syntaxFormula0084 syntaxFormula0078
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))) p0502 p0507
    have p0509 :=
      @gSyl6bb
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0079 syntaxFormula0081 syntaxFormula0085 p0491 p0508
    have p0510 :=
      @gSyl5bbr
        (synWbr (.cv b) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv a))
        syntaxFormula0079
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0085 p0460 p0509
    have p0511 :=
      @gSyl5bb (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a))
        (synWbr (.cv b) (synCcom (synCcom (synCcnv (.cv f)) (.cv r)) (.cv f)) (.cv a))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0085 p0457 p0510
    have p0512 :=
      @gAnbi12d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv b) (synCdm (.cv f))) (.classMem (.cv b) (.cv x))
        (.classMem (.cv a) (synCdm (.cv f))) (.classMem (.cv a) (.cv x)) p0201 p0102
    have p0513 :=
      @gAnbi1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0084 (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))) p0512
    have p0514 :=
      @gBiid (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
    have p0515 :=
      @gAnbi2i (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x))) p0514
    have p0516 :=
      @gA1ii
        (.imp (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
          (synWb syntaxFormula0085 syntaxFormula0086))
        (synWb syntaxFormula0086 syntaxFormula0086) p0513 p0515
    have p0517 :=
      @gBitrd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)) syntaxFormula0085
        syntaxFormula0086 p0511 p0516
    have p0518 :=
      @gBiimpd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)) syntaxFormula0086 p0517
    have p0519 :=
      @gSyl5 syntaxFormula0074 (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0086 p0455 p0518
    have p0520 :=
      @gAncom (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
    have p0521 :=
      @gSyl6ib
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074 syntaxFormula0086
        (synWa (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
          (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x))))
        p0519 p0520
    have p0522 :=
      @gSimpl (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
    have p0523 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074
        (synWa (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
          (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x))))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))) p0521 p0522
    have p0525 :=
      @gSimpld syntaxFormula0074 (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)) p0454
    have p0526 :=
      @gSyl5 syntaxFormula0074 (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0038 p0525 p0278
    have p0527 :=
      @gAncom (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
    have p0528 :=
      @gSyl6ib
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074 syntaxFormula0038
        (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
          (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
        p0526 p0527
    have p0529 :=
      @gSimpl (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
    have p0530 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074
        (synWa (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
          (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))) p0528 p0529
    have p0531 :=
      @gA1dd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))) p0530
    have p0532 :=
      @gAncom (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
    have p0533 := @gWppweantisym (.cv y) (.cv r)
    have p0534 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCantisym) (.cv y)) p0004
        p0533
    have p0535 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv r) (synCantisym) (.cv y)) syntaxFormula0074 p0534
    have p0536 := @gBrex (.cv r) (.cv y) (synCantisym)
    have p0537 := @gBreq (.cv c) (.cv d) (.cv e) (.cv r)
    have p0538 := @gBreq (.cv d) (.cv c) (.cv e) (.cv r)
    have p0539 :=
      @gAnbi12d (.classEq (.cv e) (.cv r)) (synWbr (.cv c) (.cv e) (.cv d))
        (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv e) (.cv c))
        (synWbr (.cv d) (.cv r) (.cv c)) p0537 p0538
    have p0540 :=
      @gImbi1d (.classEq (.cv e) (.cv r))
        (synWa (synWbr (.cv c) (.cv e) (.cv d)) (synWbr (.cv d) (.cv e) (.cv c)))
        (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
        (.objEq c d) p0539
    have p0541 :=
      @gN2ralbidv (.classEq (.cv e) (.cv r))
        (.imp (synWa (synWbr (.cv c) (.cv e) (.cv d)) (synWbr (.cv d) (.cv e) (.cv c)))
          (.objEq c d))
        (.imp (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
          (.objEq c d))
        c d (.cv g) (.cv g) dv_cache_0092 dv_cache_0093 p0540
    have p0542 :=
      @gRaleq
        (.imp (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
          (.objEq c d))
        d (.cv g) (.cv y) dv_cache_0094 dv_cache_0010
    have p0543 :=
      @gRaleqbi1dv
        (synWral d (.cv g) (.imp
            (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
            (.objEq c d)))
        (synWral d (.cv y) (.imp
            (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
            (.objEq c d)))
        c (.cv g) (.cv y) dv_cache_0095 dv_cache_0009 p0542
    have p0544 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAntisym c d e g
        dv_cache_0052 dv_cache_0050 dv_cache_0051 dv_cache_0096 dv_cache_0097
        dv_cache_0013
    have p0545 :=
      @gBrabg
        (synWral c (.cv g) (synWral d (.cv g) (.imp
              (synWa (synWbr (.cv c) (.cv e) (.cv d)) (synWbr (.cv d) (.cv e) (.cv c)))
              (.objEq c d))))
        (synWral c (.cv g) (synWral d (.cv g) (.imp
              (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
              (.objEq c d))))
        (synWral c (.cv y) (synWral d (.cv y) (.imp
              (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
              (.objEq c d))))
        e g (.cv r) (.cv y) (synCvv) (synCvv) (synCantisym) dv_cache_0098 dv_cache_0055
        dv_cache_0043 dv_cache_0057 dv_cache_0099 dv_cache_0100 dv_cache_0101 p0541 p0543
        p0544
    have p0546 :=
      @gSyl (synWbr (.cv r) (synCantisym) (.cv y))
        (synWa (.classMem (.cv r) (synCvv)) (.classMem (.cv y) (synCvv)))
        (synWb (synWbr (.cv r) (synCantisym) (.cv y)) (synWral c (.cv y) (synWral d (.cv y)
              (.imp (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
                (.objEq c d)))))
        p0536 p0545
    have p0547 :=
      @gIbi (synWbr (.cv r) (synCantisym) (.cv y))
        (synWral c (.cv y) (synWral d (.cv y) (.imp
              (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
              (.objEq c d))))
        p0546
    have p0548_e01_recanon :
      Nominal.NPrf (.imp (synWbr (.cv r) (synCantisym) (.cv y)) syntaxFormula0089) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWbr, synCop, synCun, synCnin, synWnan, synWa, synCcompl,
            synWrex, synWex, synCphi, synCantisym, synCopab, synWral]
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
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074 (synWbr (.cv r) (synCantisym) (.cv y)) syntaxFormula0089 p0535
        p0548_e01_recanon
    have p0549 :=
      @gSimp2 synWtru (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0073
    have p0550 :=
      @gSimpld syntaxFormula0074 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        p0549
    have p0551 :=
      @gSyl5 syntaxFormula0074 (.classMem (.cv a) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (synCfv (.cv f) (.cv a)) (.cv y)) p0550 p0027
    have p0553 :=
      @gSimprd syntaxFormula0074 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        p0549
    have p0554 :=
      @gSyl5 syntaxFormula0074 (.classMem (.cv b) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) p0553 p0318
    have p0555 := @gBreq1 (.cv c) (synCfv (.cv f) (.cv a)) (.cv d) (.cv r)
    have p0556 := @gBreq2 (.cv c) (synCfv (.cv f) (.cv a)) (.cv d) (.cv r)
    have p0557 :=
      @gAnbi12d (.classEq (.cv c) (synCfv (.cv f) (.cv a)))
        (synWbr (.cv c) (.cv r) (.cv d))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (synWbr (.cv d) (.cv r) (.cv c))
        (synWbr (.cv d) (.cv r) (synCfv (.cv f) (.cv a))) p0555 p0556
    have p0558 := @gEqeq1 (.cv c) (synCfv (.cv f) (.cv a)) (.cv d)
    have p0559_e01_recanon :
      Nominal.NPrf
        (.imp (.classEq (.cv c) (synCfv (.cv f) (.cv a)))
          (synWb (.objEq c d) (.classEq (synCfv (.cv f) (.cv a)) (.cv d)))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synCfv, synCio, synCuni, synWex, synWa, synCsn, synWbr,
            synCop, synCun, synCnin, synWnan, synCcompl, synWrex, synCphi, synWb]
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
      @gImbi12d (.classEq (.cv c) (synCfv (.cv f) (.cv a)))
        (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
        syntaxFormula0090 (.objEq c d) (.classEq (synCfv (.cv f) (.cv a)) (.cv d)) p0557
        p0559_e01_recanon
    have p0560 :=
      @gBreq2 (.cv d) (synCfv (.cv f) (.cv b)) (synCfv (.cv f) (.cv a)) (.cv r)
    have p0561 :=
      @gBreq1 (.cv d) (synCfv (.cv f) (.cv b)) (synCfv (.cv f) (.cv a)) (.cv r)
    have p0562 :=
      @gAnbi12d (.classEq (.cv d) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (.cv d) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))) p0560 p0561
    have p0563 := @gEqeq2 (.cv d) (synCfv (.cv f) (.cv b)) (synCfv (.cv f) (.cv a))
    have p0564 :=
      @gImbi12d (.classEq (.cv d) (synCfv (.cv f) (.cv b))) syntaxFormula0090
        syntaxFormula0091 (.classEq (synCfv (.cv f) (.cv a)) (.cv d))
        (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b))) p0562 p0563
    have p0565 :=
      @gRspc2v
        (.imp (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
          (.objEq c d))
        syntaxFormula0092
        (.imp syntaxFormula0090 (.classEq (synCfv (.cv f) (.cv a)) (.cv d))) c d
        (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)) (.cv y) (.cv y) dv_cache_0062
        dv_cache_0063 dv_cache_0065 dv_cache_0009 dv_cache_0009 dv_cache_0010
        dv_cache_0102 dv_cache_0103 dv_cache_0013 p0559 p0564
    have p0566 :=
      @gEx (.classMem (synCfv (.cv f) (.cv a)) (.cv y))
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y))
        (.imp (synWral c (.cv y) (synWral d (.cv y) (.imp
                (synWa (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
                (.objEq c d)))) syntaxFormula0092)
        p0565
    have p0567_e02_recanon :
      Nominal.NPrf
        (.imp (.classMem (synCfv (.cv f) (.cv a)) (.cv y))
          (.imp (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0093)) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synCfv, synCio, synCuni, synWex, synWa, synCsn, synWbr,
            synCop, synCun, synCnin, synWnan, synCcompl, synWrex, synCphi,
            synWral]
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
      @gSyl6c
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074 (.classMem (synCfv (.cv f) (.cv a)) (.cv y))
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0093 p0551 p0554
        p0567_e02_recanon
    have p0568 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074 syntaxFormula0089 syntaxFormula0092 p0548 p0567
    have p0569 :=
      @gSyl7bi
        (synWa (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
          (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
        syntaxFormula0091
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074 (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)))
        p0532 p0568
    have p0570 :=
      @gExp4a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b))) p0569
    have p0571 :=
      Nominal.ax2 (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)))
    have p0572 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074
        (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
          (.imp (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
            (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)))))
        (.imp (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
            (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
          (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
            (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)))))
        p0570 p0571
    have p0573 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074
        (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
          (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
        (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
          (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b))))
        p0531 p0572
    have p0574 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
        (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b))) p0523 p0573
    have p0575 := @gF1of1 (.cv x) (.cv y) (.cv f)
    have p0576 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf1o (.cv f) (.cv x) (.cv y)) (synWf1 (.cv f) (.cv x) (.cv y)) p0018 p0575
    have p0577 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf1 (.cv f) (.cv x) (.cv y)) syntaxFormula0074 p0576
    have p0579 :=
      @g_pm3_2 (synWf1 (.cv f) (.cv x) (.cv y))
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
    have p0580 :=
      @gSyl5 syntaxFormula0074
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWf1 (.cv f) (.cv x) (.cv y)) syntaxFormula0094 p0549 p0579
    have p0581 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074 (synWf1 (.cv f) (.cv x) (.cv y))
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

/-- Checked nominal proof certificate identified upstream as `g_pwpullwesetimpndv_stage3`. -/
@[expose]
noncomputable def gPwpullwesetimpndvStage3 (x : Var) (y : Var) (f : Var) (r : Var)
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
    have dv_cache_0027 : c ∉ ((synCpwpull (.cv f) (.cv r))).fv := by
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
    have dv_cache_0062 : c ∉ ((synCfv (.cv f) (.cv a))).fv := by
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
    have dv_cache_0063 : d ∉ ((synCfv (.cv f) (.cv a))).fv := by
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
    have dv_cache_0065 : d ∉ ((synCfv (.cv f) (.cv b))).fv := by
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
    have dv_cache_0074 : b ∉ (synWtru).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0075 : a ≠ b := by exact (show a ≠ b from (by exact fresh_a_ne_b))
    have dv_cache_0077 : a ∉ ((Wff.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))).fv :=
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
    have dv_cache_0078 : b ∉ ((Wff.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))).fv :=
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
    have dv_cache_0087 : d ∉ ((synCpwpull (.cv f) (.cv r))).fv := by
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
        ((synWral a (.cv x) (synWral b (.cv x) (.imp
                (synWa (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
                  (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)))
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
        ((synWral a (.cv x) (synWral b (.cv x) (.imp
                (synWa (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
                  (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)))
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
        ((synWral c (.cv y) (synWral d (.cv y) (synWo (synWbr (.cv c) (.cv r) (.cv d))
                (synWbr (.cv d) (.cv r) (.cv c)))))).fv :=
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
        ((synWral c (.cv y) (synWral d (.cv y) (synWo (synWbr (.cv c) (.cv r) (.cv d))
                (synWbr (.cv d) (.cv r) (.cv c)))))).fv :=
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
        ((synWo (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
            (synWbr (.cv d) (.cv r) (synCfv (.cv f) (.cv a))))).fv :=
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
        ((synWo (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
            (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))))).fv :=
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
        ((synWral a (.cv x) (synWral b (.cv x)
              (synWo (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
                (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)))))).fv :=
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
        ((synWral a (.cv x) (synWral b (.cv x)
              (synWo (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
                (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)))))).fv :=
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
        ((synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))).fv :=
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
    have dv_cache_0114 : u ∉ ((synCfv (.cv f) (.cv c))).fv := by
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
      u ∉ ((Wff.classMem (synCfv (.cv f) (.cv c)) (synCima (.cv f) (.cv a)))).fv := by
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
        ((synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))).fv :=
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
      c ∉ ((synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a))))).fv := by
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
    have dv_cache_0119 : u ∉ ((synCima (.cv f) (.cv a))).fv := by
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
      (synWa (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
    let syntaxFormula0073 : Wff :=
      (synWa (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)))
    let syntaxFormula0074 : Wff :=
      (synW3a synWtru (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0073)
    let syntaxFormula0086 : Wff :=
      (synWa (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))))
    let syntaxFormula0094 : Wff :=
      (synWa (synWf1 (.cv f) (.cv x) (.cv y))
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))))
    let syntaxFormula0095 : Wff := (.imp syntaxFormula0073 (.classEq (.cv a) (.cv b)))
    let syntaxFormula0096 : Wff := (synWral b (.cv x) syntaxFormula0095)
    let syntaxFormula0097 : Wff := (synWral a (.cv x) syntaxFormula0096)
    let syntaxFormula0098 : Wff :=
      (synWral d (.cv y)
        (synWo (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c))))
    let syntaxFormula0099 : Wff := (synWral c (.cv y) syntaxFormula0098)
    let syntaxFormula0100 : Wff :=
      (synWo (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))))
    let syntaxFormula0101 : Wff := (.imp syntaxFormula0099 syntaxFormula0100)
    let syntaxFormula0102 : Wff :=
      (synWa (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))))
    let syntaxFormula0103 : Wff :=
      (synWa (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))))
    let syntaxFormula0104 : Wff :=
      (synWo (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)))
    let syntaxFormula0105 : Wff := (.imp syntaxFormula0100 syntaxFormula0104)
    let syntaxFormula0106 : Wff := (synWral b (.cv x) syntaxFormula0104)
    let syntaxFormula0107 : Wff := (synWral a (.cv x) syntaxFormula0106)
    let syntaxFormula0108 : Wff :=
      (synWa (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv c) (.cv a)))
    let syntaxFormula0109 : Wff :=
      (synWa (.classMem (.cv c) (.cv a))
        (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a)))))
    let syntaxFormula0110 : Wff := (.imp (.classMem (.cv c) (.cv a)) syntaxFormula0109)
    let syntaxFormula0111 : Wff := (synWex c syntaxFormula0109)
    let syntaxFormula0112 : Wff :=
      (synWrex c (.cv a) (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a)))))
    let syntaxFormula0113 : Wff :=
      (synWa (.classMem (.cv u) (.cv y)) (.classMem (.cv u) (synCima (.cv f) (.cv a))))
    let syntaxClass0114 : Class := (.cab u syntaxFormula0113)
    let syntaxFormula0115 : Wff := (synWne syntaxClass0114 (synC0))
    let syntaxFormula0116 : Wff := (synWss syntaxClass0114 (.cv y))
    let syntaxFormula0117 : Wff :=
      (.classMem (synCin (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a)))) (.cv y))
        (synCvv))
    let syntaxFormula0118 : Wff := (.classMem syntaxClass0114 (synCvv))
    have p0582 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074 syntaxFormula0094 p0581
    have p0583 := @gF1fveq (.cv x) (.cv y) (.cv a) (.cv b) (.cv f)
    have p0584 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074 syntaxFormula0094
        (synWb (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)))
          (.classEq (.cv a) (.cv b)))
        p0582 p0583
    have p0585 :=
      @gBi1 (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)))
        (.classEq (.cv a) (.cv b))
    have p0586 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074
        (synWb (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)))
          (.classEq (.cv a) (.cv b)))
        (.imp (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)))
          (.classEq (.cv a) (.cv b)))
        p0584 p0585
    have p0587 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0074 (.classEq (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)))
        (.classEq (.cv a) (.cv b)) p0574 p0586
    have p0588 :=
      @gN3expd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0073 (.classEq (.cv a) (.cv b)) p0587
    have p0589 :=
      @gImp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0095 p0588
    have p0590 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0095 p0589
    have p0591 :=
      @gRalrimdvv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0095 a b (.cv x) (.cv x) dv_cache_0028 dv_cache_0019
        dv_cache_0073 dv_cache_0020 dv_cache_0074 dv_cache_0075 p0590
    have p0592 := @gPwpullex (.cv r) (.cv f) p0046 p0113
    have p0593 :=
      @gA1i (.classMem (synCpwpull (.cv f) (.cv r)) (synCvv)) synWtru p0592
    have p0594 := @gA1i (.classMem (.cv x) (synCvv)) synWtru p0116
    have p0595 := @gBreq (.cv a) (.cv b) (.cv c) (synCpwpull (.cv f) (.cv r))
    have p0596 := @gBreq (.cv b) (.cv a) (.cv c) (synCpwpull (.cv f) (.cv r))
    have p0597 :=
      @gAnbi12d (.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))
        (synWbr (.cv a) (.cv c) (.cv b))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (.cv c) (.cv a))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)) p0595 p0596
    have p0598 :=
      @gImbi1d (.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))
        (synWa (synWbr (.cv a) (.cv c) (.cv b)) (synWbr (.cv b) (.cv c) (.cv a)))
        syntaxFormula0073 (.objEq a b) p0597
    have p0599 :=
      @gN2ralbidv (.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))
        (.imp (synWa (synWbr (.cv a) (.cv c) (.cv b)) (synWbr (.cv b) (.cv c) (.cv a)))
          (.objEq a b))
        (.imp syntaxFormula0073 (.objEq a b)) a b (.cv d) (.cv d) dv_cache_0077
        dv_cache_0078 p0598
    have p0600 :=
      @gRaleq (.imp syntaxFormula0073 (.objEq a b)) b (.cv d) (.cv x) dv_cache_0002
        dv_cache_0028
    have p0601 :=
      @gRaleqbi1dv (synWral b (.cv d) (.imp syntaxFormula0073 (.objEq a b)))
        (synWral b (.cv x) (.imp syntaxFormula0073 (.objEq a b))) a (.cv d) (.cv x)
        dv_cache_0081 dv_cache_0023 p0600
    have p0602 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAntisym a b c d
        dv_cache_0004 dv_cache_0082 dv_cache_0005 dv_cache_0024 dv_cache_0006
        dv_cache_0075
    have p0603 :=
      @gBrabg
        (synWral a (.cv d) (synWral b (.cv d) (.imp
              (synWa (synWbr (.cv a) (.cv c) (.cv b)) (synWbr (.cv b) (.cv c) (.cv a)))
              (.objEq a b))))
        (synWral a (.cv d) (synWral b (.cv d) (.imp syntaxFormula0073 (.objEq a b))))
        (synWral a (.cv x) (synWral b (.cv x) (.imp syntaxFormula0073 (.objEq a b)))) c
        d (synCpwpull (.cv f) (.cv r)) (.cv x) (synCvv) (synCvv) (synCantisym)
        dv_cache_0027 dv_cache_0087 dv_cache_0029 dv_cache_0088 dv_cache_0104
        dv_cache_0105 dv_cache_0013 p0599 p0601 p0602
    have p0604 :=
      @gSyl2anc synWtru (.classMem (synCpwpull (.cv f) (.cv r)) (synCvv))
        (.classMem (.cv x) (synCvv))
        (synWb (synWbr (synCpwpull (.cv f) (.cv r)) (synCantisym) (.cv x))
          (synWral a (.cv x) (synWral b (.cv x) (.imp syntaxFormula0073 (.objEq a b)))))
        p0593 p0594 p0603
    have p0605 :=
      @gBiimprd synWtru (synWbr (synCpwpull (.cv f) (.cv r)) (synCantisym) (.cv x))
        (synWral a (.cv x) (synWral b (.cv x) (.imp syntaxFormula0073 (.objEq a b))))
        p0604
    have p0606_e01_recanon :
      Nominal.NPrf
        (.imp synWtru (.imp syntaxFormula0097
            (synWbr (synCpwpull (.cv f) (.cv r)) (synCantisym) (.cv x)))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [synWtru, synWral, synWbr, synCop, synCun, synCnin, synWnan,
            synWa, synCcompl, synWrex, synWex, synCphi, synCpwpull, synCcom,
            synCopab, synCantisym]
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
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0097
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCantisym) (.cv x)) p0591
        p0606_e01_recanon
    have p0607 :=
      @gMpi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWbr (synCpwpull (.cv f) (.cv r)) (synCantisym) (.cv x)) p0000
        p0606
    have p0608 :=
      @gN3jca
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCref) (.cv x))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCtrans) (.cv x))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCantisym) (.cv x)) p0126 p0452 p0607
    have p0609 := @gPorta (.cv x) (synCpwpull (.cv f) (.cv r))
    have p0610 :=
      @gSylibr
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synW3a (synWbr (synCpwpull (.cv f) (.cv r)) (synCref) (.cv x))
          (synWbr (synCpwpull (.cv f) (.cv r)) (synCtrans) (.cv x))
          (synWbr (synCpwpull (.cv f) (.cv r)) (synCantisym) (.cv x)))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCpartial) (.cv x)) p0608 p0609
    have p0612 := @gWppweconnex (.cv y) (.cv r)
    have p0613 :=
      @gSyl
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCconnex) (.cv y)) p0004
        p0612
    have p0614 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv r) (synCconnex) (.cv y))
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))) p0613
    have p0615 := @gBrex (.cv r) (.cv y) (synCconnex)
    have p0618 :=
      @gOrbi12d (.classEq (.cv e) (.cv r)) (synWbr (.cv c) (.cv e) (.cv d))
        (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv e) (.cv c))
        (synWbr (.cv d) (.cv r) (.cv c)) p0537 p0538
    have p0619 :=
      @gN2ralbidv (.classEq (.cv e) (.cv r))
        (synWo (synWbr (.cv c) (.cv e) (.cv d)) (synWbr (.cv d) (.cv e) (.cv c)))
        (synWo (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c))) c d
        (.cv g) (.cv g) dv_cache_0092 dv_cache_0093 p0618
    have p0620 :=
      @gRaleq
        (synWo (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c))) d
        (.cv g) (.cv y) dv_cache_0094 dv_cache_0010
    have p0621 :=
      @gRaleqbi1dv
        (synWral d (.cv g)
          (synWo (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c))))
        syntaxFormula0098 c (.cv g) (.cv y) dv_cache_0095 dv_cache_0009 p0620
    have p0622 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfConnex c d e g
        dv_cache_0052 dv_cache_0050 dv_cache_0051 dv_cache_0096 dv_cache_0097
        dv_cache_0013
    have p0623 :=
      @gBrabg
        (synWral c (.cv g) (synWral d (.cv g)
            (synWo (synWbr (.cv c) (.cv e) (.cv d)) (synWbr (.cv d) (.cv e) (.cv c)))))
        (synWral c (.cv g) (synWral d (.cv g)
            (synWo (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))))
        syntaxFormula0099 e g (.cv r) (.cv y) (synCvv) (synCvv) (synCconnex)
        dv_cache_0098 dv_cache_0055 dv_cache_0043 dv_cache_0057 dv_cache_0106
        dv_cache_0107 dv_cache_0101 p0619 p0621 p0622
    have p0624 :=
      @gSyl (synWbr (.cv r) (synCconnex) (.cv y))
        (synWa (.classMem (.cv r) (synCvv)) (.classMem (.cv y) (synCvv)))
        (synWb (synWbr (.cv r) (synCconnex) (.cv y)) syntaxFormula0099) p0615 p0623
    have p0625 := @gIbi (synWbr (.cv r) (synCconnex) (.cv y)) syntaxFormula0099 p0624
    have p0626 :=
      @gSimp2 synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
    have p0627 :=
      @gSyl5 (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv a) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (synCfv (.cv f) (.cv a)) (.cv y)) p0626 p0027
    have p0628 :=
      @gSimp3 synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
    have p0629 :=
      @gSyl5 (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv b) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) p0628 p0318
    have p0632 :=
      @gOrbi12d (.classEq (.cv c) (synCfv (.cv f) (.cv a)))
        (synWbr (.cv c) (.cv r) (.cv d))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (synWbr (.cv d) (.cv r) (.cv c))
        (synWbr (.cv d) (.cv r) (synCfv (.cv f) (.cv a))) p0331 p0556
    have p0635 :=
      @gOrbi12d (.classEq (.cv d) (synCfv (.cv f) (.cv b)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (.cv d) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))) p0335 p0561
    have p0636 :=
      @gRspc2v
        (synWo (synWbr (.cv c) (.cv r) (.cv d)) (synWbr (.cv d) (.cv r) (.cv c)))
        syntaxFormula0100
        (synWo (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (.cv d))
          (synWbr (.cv d) (.cv r) (synCfv (.cv f) (.cv a))))
        c d (synCfv (.cv f) (.cv a)) (synCfv (.cv f) (.cv b)) (.cv y) (.cv y)
        dv_cache_0062 dv_cache_0063 dv_cache_0065 dv_cache_0009 dv_cache_0009
        dv_cache_0010 dv_cache_0108 dv_cache_0109 dv_cache_0013 p0632 p0635
    have p0637 :=
      @gEx (.classMem (synCfv (.cv f) (.cv a)) (.cv y))
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0101 p0636
    have p0638 :=
      @gSyl6c
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (synCfv (.cv f) (.cv a)) (.cv y))
        (.classMem (synCfv (.cv f) (.cv b)) (.cv y)) syntaxFormula0101 p0627 p0629 p0637
    have p0639 :=
      @gSyl7 (synWbr (.cv r) (synCconnex) (.cv y)) syntaxFormula0099
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0100 p0625 p0638
    have p0640 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (.cv r) (synCconnex) (.cv y)) syntaxFormula0100 p0614 p0639
    have p0641 :=
      @gSimpl (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
    have p0643 :=
      @gSyl syntaxFormula0102
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv a) (.cv x)) p0641 p0626
    have p0646 :=
      @gSyl syntaxFormula0102
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv b) (.cv x)) p0641 p0628
    have p0647 :=
      @gJca syntaxFormula0102 (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x))
        p0643 p0646
    have p0648 :=
      @gSimpr (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
    have p0649 :=
      @gJca syntaxFormula0102
        (synWa (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b))) p0647 p0648
    have p0650 :=
      @gSyl5ibr syntaxFormula0102 (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0038 p0649 p0277
    have p0651 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b)) p0650
    have p0652 :=
      @gSimpl (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
    have p0654 :=
      @gSyl syntaxFormula0103
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv b) (.cv x)) p0652 p0628
    have p0657 :=
      @gSyl syntaxFormula0103
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.classMem (.cv a) (.cv x)) p0652 p0626
    have p0658 :=
      @gJca syntaxFormula0103 (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x))
        p0654 p0657
    have p0659 :=
      @gSimpr (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
    have p0660 :=
      @gJca syntaxFormula0103
        (synWa (.classMem (.cv b) (.cv x)) (.classMem (.cv a) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a))) p0658 p0659
    have p0661 :=
      @gSyl5ibr syntaxFormula0103 (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0086 p0660 p0517
    have p0662 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)) p0661
    have p0663 :=
      @gPm348 (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a))
    have p0664 :=
      @gEx
        (.imp (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
          (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b)))
        (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
          (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)))
        syntaxFormula0105 p0663
    have p0665 :=
      @gSyl6c
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        (.imp (synWbr (synCfv (.cv f) (.cv a)) (.cv r) (synCfv (.cv f) (.cv b)))
          (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b)))
        (.imp (synWbr (synCfv (.cv f) (.cv b)) (.cv r) (synCfv (.cv f) (.cv a)))
          (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)))
        syntaxFormula0105 p0651 p0662 p0664
    have p0666 :=
      @gMpdd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synW3a synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)))
        syntaxFormula0100 syntaxFormula0104 p0640 p0665
    have p0667 :=
      @gN3expd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)) syntaxFormula0104
        p0666
    have p0668 :=
      @gImp4a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (.classMem (.cv a) (.cv x)) (.classMem (.cv b) (.cv x)) syntaxFormula0104
        p0667
    have p0669 :=
      @gRalrimdvv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0104 a b (.cv x) (.cv x) dv_cache_0028 dv_cache_0019
        dv_cache_0073 dv_cache_0020 dv_cache_0074 dv_cache_0075 p0668
    have p0675 :=
      @gOrbi12d (.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))
        (synWbr (.cv a) (.cv c) (.cv b))
        (synWbr (.cv a) (synCpwpull (.cv f) (.cv r)) (.cv b))
        (synWbr (.cv b) (.cv c) (.cv a))
        (synWbr (.cv b) (synCpwpull (.cv f) (.cv r)) (.cv a)) p0437 p0596
    have p0676 :=
      @gN2ralbidv (.classEq (.cv c) (synCpwpull (.cv f) (.cv r)))
        (synWo (synWbr (.cv a) (.cv c) (.cv b)) (synWbr (.cv b) (.cv c) (.cv a)))
        syntaxFormula0104 a b (.cv d) (.cv d) dv_cache_0077 dv_cache_0078 p0675
    have p0677 := @gRaleq syntaxFormula0104 b (.cv d) (.cv x) dv_cache_0002 dv_cache_0028
    have p0678 :=
      @gRaleqbi1dv (synWral b (.cv d) syntaxFormula0104) syntaxFormula0106 a (.cv d)
        (.cv x) dv_cache_0081 dv_cache_0023 p0677
    have p0679 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfConnex a b c d
        dv_cache_0004 dv_cache_0082 dv_cache_0005 dv_cache_0024 dv_cache_0006
        dv_cache_0075
    have p0680 :=
      @gBrabg
        (synWral a (.cv d) (synWral b (.cv d)
            (synWo (synWbr (.cv a) (.cv c) (.cv b)) (synWbr (.cv b) (.cv c) (.cv a)))))
        (synWral a (.cv d) (synWral b (.cv d) syntaxFormula0104)) syntaxFormula0107 c d
        (synCpwpull (.cv f) (.cv r)) (.cv x) (synCvv) (synCvv) (synCconnex)
        dv_cache_0027 dv_cache_0087 dv_cache_0029 dv_cache_0088 dv_cache_0110
        dv_cache_0111 dv_cache_0013 p0676 p0678 p0679
    have p0681 :=
      @gSyl2anc synWtru (.classMem (synCpwpull (.cv f) (.cv r)) (synCvv))
        (.classMem (.cv x) (synCvv))
        (synWb (synWbr (synCpwpull (.cv f) (.cv r)) (synCconnex) (.cv x)) syntaxFormula0107)
        p0115 p0117 p0680
    have p0682 :=
      @gBiimprd synWtru (synWbr (synCpwpull (.cv f) (.cv r)) (synCconnex) (.cv x))
        syntaxFormula0107 p0681
    have p0683 :=
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru syntaxFormula0107
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCconnex) (.cv x)) p0669 p0682
    have p0684 :=
      @gMpi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        synWtru (synWbr (synCpwpull (.cv f) (.cv r)) (synCconnex) (.cv x)) p0000 p0683
    have p0685 :=
      @gJca
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCpartial) (.cv x))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCconnex) (.cv x)) p0610 p0684
    have p0686 := @gSopc (.cv x) (synCpwpull (.cv f) (.cv r))
    have p0687 :=
      @gSylibr
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa (synWbr (synCpwpull (.cv f) (.cv r)) (synCpartial) (.cv x))
          (synWbr (synCpwpull (.cv f) (.cv r)) (synCconnex) (.cv x)))
        (synWbr (synCpwpull (.cv f) (.cv r)) (synCstrict) (.cv x)) p0685 p0686
    have p0689 :=
      @gSimpr synWtru (synWa (synWss (.cv u) (.cv x)) (synWne (.cv u) (synC0)))
    have p0690 :=
      @gSimprd
        (synWa synWtru (synWa (synWss (.cv u) (.cv x)) (synWne (.cv u) (synC0))))
        (synWss (.cv u) (.cv x)) (synWne (.cv u) (synC0)) p0689
    have p0692 :=
      @gSimpld
        (synWa synWtru (synWa (synWss (.cv u) (.cv x)) (synWne (.cv u) (synC0))))
        (synWss (.cv u) (.cv x)) (synWne (.cv u) (synC0)) p0689
    have p0693 :=
      @gA1d
        (synWa synWtru (synWa (synWss (.cv u) (.cv x)) (synWne (.cv u) (synC0))))
        (synWss (.cv u) (.cv x)) (synWne (.cv u) (synC0)) p0692
    have p0694 := @gAncom (synWne (.cv u) (synC0)) (synWss (.cv u) (.cv x))
    have p0695 := @gVex u
    have p0696 :=
      @gA1i (.classMem (.cv u) (synCvv))
        (synWa synWtru (synWa (synWss (.cv u) (.cv x)) (synWne (.cv u) (synC0))))
        p0695
    have p0698 :=
      @gId
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
    have p0699 :=
      @gSimpr synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))
    have p0700 := @gSimpr (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))
    have p0701 :=
      @gSyl
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))
        (synWne (.cv a) (synC0)) p0699 p0700
    have p0702 :=
      @gJca
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWne (.cv a) (synC0)) p0698 p0701
    have p0703 := @gN0 c (.cv a) dv_cache_0112
    have p0704 :=
      @gBiimpi (synWne (.cv a) (synC0)) (synWex c (.classMem (.cv c) (.cv a))) p0703
    have p0705 :=
      Nominal.ax17
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))) c
        dv_cache_0113
    have p0706 :=
      @gSimpl
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv c) (.cv a))
    have p0708 := @gSimpl (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))
    have p0709 :=
      @gSyl
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))
        (synWss (.cv a) (.cv x)) p0699 p0708
    have p0710 :=
      @gSyl syntaxFormula0108
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWss (.cv a) (.cv x)) p0706 p0709
    have p0711 :=
      @gSimpr
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv c) (.cv a))
    have p0712 :=
      @gJca syntaxFormula0108 (synWss (.cv a) (.cv x)) (.classMem (.cv c) (.cv a)) p0710
        p0711
    have p0713 := @gSsel2 (.cv a) (.cv x) (.cv c)
    have p0714 :=
      @gSyl syntaxFormula0108
        (synWa (synWss (.cv a) (.cv x)) (.classMem (.cv c) (.cv a)))
        (.classMem (.cv c) (.cv x)) p0712 p0713
    have p0715 := @gId (.classMem (.cv c) (.cv x))
    have p0716 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf (.cv f) (.cv x) (.cv y)) (.classMem (.cv c) (.cv x)) p0022
    have p0717 := @gFfvelrn (.cv x) (.cv y) (.cv c) (.cv f)
    have p0718 :=
      @gEx (synWf (.cv f) (.cv x) (.cv y)) (.classMem (.cv c) (.cv x))
        (.classMem (synCfv (.cv f) (.cv c)) (.cv y)) p0717
    have p0719 :=
      @gSyl56 (.classMem (.cv c) (.cv x)) (.classMem (.cv c) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWf (.cv f) (.cv x) (.cv y))
        (.imp (.classMem (.cv c) (.cv x)) (.classMem (synCfv (.cv f) (.cv c)) (.cv y)))
        p0715 p0716 p0718
    have p0720 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv c) (.cv x)) (.classMem (synCfv (.cv f) (.cv c)) (.cv y)) p0719
    have p0721 :=
      @gSyl5 syntaxFormula0108 (.classMem (.cv c) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (synCfv (.cv f) (.cv c)) (.cv y)) p0714 p0720
    have p0723 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWfun (.cv f)) syntaxFormula0108 p0042
    have p0733 :=
      @gEleq2d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synCdm (.cv f)) (.cv x) (.cv c) p0101
    have p0734 :=
      @gBiimprd
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv c) (synCdm (.cv f))) (.classMem (.cv c) (.cv x)) p0733
    have p0735 :=
      @gSyl5 syntaxFormula0108 (.classMem (.cv c) (.cv x))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.classMem (.cv c) (synCdm (.cv f))) p0714 p0734
    have p0736 :=
      @gJcad
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0108 (synWfun (.cv f)) (.classMem (.cv c) (synCdm (.cv f))) p0723
        p0735
    have p0737 := @gFunfvima (.cv a) (.cv c) (.cv f)
    have p0738 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0108
        (synWa (synWfun (.cv f)) (.classMem (.cv c) (synCdm (.cv f))))
        (.imp (.classMem (.cv c) (.cv a))
          (.classMem (synCfv (.cv f) (.cv c)) (synCima (.cv f) (.cv a))))
        p0736 p0737
    have p0739 :=
      @gMpdi
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0108 (.classMem (.cv c) (.cv a))
        (.classMem (synCfv (.cv f) (.cv c)) (synCima (.cv f) (.cv a))) p0711 p0738
    have p0740 :=
      @gJcad
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0108 (.classMem (synCfv (.cv f) (.cv c)) (.cv y))
        (.classMem (synCfv (.cv f) (.cv c)) (synCima (.cv f) (.cv a))) p0721 p0739
    have p0741 := @gEleq1 (.cv u) (synCfv (.cv f) (.cv c)) (synCima (.cv f) (.cv a))
    have p0742 :=
      @gRspcev (.classMem (.cv u) (synCima (.cv f) (.cv a)))
        (.classMem (synCfv (.cv f) (.cv c)) (synCima (.cv f) (.cv a))) u
        (synCfv (.cv f) (.cv c)) (.cv y) dv_cache_0114 dv_cache_0115 dv_cache_0116 p0741
    have p0743 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0108
        (synWa (.classMem (synCfv (.cv f) (.cv c)) (.cv y))
          (.classMem (synCfv (.cv f) (.cv c)) (synCima (.cv f) (.cv a))))
        (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a)))) p0740 p0742
    have p0744 :=
      @gExp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv c) (.cv a))
        (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a)))) p0743
    have p0745 :=
      @gIdd
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv c) (.cv a))
    have p0746 :=
      @g_pm3_2 (.classMem (.cv c) (.cv a))
        (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a))))
    have p0747 :=
      @gSyl6
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv c) (.cv a)) (.classMem (.cv c) (.cv a))
        (.imp (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a))))
          syntaxFormula0109)
        p0745 p0746
    have p0748 :=
      @gA2d
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv c) (.cv a))
        (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a))))
        syntaxFormula0109 p0747
    have p0749 :=
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.imp (.classMem (.cv c) (.cv a))
          (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a)))))
        syntaxFormula0110 p0744 p0748
    have p0750 :=
      @gAlimdv
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0110 c dv_cache_0117 p0749
    have p0751 :=
      @gSyl5
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.all c (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0)))))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.all c syntaxFormula0110) p0705 p0750
    have p0752 := @gExim (.classMem (.cv c) (.cv a)) syntaxFormula0109 c
    have p0753 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.all c syntaxFormula0110)
        (.imp (synWex c (.classMem (.cv c) (.cv a))) syntaxFormula0111) p0751 p0752
    have p0754 :=
      @gImp3a
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWex c (.classMem (.cv c) (.cv a))) syntaxFormula0111 p0753
    have p0755 :=
      @gSylan2i (synWne (.cv a) (synC0))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWex c (.classMem (.cv c) (.cv a))) syntaxFormula0111 p0704 p0754
    have p0756 := (Nominal.biimpRefl syntaxFormula0112)
    have p0757 :=
      @gSyl6ibr
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
          (synWne (.cv a) (synC0)))
        syntaxFormula0111 syntaxFormula0112 p0755 p0756
    have p0758 :=
      @gSyl5
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWa (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
          (synWne (.cv a) (synC0)))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        syntaxFormula0112 p0702 p0757
    have p0759 :=
      @gId (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a))))
    have p0760 :=
      @gA1i
        (.imp (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a))))
          (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a)))))
        (.classMem (.cv c) (.cv a)) p0759
    have p0761 :=
      @gRexlimiv (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a))))
        (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a)))) c (.cv a)
        dv_cache_0118 p0760
    have p0762 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0112
        (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a)))) p0758 p0761
    have p0763 :=
      (Nominal.biimpRefl (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a)))))
    have p0764 :=
      @gSyl6ib
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWrex u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a))))
        (synWex u syntaxFormula0113) p0762 p0763
    have p0765 := @gAbn0 syntaxFormula0113 u
    have p0766 :=
      @gSyl6ibr
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWex u syntaxFormula0113) syntaxFormula0115 p0764 p0765
    have p0767 :=
      @gSsab2 (.classMem (.cv u) (synCima (.cv f) (.cv a))) u (.cv y) dv_cache_0115
    have p0768 :=
      @gA1i syntaxFormula0116
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        p0767
    have p0769 :=
      @gA1d
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0116 syntaxFormula0115 p0768
    have p0770 := @gAncom syntaxFormula0115 syntaxFormula0116
    have p0771 := @gAbid2 u (synCima (.cv f) (.cv a)) dv_cache_0119
    have p0772 := @gVex a
    have p0773 := @gImaex (.cv f) (.cv a) p0046 p0772
    have p0774 :=
      @gEqeltri (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a))))
        (synCima (.cv f) (.cv a)) (synCvv) p0771 p0773
    have p0775 :=
      @gA1i (.classMem (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a)))) (synCvv))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        p0774
    have p0776 :=
      @gA1d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWbr (.cv r) (synCwe) (.cv y))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        p0004
    have p0777 := (Nominal.classEqRefl (synCwe))
    have p0778 :=
      @gBreqi (.cv r) (.cv y) (synCwe) (synCin (synCstrict) (synCfound)) p0777
    have p0779 := @gBrin (.cv r) (.cv y) (synCstrict) (synCfound)
    have p0780 :=
      @gBitri (synWbr (.cv r) (synCwe) (.cv y))
        (synWbr (.cv r) (synCin (synCstrict) (synCfound)) (.cv y))
        (synWa (synWbr (.cv r) (synCstrict) (.cv y)) (synWbr (.cv r) (synCfound) (.cv y)))
        p0778 p0779
    have p0781 :=
      @gSimprbi (synWbr (.cv r) (synCwe) (.cv y))
        (synWbr (.cv r) (synCstrict) (.cv y)) (synWbr (.cv r) (synCfound) (.cv y))
        p0780
    have p0782 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWbr (.cv r) (synCwe) (.cv y)) (synWbr (.cv r) (synCfound) (.cv y)) p0776
        p0781
    have p0783 := @gBrex (.cv r) (.cv y) (synCfound)
    have p0784 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWbr (.cv r) (synCfound) (.cv y))
        (synWa (.classMem (.cv r) (synCvv)) (.classMem (.cv y) (synCvv))) p0782 p0783
    have p0785 := @gAncom (.classMem (.cv r) (synCvv)) (.classMem (.cv y) (synCvv))
    have p0786 :=
      @gSyl6ib
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWa (.classMem (.cv r) (synCvv)) (.classMem (.cv y) (synCvv)))
        (synWa (.classMem (.cv y) (synCvv)) (.classMem (.cv r) (synCvv))) p0784 p0785
    have p0787 := @gSimpl (.classMem (.cv y) (synCvv)) (.classMem (.cv r) (synCvv))
    have p0788 :=
      @gSyl6
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (synWa (.classMem (.cv y) (synCvv)) (.classMem (.cv r) (synCvv)))
        (.classMem (.cv y) (synCvv)) p0786 p0787
    have p0789 :=
      @gInexg (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a)))) (.cv y) (synCvv)
        (synCvv)
    have p0790 :=
      @gEx (.classMem (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a)))) (synCvv))
        (.classMem (.cv y) (synCvv)) syntaxFormula0117 p0789
    have p0791 :=
      @gSyl9
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cv y) (synCvv))
        (.classMem (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a)))) (synCvv))
        syntaxFormula0117 p0788 p0790
    have p0792 :=
      @gSyl5
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        (.classMem (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a)))) (synCvv))
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (.imp (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
          syntaxFormula0117)
        p0775 p0791
    have p0793 :=
      @gPm243d
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0117 p0792
    have p0794 :=
      @gDfrab2 (.classMem (.cv u) (synCima (.cv f) (.cv a))) u (.cv y) dv_cache_0115
    have p0795 :=
      (Nominal.classEqRefl (synCrab u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a)))))
    have p0796 :=
      @gEqtr3i (synCrab u (.cv y) (.classMem (.cv u) (synCima (.cv f) (.cv a))))
        (synCin (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a)))) (.cv y))
        syntaxClass0114 p0794 p0795
    have p0797 :=
      @gEqcomi (synCin (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a)))) (.cv y))
        syntaxClass0114 p0796
    have p0798 :=
      @gA1i
        (.classEq syntaxClass0114
          (synCin (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a)))) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        p0797
    have p0799 :=
      @gEleq1d
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxClass0114
        (synCin (.cab u (.classMem (.cv u) (synCima (.cv f) (.cv a)))) (.cv y))
        (synCvv) p0798
    have p0800 :=
      @gBiimprd
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0118 syntaxFormula0117 p0799
    have p0801 :=
      @gSylcom
        (synWa (synWf1o (.cv f) (.cv x) (.cv y)) (synWbr (.cv r) (synCwe) (.cv y)))
        (synWa synWtru (synWa (synWss (.cv a) (.cv x)) (synWne (.cv a) (synC0))))
        syntaxFormula0117 syntaxFormula0118 p0793 p0800
    have p0802 := @gBrex (.cv r) (.cv y) (synCfound)
    have p0803 := @gBreq (.cv w) (.cv v) (.cv d) (.cv r)
    have p0804 :=
      @gImbi1d (.classEq (.cv d) (.cv r)) (synWbr (.cv w) (.cv d) (.cv v))
        (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v) p0803
    have p0805 :=
      @gRexralbidv (.classEq (.cv d) (.cv r))
        (.imp (synWbr (.cv w) (.cv d) (.cv v)) (.objEq w v))
        (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)) v w (.cv b) (.cv b)
        dv_cache_0120 dv_cache_0121 p0804
    have p0806 :=
      @gImbi2d (.classEq (.cv d) (.cv r))
        (synWrex v (.cv b)
          (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv d) (.cv v)) (.objEq w v))))
        (synWrex v (.cv b)
          (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))
        (synWa (synWss (.cv b) (.cv c)) (synWne (.cv b) (synC0))) p0805
    have p0807 :=
      @gAlbidv (.classEq (.cv d) (.cv r))
        (.imp (synWa (synWss (.cv b) (.cv c)) (synWne (.cv b) (synC0))) (synWrex v (.cv b)
            (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv d) (.cv v)) (.objEq w v)))))
        (.imp (synWa (synWss (.cv b) (.cv c)) (synWne (.cv b) (synC0))) (synWrex v (.cv b)
            (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))))
        b dv_cache_0122 p0806
    have p0808 := @gSseq2 (.cv c) (.cv y) (.cv b)
    have p0809 :=
      @gAnbi1d (.classEq (.cv c) (.cv y)) (synWss (.cv b) (.cv c))
        (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0)) p0808
    have p0810 :=
      @gImbi1d (.classEq (.cv c) (.cv y))
        (synWa (synWss (.cv b) (.cv c)) (synWne (.cv b) (synC0)))
        (synWa (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0)))
        (synWrex v (.cv b)
          (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v))))
        p0809
    have p0811 :=
      @gAlbidv (.classEq (.cv c) (.cv y))
        (.imp (synWa (synWss (.cv b) (.cv c)) (synWne (.cv b) (synC0))) (synWrex v (.cv b)
            (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))))
        (.imp (synWa (synWss (.cv b) (.cv y)) (synWne (.cv b) (synC0))) (synWrex v (.cv b)
            (synWral w (.cv b) (.imp (synWbr (.cv w) (.cv r) (.cv v)) (.objEq w v)))))
        b dv_cache_0123 p0810
    have p0812 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFound b w v d c
        dv_cache_0013 dv_cache_0006 dv_cache_0124 dv_cache_0125 dv_cache_0005
        dv_cache_0126 dv_cache_0127 dv_cache_0128 dv_cache_0129 dv_cache_0130
    exact
      continuation p0607 p0615 p0687 p0690 p0693 p0694 p0696 p0709 p0766 p0769 p0770 p0776
        p0777 p0780 p0782 p0801 p0802 p0807 p0811 p0812

end NFChoice.DirectNominalPrf.WPPReplay

end
