/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk016Compact001Block011

/-! NF weak partition development: NominalWPPReplayChunk016Compact001Part051. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_pwpullwesetimpndv_stage6 (x : Var) (y : Var) (f : Var) (r : Var)
    (p0000 : _) (p0115 : _) (p0117 : _) (p0440 : _) (p0607 : _) (p0687 : _) (p0690 : _)
    (p0693 : _) (p0694 : _) (p0696 : _) (p0777 : _) (p1293 : _) (p1294 : _) (p1299 : _)
    {Result : Type} (continuation : _ → Result) :=
  show Result from
    by
    let proofSupport : Finset Var :=
      ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ f } : Finset Var) ∪
        ({ r } : Finset Var)
    let a : Var := freshVar proofSupport 0
    let b : Var := freshVar proofSupport 1
    let c : Var := freshVar proofSupport 2
    let d : Var := freshVar proofSupport 3
    let z : Var := freshVar proofSupport 5
    let e : Var := freshVar proofSupport 6
    let h : Var := freshVar proofSupport 7
    let u : Var := freshVar proofSupport 8
    let v : Var := freshVar proofSupport 9
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
    have fresh_e_ne_x : e ≠ x := by
      intro h
      exact
        fresh_e
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
    have fresh_e_ne_f : e ≠ f := by
      intro h
      exact
        fresh_e
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_e_ne_r : e ≠ r := by
      intro h
      exact fresh_e (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_u : u ∉ proofSupport :=
      by
      change freshVar proofSupport 8 ∉ proofSupport
      exact freshVar_not_mem proofSupport 8
    have fresh_u_ne_x : u ≠ x := by
      intro h
      exact
        fresh_u
          (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
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
    have fresh_u_ne_r : u ≠ r := by
      intro h
      exact fresh_u (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
    have fresh_v : v ∉ proofSupport :=
      by
      change freshVar proofSupport 9 ∉ proofSupport
      exact freshVar_not_mem proofSupport 9
    have fresh_v_ne_f : v ≠ f := by
      intro h
      exact
        fresh_v
          (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
    have fresh_v_ne_r : v ≠ r := by
      intro h
      exact fresh_v (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
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
    have fresh_a_ne_z : a ≠ z :=
      by
      change freshVar proofSupport 0 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
    have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
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
    have fresh_b_ne_z : b ≠ z :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 5
      exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
    have fresh_b_ne_e : b ≠ e :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
    have fresh_e_ne_b : e ≠ b := Ne.symm fresh_b_ne_e
    have fresh_b_ne_u : b ≠ u :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 8
      exact freshVar_injective proofSupport (i := 1) (j := 8) (by decide)
    have fresh_u_ne_b : u ≠ b := Ne.symm fresh_b_ne_u
    have fresh_b_ne_v : b ≠ v :=
      by
      change freshVar proofSupport 1 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 1) (j := 9) (by decide)
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
    have fresh_d_ne_e : d ≠ e :=
      by
      change freshVar proofSupport 3 ≠ freshVar proofSupport 6
      exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
    have fresh_e_ne_d : e ≠ d := Ne.symm fresh_d_ne_e
    have fresh_z_ne_u : z ≠ u :=
      by
      change freshVar proofSupport 5 ≠ freshVar proofSupport 8
      exact freshVar_injective proofSupport (i := 5) (j := 8) (by decide)
    have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
    have fresh_z_ne_v : z ≠ v :=
      by
      change freshVar proofSupport 5 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 5) (j := 9) (by decide)
    have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
    have fresh_u_ne_v : u ≠ v :=
      by
      change freshVar proofSupport 8 ≠ freshVar proofSupport 9
      exact freshVar_injective proofSupport (i := 8) (j := 9) (by decide)
    have fresh_v_ne_u : v ≠ u := Ne.symm fresh_u_ne_v
    have dv_cache_0004 : d ≠ c := by exact (show d ≠ c from (by exact fresh_d_ne_c))
    have dv_cache_0005 : d ≠ b := by exact (show d ≠ b from (by exact fresh_d_ne_b))
    have dv_cache_0006 : c ≠ b := by exact (show c ≠ b from (by exact fresh_c_ne_b))
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
    have dv_cache_0032 : b ≠ c := by exact (show b ≠ c from (by exact fresh_b_ne_c))
    have dv_cache_0054 : d ≠ e := by exact (show d ≠ e from (by exact fresh_d_ne_e))
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
    have dv_cache_0096 : e ≠ c := by exact (show e ≠ c from (by exact fresh_e_ne_c))
    have dv_cache_0097 : e ≠ d := by exact (show e ≠ d from (by exact fresh_e_ne_d))
    have dv_cache_0112 : c ∉ ((Class.cv a)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_a, not_false_eq_true])
    have dv_cache_0125 : c ≠ v := by exact (show c ≠ v from (by exact fresh_c_ne_v))
    have dv_cache_0129 : b ≠ v := by exact (show b ≠ v from (by exact fresh_b_ne_v))
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
    have dv_cache_0173 : z ∉ ((Class.cv a)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_z_ne_a, not_false_eq_true])
    have dv_cache_0183 :
      c ∉
        ((syn_cdif (syn_cpwpull (.cv f) (.cv r))
            (syn_ccnv (syn_cpwpull (.cv f) (.cv r))))).fv :=
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
    have dv_cache_0189 : a ∉ ((Wff.classEq (.cv b) (.cv x))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_a_ne_b, fresh_a_ne_x, or_false,
            not_false_eq_true])
    have dv_cache_0190 : a ≠ v := by exact (show a ≠ v from (by exact fresh_a_ne_v))
    have dv_cache_0191 : v ≠ z := by exact (show v ≠ z from (by exact fresh_v_ne_z))
    have dv_cache_0192 :
      b ∉
        ((syn_cdif (syn_cpwpull (.cv f) (.cv r))
            (syn_ccnv (syn_cpwpull (.cv f) (.cv r))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_f, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0193 :
      c ∉
        ((Wff.all a (.imp (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
              (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp (syn_wbr (.cv v)
                      (syn_cdif (syn_cpwpull (.cv f) (.cv r))
                        (syn_ccnv (syn_cpwpull (.cv f) (.cv r)))) (.cv z))
                    (.objEq v z))))))).fv :=
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
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_x,
            fresh_c_ne_v, fresh_c_ne_z, fresh_c_ne_f, fresh_c_ne_r,
            compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
    have dv_cache_0194 :
      b ∉
        ((Wff.all a (.imp (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
              (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp (syn_wbr (.cv v)
                      (syn_cdif (syn_cpwpull (.cv f) (.cv r))
                        (syn_ccnv (syn_cpwpull (.cv f) (.cv r)))) (.cv z))
                    (.objEq v z))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
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
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_x,
            fresh_b_ne_v, fresh_b_ne_z, fresh_b_ne_f, fresh_b_ne_r,
            compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
    have dv_cache_0195 : v ∉ ((Class.cv a)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_v_ne_a, not_false_eq_true])
    have dv_cache_0196 : v ∉ ((Class.cv u)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_v_ne_u, not_false_eq_true])
    have dv_cache_0197 : z ∉ ((Class.cv u)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_z_ne_u, not_false_eq_true])
    have dv_cache_0198 : a ∉ ((Class.cv u)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_a_ne_u, not_false_eq_true])
    have dv_cache_0199 :
      a ∉
        ((Wff.imp (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))
            (syn_wrex z (.cv u) (syn_wral v (.cv u) (.imp (syn_wbr (.cv v)
                    (syn_cdif (syn_cpwpull (.cv f) (.cv r))
                      (syn_ccnv (syn_cpwpull (.cv f) (.cv r)))) (.cv z)) (.objEq v z)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
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
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_a_ne_u, fresh_a_ne_x,
            fresh_a_ne_v, fresh_a_ne_z, fresh_a_ne_f, fresh_a_ne_r,
            compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
    have dv_cache_0200 :
      z ∉
        ((syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
            Finset.mem_singleton, fresh_z_ne_u, fresh_z_ne_x, compact_fv_not_mem_empty,
            or_false, not_false_eq_true])
    have dv_cache_0201 :
      v ∉
        ((Wff.imp (syn_wbr (.cv a) (syn_cdif (syn_cpwpull (.cv f) (.cv r))
                (syn_ccnv (syn_cpwpull (.cv f) (.cv r)))) (.cv z))
            (.classEq (.cv a) (.cv z)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_singleton, fresh_v_ne_a, fresh_v_ne_z, fresh_v_ne_f, fresh_v_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0202 : b ∉ ((Wff.classEq (.cv d) (syn_cpwpull (.cv f) (.cv r)))).fv :=
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
            Finset.mem_singleton, fresh_b_ne_d, fresh_b_ne_f, fresh_b_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0203 : c ∉ ((Wff.classEq (.cv d) (syn_cpwpull (.cv f) (.cv r)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_d, fresh_c_ne_f, fresh_c_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0204 : e ∉ ((syn_cpwpull (.cv f) (.cv r))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_e_ne_f, fresh_e_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0205 : e ∉ ((Class.cv x)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : e ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_e_ne_x, not_false_eq_true])
    have dv_cache_0206 :
      d ∉
        ((syn_wral b (.cv x) (syn_wral c (.cv x) (.imp
                (syn_wa (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv c))
                  (syn_wbr (.cv c) (syn_cpwpull (.cv f) (.cv r)) (.cv b)))
                (.objEq b c))))).fv :=
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
            Finset.mem_insert, Finset.mem_singleton, fresh_d_ne_x, fresh_d_ne_b,
            fresh_d_ne_c, fresh_d_ne_f, fresh_d_ne_r, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0207 :
      e ∉
        ((syn_wral b (.cv x) (syn_wral c (.cv x) (.imp
                (syn_wa (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv c))
                  (syn_wbr (.cv c) (syn_cpwpull (.cv f) (.cv r)) (.cv b)))
                (.objEq b c))))).fv :=
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
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_union, Finset.mem_erase,
            Finset.mem_insert, Finset.mem_singleton, fresh_e_ne_x, fresh_e_ne_b,
            fresh_e_ne_c, fresh_e_ne_f, fresh_e_ne_r, or_false, and_false,
            not_false_eq_true])
    have dv_cache_0208 : b ∉ ((Class.cv a)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_b_ne_a, not_false_eq_true])
    have dv_cache_0209 : c ∉ ((Class.cv z)).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
            fresh_c_ne_z, not_false_eq_true])
    have dv_cache_0210 :
      b ∉
        ((Wff.imp (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv c))
              (syn_wbr (.cv c) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
            (.classEq (.cv a) (.cv c)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_c, fresh_b_ne_f, fresh_b_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0211 :
      c ∉
        ((Wff.imp (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
              (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
            (.classEq (.cv a) (.cv z)))).fv :=
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
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_z, fresh_c_ne_f, fresh_c_ne_r,
            or_false, not_false_eq_true])
    have dv_cache_0212 :
      a ∉
        ((syn_wa (syn_wa (syn_wa syn_wtru
                (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
              (.classMem (.cv z) (.cv u))) (syn_wral v (.cv u) (.imp (syn_wbr (.cv v)
                  (syn_cdif (syn_cpwpull (.cv f) (.cv r))
                    (syn_ccnv (syn_cpwpull (.cv f) (.cv r)))) (.cv z))
                (.classEq (.cv v) (.cv z)))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
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
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
            NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_u, fresh_a_ne_x,
            fresh_a_ne_z, fresh_a_ne_v, fresh_a_ne_f, fresh_a_ne_r,
            compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
    have dv_cache_0213 :
      u ∉
        ((syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
            NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cwe, Finset.mem_union,
            Finset.mem_singleton, fresh_u_ne_x, fresh_u_ne_y, fresh_u_ne_f, fresh_u_ne_r,
            compact_fv_not_mem_empty, or_false, not_false_eq_true])
    have dv_cache_0214 : u ∉ (syn_wtru).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wtru,
            compact_fv_not_mem_empty, not_false_eq_true])
    have dv_cache_0215 : u ∉ ((Wff.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv,
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull, Finset.mem_union,
            Finset.mem_singleton, fresh_u_ne_c, fresh_u_ne_f, fresh_u_ne_r, or_false,
            not_false_eq_true])
    have dv_cache_0216 : u ∉ ((Wff.classEq (.cv b) (.cv x))).fv := by
      exact
        (by
          have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
            by
            intro hmem
            cases hmem
          simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
            NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
            Finset.mem_singleton, fresh_u_ne_b, fresh_u_ne_x, or_false,
            not_false_eq_true])
    have dv_cache_0217 : b ≠ u := by exact (show b ≠ u from (by exact fresh_b_ne_u))
    have dv_cache_0218 : c ≠ u := by exact (show c ≠ u from (by exact fresh_c_ne_u))
    have dv_cache_0219 : u ≠ a := by exact (show u ≠ a from (by exact fresh_u_ne_a))
    have dv_cache_0220 : u ≠ z := by exact (show u ≠ z from (by exact fresh_u_ne_z))
    have dv_cache_0221 :
      c ∉
        ((Wff.all u (.imp (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))
              (syn_wrex z (.cv u) (syn_wral a (.cv u)
                  (.imp (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
                    (.classEq (.cv a) (.cv z)))))))).fv :=
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
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_c_ne_u, fresh_c_ne_x,
            fresh_c_ne_a, fresh_c_ne_z, fresh_c_ne_f, fresh_c_ne_r,
            compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
    have dv_cache_0222 :
      b ∉
        ((Wff.all u (.imp (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))
              (syn_wrex z (.cv u) (syn_wral a (.cv u)
                  (.imp (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
                    (.classEq (.cv a) (.cv z)))))))).fv :=
      by
      exact
        (by
          have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
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
            NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cpwpull,
            NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
            Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_u, fresh_b_ne_x,
            fresh_b_ne_a, fresh_b_ne_z, fresh_b_ne_f, fresh_b_ne_r,
            compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
    let syntaxClass0183 : Class :=
      (syn_cdif (syn_cpwpull (.cv f) (.cv r)) (syn_ccnv (syn_cpwpull (.cv f) (.cv r))))
    let syntaxFormula0239 : Wff := (.classMem syntaxClass0183 (syn_cvv))
    let syntaxFormula0247 : Wff := (syn_wbr syntaxClass0183 (syn_cfound) (.cv x))
    let syntaxFormula0249 : Wff := (syn_wbr (.cv v) syntaxClass0183 (.cv z))
    let syntaxFormula0250 : Wff := (.imp syntaxFormula0249 (.classEq (.cv v) (.cv z)))
    let syntaxFormula0251 : Wff := (syn_wral v (.cv a) syntaxFormula0250)
    let syntaxFormula0252 : Wff := (syn_wrex z (.cv a) syntaxFormula0251)
    let syntaxFormula0253 : Wff :=
      (.imp (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0))) syntaxFormula0252)
    let syntaxFormula0254 : Wff := (.all a syntaxFormula0253)
    let syntaxFormula0255 : Wff := (syn_wral v (.cv u) syntaxFormula0250)
    let syntaxFormula0256 : Wff := (syn_wrex z (.cv u) syntaxFormula0255)
    let syntaxFormula0257 : Wff :=
      (.imp (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))) syntaxFormula0256)
    let syntaxFormula0258 : Wff := (.imp (syn_wss (.cv u) (.cv x)) syntaxFormula0256)
    let syntaxFormula0259 : Wff := (.imp (syn_wne (.cv u) (syn_c0)) syntaxFormula0258)
    let syntaxFormula0260 : Wff := (.imp (syn_wne (.cv u) (syn_c0)) syntaxFormula0256)
    let syntaxFormula0261 : Wff :=
      (.imp (.imp (syn_wne (.cv u) (syn_c0)) (syn_wss (.cv u) (.cv x))) syntaxFormula0260)
    let syntaxFormula0262 : Wff :=
      (syn_wa (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (.classMem (.cv z) (.cv u)))
    let syntaxFormula0263 : Wff := (syn_wa syntaxFormula0262 syntaxFormula0255)
    let syntaxFormula0264 : Wff := (syn_wa syntaxFormula0263 (.classMem (.cv a) (.cv u)))
    let syntaxFormula0265 : Wff :=
      (syn_wa syntaxFormula0264 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)))
    let syntaxFormula0266 : Wff :=
      (syn_wa syntaxFormula0265 (.neg (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))))
    let syntaxFormula0267 : Wff := (syn_wbr (.cv a) syntaxClass0183 (.cv z))
    let syntaxFormula0268 : Wff := (.imp syntaxFormula0267 (.classEq (.cv a) (.cv z)))
    let syntaxFormula0269 : Wff :=
      (syn_wa syntaxFormula0265 (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
    let syntaxFormula0270 : Wff :=
      (syn_wa (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv c))
        (syn_wbr (.cv c) (syn_cpwpull (.cv f) (.cv r)) (.cv b)))
    let syntaxFormula0271 : Wff := (.imp syntaxFormula0270 (.classEq (.cv b) (.cv c)))
    let syntaxFormula0272 : Wff := (syn_wral c (.cv x) syntaxFormula0271)
    let syntaxFormula0273 : Wff := (syn_wral b (.cv x) syntaxFormula0272)
    let syntaxFormula0274 : Wff :=
      (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv c))
        (syn_wbr (.cv c) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
    let syntaxFormula0275 : Wff :=
      (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
        (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
    let syntaxFormula0276 : Wff := (.imp syntaxFormula0275 (.classEq (.cv a) (.cv z)))
    let syntaxFormula0277 : Wff :=
      (.imp (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) (.classEq (.cv a) (.cv z)))
    let syntaxFormula0278 : Wff :=
      (.imp (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) (.classEq (.cv a) (.cv z)))
    let syntaxFormula0279 : Wff := (syn_wral a (.cv u) syntaxFormula0277)
    let syntaxFormula0280 : Wff := (.imp syntaxFormula0255 syntaxFormula0279)
    let syntaxFormula0281 : Wff := (.imp (.classMem (.cv z) (.cv u)) syntaxFormula0280)
    let syntaxFormula0282 : Wff := (.all z syntaxFormula0281)
    let syntaxFormula0283 : Wff := (syn_wral z (.cv u) syntaxFormula0280)
    let syntaxFormula0284 : Wff := (syn_wrex z (.cv u) syntaxFormula0279)
    let syntaxFormula0285 : Wff :=
      (.imp (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))) syntaxFormula0284)
    let syntaxFormula0286 : Wff :=
      (syn_wral a (.cv u) (.imp (syn_wbr (.cv a) (.cv c) (.cv z)) (.classEq (.cv a) (.cv z))))
    let syntaxFormula0287 : Wff := (syn_wrex z (.cv u) syntaxFormula0286)
    let syntaxFormula0288 : Wff :=
      (.imp (syn_wa (syn_wss (.cv u) (.cv b)) (syn_wne (.cv u) (syn_c0))) syntaxFormula0287)
    let syntaxFormula0289 : Wff :=
      (.imp (syn_wa (syn_wss (.cv u) (.cv b)) (syn_wne (.cv u) (syn_c0))) syntaxFormula0284)
    let syntaxFormula0290 : Wff := (.all u syntaxFormula0288)
    let syntaxFormula0291 : Wff := (.all u syntaxFormula0285)
    have p1300 := @g_sseq2 (.cv b) (.cv x) (.cv a)
    have p1301 :=
      @g_anbi1d (.classEq (.cv b) (.cv x)) (syn_wss (.cv a) (.cv b))
        (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)) p1300
    have p1302 :=
      @g_imbi1d (.classEq (.cv b) (.cv x))
        (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wne (.cv a) (syn_c0)))
        (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
        (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp syntaxFormula0249 (.objEq v z))))
        p1301
    have p1303 :=
      @g_albidv (.classEq (.cv b) (.cv x))
        (.imp (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wne (.cv a) (syn_c0)))
          (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp syntaxFormula0249 (.objEq v z)))))
        (.imp (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
          (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp syntaxFormula0249 (.objEq v z)))))
        a dv_cache_0189 p1302
    have p1304 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_found a v z c b
        dv_cache_0032 dv_cache_0025 dv_cache_0129 dv_cache_0086 dv_cache_0024
        dv_cache_0125 dv_cache_0084 dv_cache_0190 dv_cache_0085 dv_cache_0191
    have p1305 :=
      @g_brabg
        (.all a (.imp (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wne (.cv a) (syn_c0)))
            (syn_wrex z (.cv a) (syn_wral v (.cv a)
                (.imp (syn_wbr (.cv v) (.cv c) (.cv z)) (.objEq v z))))))
        (.all a (.imp (syn_wa (syn_wss (.cv a) (.cv b)) (syn_wne (.cv a) (syn_c0)))
            (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp syntaxFormula0249 (.objEq v z))))))
        (.all a (.imp (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
            (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp syntaxFormula0249 (.objEq v z))))))
        c b syntaxClass0183 (.cv x) (syn_cvv) (syn_cvv) (syn_cfound) dv_cache_0183
        dv_cache_0192 dv_cache_0029 dv_cache_0028 dv_cache_0193 dv_cache_0194
        dv_cache_0006 p1299 p1303 p1304
    have p1306 :=
      @g_syl syntaxFormula0247 (syn_wa syntaxFormula0239 (.classMem (.cv x) (syn_cvv)))
        (syn_wb syntaxFormula0247 (.all a
            (.imp (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
              (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp syntaxFormula0249 (.objEq v z)))))))
        p1294 p1305
    have p1307 :=
      @g_ibi syntaxFormula0247
        (.all a (.imp (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
            (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp syntaxFormula0249 (.objEq v z))))))
        p1306
    have p1308_e01_recanon : Nominal.NPrf (.imp syntaxFormula0247 syntaxFormula0254) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_wa, syn_wrex, syn_wex]
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
        p1307
    have p1308 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        syntaxFormula0247 syntaxFormula0254 p1293 p1308_e01_recanon
    have p1309 := @g_sseq1 (.cv a) (.cv u) (.cv x)
    have p1310 := @g_neeq1 (.cv a) (.cv u) (syn_c0)
    have p1311 :=
      @g_anbi12d (.classEq (.cv a) (.cv u)) (syn_wss (.cv a) (.cv x))
        (syn_wss (.cv u) (.cv x)) (syn_wne (.cv a) (syn_c0)) (syn_wne (.cv u) (syn_c0))
        p1309 p1310
    have p1312 :=
      @g_raleq (.imp syntaxFormula0249 (.objEq v z)) v (.cv a) (.cv u) dv_cache_0195
        dv_cache_0196
    have p1313 :=
      @g_rexeqbi1dv (syn_wral v (.cv a) (.imp syntaxFormula0249 (.objEq v z)))
        (syn_wral v (.cv u) (.imp syntaxFormula0249 (.objEq v z))) z (.cv a) (.cv u)
        dv_cache_0173 dv_cache_0197 p1312
    have p1314 :=
      @g_imbi12d (.classEq (.cv a) (.cv u))
        (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
        (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))
        (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp syntaxFormula0249 (.objEq v z))))
        (syn_wrex z (.cv u) (syn_wral v (.cv u) (.imp syntaxFormula0249 (.objEq v z))))
        p1311 p1313
    have p1315 :=
      @g_spcgv
        (.imp (syn_wa (syn_wss (.cv a) (.cv x)) (syn_wne (.cv a) (syn_c0)))
          (syn_wrex z (.cv a) (syn_wral v (.cv a) (.imp syntaxFormula0249 (.objEq v z)))))
        (.imp (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))
          (syn_wrex z (.cv u) (syn_wral v (.cv u) (.imp syntaxFormula0249 (.objEq v z)))))
        a (.cv u) (syn_cvv) dv_cache_0198 dv_cache_0199 p1314
    have p1316_e01_recanon :
      Nominal.NPrf
        (.imp (.classMem (.cv u) (syn_cvv)) (.imp syntaxFormula0254 syntaxFormula0257)) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_cvv, syn_wa, syn_wss, syn_cin, syn_ccompl, syn_cnin, syn_wnan,
            syn_wne, syn_c0, syn_cdif, syn_wrex, syn_wex, syn_wral]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
        p1315
    have p1316 :=
      @g_syl9
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        syntaxFormula0254 (.classMem (.cv u) (syn_cvv)) syntaxFormula0257 p1308
        p1316_e01_recanon
    have p1317 :=
      @g_syl5
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (.classMem (.cv u) (syn_cvv))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (.imp (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
          syntaxFormula0257)
        p0696 p1316
    have p1318 :=
      @g_pm2_43d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        syntaxFormula0257 p1317
    have p1319 :=
      @g_syl7bi (syn_wa (syn_wne (.cv u) (syn_c0)) (syn_wss (.cv u) (.cv x)))
        (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        syntaxFormula0256 p0694 p1318
    have p1320 :=
      @g_exp4a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (syn_wne (.cv u) (syn_c0)) (syn_wss (.cv u) (.cv x)) syntaxFormula0256 p1319
    have p1321 :=
      Nominal.ax2 (syn_wne (.cv u) (syn_c0)) (syn_wss (.cv u) (.cv x))
        (syn_wrex z (.cv u) (syn_wral v (.cv u) (.imp syntaxFormula0249 (.objEq v z))))
    have p1322_e01_recanon : Nominal.NPrf (.imp syntaxFormula0259 syntaxFormula0261) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_wne, syn_c0, syn_cdif, syn_cin, syn_ccompl, syn_cnin, syn_wnan,
            syn_wa, syn_cvv, syn_wss, syn_wrex, syn_wex, syn_wral]
          simp (config :=
            { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
        p1321
    have p1322 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        syntaxFormula0259 syntaxFormula0261 p1320 p1322_e01_recanon
    have p1323 :=
      @g_mpdi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (.imp (syn_wne (.cv u) (syn_c0)) (syn_wss (.cv u) (.cv x))) syntaxFormula0260
        p0693 p1322
    have p1324 :=
      @g_mpdi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (syn_wne (.cv u) (syn_c0)) syntaxFormula0256 p0690 p1323
    have p1325 :=
      @g_nfv
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))) z
        dv_cache_0200
    have p1326 :=
      @g_nfri
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))) z
        p1325
    have p1327 :=
      @g_simpl syntaxFormula0265
        (.neg (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
    have p1328 :=
      @g_simpr syntaxFormula0264 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
    have p1329 :=
      @g_syl syntaxFormula0266 syntaxFormula0265
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) p1327 p1328
    have p1330 :=
      @g_simpr syntaxFormula0265
        (.neg (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
    have p1331 := @g_brcnv (.cv a) (.cv z) (syn_cpwpull (.cv f) (.cv r))
    have p1332 :=
      @g_notbii (syn_wbr (.cv a) (syn_ccnv (syn_cpwpull (.cv f) (.cv r))) (.cv z))
        (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p1331
    have p1333 :=
      @g_biimpri (.neg (syn_wbr (.cv a) (syn_ccnv (syn_cpwpull (.cv f) (.cv r))) (.cv z)))
        (.neg (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))) p1332
    have p1334 :=
      @g_syl syntaxFormula0266
        (.neg (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
        (.neg (syn_wbr (.cv a) (syn_ccnv (syn_cpwpull (.cv f) (.cv r))) (.cv z))) p1330
        p1333
    have p1335 :=
      @g_jca syntaxFormula0266 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
        (.neg (syn_wbr (.cv a) (syn_ccnv (syn_cpwpull (.cv f) (.cv r))) (.cv z))) p1329
        p1334
    have p1336 :=
      @g_brdif (.cv a) (.cv z) (syn_cpwpull (.cv f) (.cv r))
        (syn_ccnv (syn_cpwpull (.cv f) (.cv r)))
    have p1337 :=
      @g_biimpri syntaxFormula0267
        (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
          (.neg (syn_wbr (.cv a) (syn_ccnv (syn_cpwpull (.cv f) (.cv r))) (.cv z))))
        p1336
    have p1338 :=
      @g_syl syntaxFormula0266
        (syn_wa (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
          (.neg (syn_wbr (.cv a) (syn_ccnv (syn_cpwpull (.cv f) (.cv r))) (.cv z))))
        syntaxFormula0267 p1335 p1337
    have p1340 :=
      @g_simpl syntaxFormula0264 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
    have p1341 := @g_simpl syntaxFormula0263 (.classMem (.cv a) (.cv u))
    have p1342 := @g_simpr syntaxFormula0262 syntaxFormula0255
    have p1343 := @g_syl syntaxFormula0264 syntaxFormula0263 syntaxFormula0255 p1341 p1342
    have p1344 := @g_simpr syntaxFormula0263 (.classMem (.cv a) (.cv u))
    have p1345 :=
      @g_jca syntaxFormula0264 syntaxFormula0255 (.classMem (.cv a) (.cv u)) p1343 p1344
    have p1346 := @g_breq1 (.cv v) (.cv a) (.cv z) syntaxClass0183
    have p1347 := @g_eqeq1 (.cv v) (.cv a) (.cv z)
    have p1348 :=
      @g_imbi12d (.classEq (.cv v) (.cv a)) syntaxFormula0249 syntaxFormula0267
        (.classEq (.cv v) (.cv z)) (.classEq (.cv a) (.cv z)) p1346 p1347
    have p1349 :=
      @g_rspccva syntaxFormula0250 syntaxFormula0268 v (.cv a) (.cv u) dv_cache_0195
        dv_cache_0196 dv_cache_0201 p1348
    have p1350 :=
      @g_syl syntaxFormula0264 (syn_wa syntaxFormula0255 (.classMem (.cv a) (.cv u)))
        syntaxFormula0268 p1345 p1349
    have p1351 := @g_syl syntaxFormula0265 syntaxFormula0264 syntaxFormula0268 p1340 p1350
    have p1352 := @g_syl syntaxFormula0266 syntaxFormula0265 syntaxFormula0268 p1327 p1351
    have p1353 :=
      @g_mpd syntaxFormula0266 syntaxFormula0267 (.classEq (.cv a) (.cv z)) p1338 p1352
    have p1354 :=
      @g_ex syntaxFormula0265
        (.neg (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
        (.classEq (.cv a) (.cv z)) p1353
    have p1355 :=
      @g_con1d syntaxFormula0265 (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (.classEq (.cv a) (.cv z)) p1354
    have p1356 :=
      @g_simpr syntaxFormula0265 (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
    have p1357 :=
      @g_simpl syntaxFormula0265 (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
    have p1359 :=
      @g_syl syntaxFormula0269 syntaxFormula0265
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) p1357 p1328
    have p1360 :=
      @g_a1d syntaxFormula0269 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
        (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p1359
    have p1361 :=
      @g_ancom (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
    have p1362 :=
      @g_a1d
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x)) syntaxFormula0269
        p0607
    have p1363 := @g_brex (syn_cpwpull (.cv f) (.cv r)) (.cv x) (syn_cantisym)
    have p1364 := @g_breq (.cv b) (.cv c) (.cv d) (syn_cpwpull (.cv f) (.cv r))
    have p1365 := @g_breq (.cv c) (.cv b) (.cv d) (syn_cpwpull (.cv f) (.cv r))
    have p1366 :=
      @g_anbi12d (.classEq (.cv d) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wbr (.cv b) (.cv d) (.cv c))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv c))
        (syn_wbr (.cv c) (.cv d) (.cv b))
        (syn_wbr (.cv c) (syn_cpwpull (.cv f) (.cv r)) (.cv b)) p1364 p1365
    have p1367 :=
      @g_imbi1d (.classEq (.cv d) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wa (syn_wbr (.cv b) (.cv d) (.cv c)) (syn_wbr (.cv c) (.cv d) (.cv b)))
        syntaxFormula0270 (.objEq b c) p1366
    have p1368 :=
      @g_n_2ralbidv (.classEq (.cv d) (syn_cpwpull (.cv f) (.cv r)))
        (.imp (syn_wa (syn_wbr (.cv b) (.cv d) (.cv c)) (syn_wbr (.cv c) (.cv d) (.cv b)))
          (.objEq b c))
        (.imp syntaxFormula0270 (.objEq b c)) b c (.cv e) (.cv e) dv_cache_0202
        dv_cache_0203 p1367
    have p1369 :=
      @g_raleq (.imp syntaxFormula0270 (.objEq b c)) c (.cv e) (.cv x) dv_cache_0146
        dv_cache_0029
    have p1370 :=
      @g_raleqbi1dv (syn_wral c (.cv e) (.imp syntaxFormula0270 (.objEq b c)))
        (syn_wral c (.cv x) (.imp syntaxFormula0270 (.objEq b c))) b (.cv e) (.cv x)
        dv_cache_0147 dv_cache_0028 p1369
    have p1371 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_antisym b c d e
        dv_cache_0097 dv_cache_0148 dv_cache_0096 dv_cache_0005 dv_cache_0004
        dv_cache_0032
    have p1372 :=
      @g_brabg
        (syn_wral b (.cv e) (syn_wral c (.cv e) (.imp
              (syn_wa (syn_wbr (.cv b) (.cv d) (.cv c)) (syn_wbr (.cv c) (.cv d) (.cv b)))
              (.objEq b c))))
        (syn_wral b (.cv e) (syn_wral c (.cv e) (.imp syntaxFormula0270 (.objEq b c))))
        (syn_wral b (.cv x) (syn_wral c (.cv x) (.imp syntaxFormula0270 (.objEq b c)))) d
        e (syn_cpwpull (.cv f) (.cv r)) (.cv x) (syn_cvv) (syn_cvv) (syn_cantisym)
        dv_cache_0087 dv_cache_0204 dv_cache_0088 dv_cache_0205 dv_cache_0206
        dv_cache_0207 dv_cache_0054 p1368 p1370 p1371
    have p1373 :=
      @g_syl (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x))
        (syn_wa (.classMem (syn_cpwpull (.cv f) (.cv r)) (syn_cvv))
          (.classMem (.cv x) (syn_cvv)))
        (syn_wb (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x))
          (syn_wral b (.cv x) (syn_wral c (.cv x) (.imp syntaxFormula0270 (.objEq b c)))))
        p1363 p1372
    have p1374 :=
      @g_ibi (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x))
        (syn_wral b (.cv x) (syn_wral c (.cv x) (.imp syntaxFormula0270 (.objEq b c))))
        p1373
    have p1375_e01_recanon :
      Nominal.NPrf
        (.imp (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x))
          syntaxFormula0273) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_wbr, syn_cop, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl,
            syn_wrex, syn_wex, syn_cphi, syn_cpwpull, syn_ccom, syn_copab, syn_cantisym,
            syn_wral]
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
        p1374
    have p1375 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0269 (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cantisym) (.cv x))
        syntaxFormula0273 p1362 p1375_e01_recanon
    have p1376 :=
      @g_simpl syntaxFormula0265 (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
    have p1377 :=
      @g_simpl syntaxFormula0264 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
    have p1378 := @g_simpl syntaxFormula0263 (.classMem (.cv a) (.cv u))
    have p1379 := @g_syl syntaxFormula0265 syntaxFormula0264 syntaxFormula0263 p1377 p1378
    have p1380 := @g_simpl syntaxFormula0262 syntaxFormula0255
    have p1381 := @g_syl syntaxFormula0265 syntaxFormula0263 syntaxFormula0262 p1379 p1380
    have p1382 :=
      @g_simpl
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (.classMem (.cv z) (.cv u))
    have p1383 :=
      @g_syl syntaxFormula0265 syntaxFormula0262
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        p1381 p1382
    have p1384 :=
      @g_simpr syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))
    have p1385 :=
      @g_simpld
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)) p1384
    have p1386 :=
      @g_syl syntaxFormula0265
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (syn_wss (.cv u) (.cv x)) p1383 p1385
    have p1387 :=
      @g_simpl syntaxFormula0264 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
    have p1388 := @g_simpr syntaxFormula0263 (.classMem (.cv a) (.cv u))
    have p1389 :=
      @g_syl syntaxFormula0265 syntaxFormula0264 (.classMem (.cv a) (.cv u)) p1387 p1388
    have p1390 := @g_sseldd syntaxFormula0265 (.cv u) (.cv x) (.cv a) p1386 p1389
    have p1391 :=
      @g_syl syntaxFormula0269 syntaxFormula0265 (.classMem (.cv a) (.cv x)) p1376 p1390
    have p1392 :=
      @g_simpl syntaxFormula0265 (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
    have p1393 :=
      @g_simpl syntaxFormula0264 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
    have p1394 := @g_simpl syntaxFormula0263 (.classMem (.cv a) (.cv u))
    have p1395 := @g_syl syntaxFormula0265 syntaxFormula0264 syntaxFormula0263 p1393 p1394
    have p1396 := @g_simpl syntaxFormula0262 syntaxFormula0255
    have p1397 := @g_syl syntaxFormula0265 syntaxFormula0263 syntaxFormula0262 p1395 p1396
    have p1398 :=
      @g_simpl
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (.classMem (.cv z) (.cv u))
    have p1399 :=
      @g_syl syntaxFormula0265 syntaxFormula0262
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        p1397 p1398
    have p1400 :=
      @g_simpr syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))
    have p1401 :=
      @g_simpld
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)) p1400
    have p1402 :=
      @g_syl syntaxFormula0265
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (syn_wss (.cv u) (.cv x)) p1399 p1401
    have p1403 :=
      @g_simpl syntaxFormula0264 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
    have p1404 := @g_simpl syntaxFormula0263 (.classMem (.cv a) (.cv u))
    have p1405 := @g_syl syntaxFormula0265 syntaxFormula0264 syntaxFormula0263 p1403 p1404
    have p1406 := @g_simpl syntaxFormula0262 syntaxFormula0255
    have p1407 := @g_syl syntaxFormula0265 syntaxFormula0263 syntaxFormula0262 p1405 p1406
    have p1408 :=
      @g_simpr
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (.classMem (.cv z) (.cv u))
    have p1409 :=
      @g_syl syntaxFormula0265 syntaxFormula0262 (.classMem (.cv z) (.cv u)) p1407 p1408
    have p1410 := @g_sseldd syntaxFormula0265 (.cv u) (.cv x) (.cv z) p1402 p1409
    have p1411 :=
      @g_syl syntaxFormula0269 syntaxFormula0265 (.classMem (.cv z) (.cv x)) p1392 p1410
    have p1412 := @g_breq1 (.cv b) (.cv a) (.cv c) (syn_cpwpull (.cv f) (.cv r))
    have p1413 := @g_breq2 (.cv b) (.cv a) (.cv c) (syn_cpwpull (.cv f) (.cv r))
    have p1414 :=
      @g_anbi12d (.classEq (.cv b) (.cv a))
        (syn_wbr (.cv b) (syn_cpwpull (.cv f) (.cv r)) (.cv c))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv c))
        (syn_wbr (.cv c) (syn_cpwpull (.cv f) (.cv r)) (.cv b))
        (syn_wbr (.cv c) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p1412 p1413
    have p1415 := @g_eqeq1 (.cv b) (.cv a) (.cv c)
    have p1416_e01_recanon :
      Nominal.NPrf
        (.imp (.classEq (.cv b) (.cv a)) (syn_wb (.objEq b c) (.classEq (.cv a) (.cv c)))) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_wb]
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
        p1415
    have p1416 :=
      @g_imbi12d (.classEq (.cv b) (.cv a)) syntaxFormula0270 syntaxFormula0274
        (.objEq b c) (.classEq (.cv a) (.cv c)) p1414 p1416_e01_recanon
    have p1417 := @g_breq2 (.cv c) (.cv z) (.cv a) (syn_cpwpull (.cv f) (.cv r))
    have p1418 := @g_breq1 (.cv c) (.cv z) (.cv a) (syn_cpwpull (.cv f) (.cv r))
    have p1419 :=
      @g_anbi12d (.classEq (.cv c) (.cv z))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv c))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
        (syn_wbr (.cv c) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) p1417 p1418
    have p1420 := @g_eqeq2 (.cv c) (.cv z) (.cv a)
    have p1421 :=
      @g_imbi12d (.classEq (.cv c) (.cv z)) syntaxFormula0274 syntaxFormula0275
        (.classEq (.cv a) (.cv c)) (.classEq (.cv a) (.cv z)) p1419 p1420
    have p1422 :=
      @g_rspc2v (.imp syntaxFormula0270 (.objEq b c)) syntaxFormula0276
        (.imp syntaxFormula0274 (.classEq (.cv a) (.cv c))) b c (.cv a) (.cv z) (.cv x)
        (.cv x) dv_cache_0208 dv_cache_0112 dv_cache_0209 dv_cache_0028 dv_cache_0028
        dv_cache_0029 dv_cache_0210 dv_cache_0211 dv_cache_0032 p1416 p1421
    have p1423 :=
      @g_syl2anc syntaxFormula0269 (.classMem (.cv a) (.cv x)) (.classMem (.cv z) (.cv x))
        (.imp (syn_wral b (.cv x) (syn_wral c (.cv x) (.imp syntaxFormula0270 (.objEq b c))))
          syntaxFormula0276)
        p1391 p1411 p1422
    have p1424_e01_recanon :
      Nominal.NPrf (.imp syntaxFormula0269 (.imp syntaxFormula0273 syntaxFormula0276)) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_wral]
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
        p1423
    have p1424 :=
      @g_sylcom
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0269 syntaxFormula0273 syntaxFormula0276 p1375 p1424_e01_recanon
    have p1425 :=
      @g_syl7bi
        (syn_wa (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
          (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)))
        syntaxFormula0275
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0269 (.classEq (.cv a) (.cv z)) p1361 p1424
    have p1426 :=
      @g_exp4a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0269 (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) (.classEq (.cv a) (.cv z))
        p1425
    have p1427 :=
      Nominal.ax2 (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) (.classEq (.cv a) (.cv z))
    have p1428 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0269
        (.imp (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) syntaxFormula0277)
        (.imp (.imp (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
            (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))) syntaxFormula0278)
        p1426 p1427
    have p1429 :=
      @g_mpdi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0269
        (.imp (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
          (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)))
        syntaxFormula0278 p1360 p1428
    have p1430 :=
      @g_mpdi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0269 (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (.classEq (.cv a) (.cv z)) p1356 p1429
    have p1431 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0265 (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a))
        (.classEq (.cv a) (.cv z)) p1430
    have p1432 :=
      @g_a1dd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0265 syntaxFormula0278 (.neg (.classEq (.cv a) (.cv z))) p1431
    have p1433 :=
      Nominal.ax2 (.neg (.classEq (.cv a) (.cv z)))
        (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)) (.classEq (.cv a) (.cv z))
    have p1434 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0265 (.imp (.neg (.classEq (.cv a) (.cv z))) syntaxFormula0278)
        (.imp (.imp (.neg (.classEq (.cv a) (.cv z)))
            (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
          (.imp (.neg (.classEq (.cv a) (.cv z))) (.classEq (.cv a) (.cv z))))
        p1432 p1433
    have p1435 :=
      @g_mpdi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0265
        (.imp (.neg (.classEq (.cv a) (.cv z)))
          (syn_wbr (.cv z) (syn_cpwpull (.cv f) (.cv r)) (.cv a)))
        (.imp (.neg (.classEq (.cv a) (.cv z))) (.classEq (.cv a) (.cv z))) p1355 p1434
    have p1436 := @g_pm2_18 (.classEq (.cv a) (.cv z))
    have p1437 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0265
        (.imp (.neg (.classEq (.cv a) (.cv z))) (.classEq (.cv a) (.cv z)))
        (.classEq (.cv a) (.cv z)) p1435 p1436
    have p1438 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0264 (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z))
        (.classEq (.cv a) (.cv z)) p1437
    have p1439 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0263 (.classMem (.cv a) (.cv u)) syntaxFormula0277 p1438
    have p1440 :=
      @g_ralrimdv
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0263 syntaxFormula0277 a (.cv u) dv_cache_0019 dv_cache_0212 p1439
    have p1441 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0262 syntaxFormula0255 syntaxFormula0279 p1440
    have p1442 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (.classMem (.cv z) (.cv u)) syntaxFormula0280 p1441
    have p1443 :=
      @g_alimdv
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        syntaxFormula0281 z dv_cache_0072 p1442
    have p1444 :=
      @g_syl5
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        (.all z (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))))
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syntaxFormula0282 p1326 p1443
    have p1445 := (Nominal.biimpRefl syntaxFormula0283)
    have p1446 :=
      @g_syl6ibr
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        syntaxFormula0282 syntaxFormula0283 p1444 p1445
    have p1447 := @g_rexim syntaxFormula0255 syntaxFormula0279 z (.cv u)
    have p1448 :=
      @g_syl6
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        syntaxFormula0283 (.imp syntaxFormula0256 syntaxFormula0284) p1446 p1447
    have p1449 :=
      @g_mpdd
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))))
        syntaxFormula0256 syntaxFormula0284 p1324 p1448
    have p1450 :=
      @g_exp3a
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)))
        syntaxFormula0284 p1449
    have p1451 :=
      @g_alrimdv
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0285 u dv_cache_0213 dv_cache_0214 p1450
    have p1455 :=
      @g_jca syn_wtru (.classMem (syn_cpwpull (.cv f) (.cv r)) (syn_cvv))
        (.classMem (.cv x) (syn_cvv)) p0115 p0117
    have p1457 :=
      @g_imbi1d (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))
        (syn_wbr (.cv a) (.cv c) (.cv z))
        (syn_wbr (.cv a) (syn_cpwpull (.cv f) (.cv r)) (.cv z)) (.classEq (.cv a) (.cv z))
        p0440
    have p1458 :=
      @g_rexralbidv (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r)))
        (.imp (syn_wbr (.cv a) (.cv c) (.cv z)) (.classEq (.cv a) (.cv z)))
        syntaxFormula0277 z a (.cv u) (.cv u) dv_cache_0076 dv_cache_0077 p1457
    have p1459 :=
      @g_imbi2d (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r))) syntaxFormula0287
        syntaxFormula0284 (syn_wa (syn_wss (.cv u) (.cv b)) (syn_wne (.cv u) (syn_c0)))
        p1458
    have p1460 :=
      @g_albidv (.classEq (.cv c) (syn_cpwpull (.cv f) (.cv r))) syntaxFormula0288
        syntaxFormula0289 u dv_cache_0215 p1459
    have p1461 := @g_sseq2 (.cv b) (.cv x) (.cv u)
    have p1462 :=
      @g_anbi1d (.classEq (.cv b) (.cv x)) (syn_wss (.cv u) (.cv b))
        (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0)) p1461
    have p1463 :=
      @g_imbi1d (.classEq (.cv b) (.cv x))
        (syn_wa (syn_wss (.cv u) (.cv b)) (syn_wne (.cv u) (syn_c0)))
        (syn_wa (syn_wss (.cv u) (.cv x)) (syn_wne (.cv u) (syn_c0))) syntaxFormula0284
        p1462
    have p1464 :=
      @g_albidv (.classEq (.cv b) (.cv x)) syntaxFormula0289 syntaxFormula0285 u
        dv_cache_0216 p1463
    have p1465 :=
      NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_found u a z c b
        dv_cache_0032 dv_cache_0217 dv_cache_0025 dv_cache_0086 dv_cache_0218
        dv_cache_0024 dv_cache_0084 dv_cache_0219 dv_cache_0220 dv_cache_0085
    have p1466_e02_recanon :
      Nominal.NPrf (.classEq (syn_cfound) (syn_copab c b syntaxFormula0290)) :=
      Nominal.RecanonTransportDev.transport
        (by
          simp only [syn_cfound, syn_copab, syn_wex, syn_wa, syn_wss, syn_cin, syn_ccompl,
            syn_cnin, syn_wnan, syn_wne, syn_c0, syn_cdif, syn_cvv, syn_wrex, syn_wral,
            syn_wbr, syn_cop, syn_cun]
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
        p1465
    have p1466 :=
      @g_brabg syntaxFormula0290 (.all u syntaxFormula0289) syntaxFormula0291 c b
        (syn_cpwpull (.cv f) (.cv r)) (.cv x) (syn_cvv) (syn_cvv) (syn_cfound)
        dv_cache_0027 dv_cache_0026 dv_cache_0029 dv_cache_0028 dv_cache_0221
        dv_cache_0222 dv_cache_0006 p1460 p1464 p1466_e02_recanon
    have p1467 :=
      @g_syl syn_wtru
        (syn_wa (.classMem (syn_cpwpull (.cv f) (.cv r)) (syn_cvv))
          (.classMem (.cv x) (syn_cvv)))
        (syn_wb (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cfound) (.cv x)) syntaxFormula0291)
        p1455 p1466
    have p1468 :=
      @g_biimprd syn_wtru (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cfound) (.cv x))
        syntaxFormula0291 p1467
    have p1469 :=
      @g_sylcom
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru syntaxFormula0291
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cfound) (.cv x)) p1451 p1468
    have p1470 :=
      @g_mpi
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        syn_wtru (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cfound) (.cv x)) p0000 p1469
    have p1471 :=
      @g_jca
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cstrict) (.cv x))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cfound) (.cv x)) p0687 p1470
    have p1473 :=
      @g_breqi (syn_cpwpull (.cv f) (.cv r)) (.cv x) (syn_cwe)
        (syn_cin (syn_cstrict) (syn_cfound)) p0777
    have p1474 := @g_brin (syn_cpwpull (.cv f) (.cv r)) (.cv x) (syn_cstrict) (syn_cfound)
    have p1475 :=
      @g_bitri (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cin (syn_cstrict) (syn_cfound)) (.cv x))
        (syn_wa (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cstrict) (.cv x))
          (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cfound) (.cv x)))
        p1473 p1474
    have p1476 :=
      @g_sylibr
        (syn_wa (syn_wf1o (.cv f) (.cv x) (.cv y)) (syn_wbr (.cv r) (syn_cwe) (.cv y)))
        (syn_wa (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cstrict) (.cv x))
          (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cfound) (.cv x)))
        (syn_wbr (syn_cpwpull (.cv f) (.cv r)) (syn_cwe) (.cv x)) p1471 p1475
    exact continuation p1476

end NFChoice.DirectNominalPrf.WPPReplay
