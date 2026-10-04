/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part034`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_enpw1lem1`. -/
@[expose]
noncomputable def gEnpw1lem1 (x : Var) (y : Var) (g : Var) (dv_g_x : g ≠ x)
    (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classMem (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
        (synCvv)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ g } : Finset Var)
  let p : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_y : p ≠ y := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_g : p ≠ g := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_y : a ≠ y := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_b_ne_y : b ≠ y := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_a : p ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_p : a ≠ p := Ne.symm fresh_p_ne_a
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have dv_cache_0001 : p ∉ ((synCsn (synCop (.cv x) (.cv y)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, or_false, not_false_eq_true])
  have dv_cache_0002 :
    p ∉
      ((synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
          (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Class.cv g)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_g, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_p, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((synCsn (synCop (.cv x) (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_x, fresh_a_ne_y, or_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((synCsi (synCcnv (synC1st)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0007 : a ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : b ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_x, fresh_b_ne_y, or_false, not_false_eq_true])
  have dv_cache_0009 : b ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_a, not_false_eq_true])
  have dv_cache_0010 : b ∉ ((synCcnv (synC1st))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0011 : b ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_x, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((Wff.classEq (.cv a) (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_x, or_false, not_false_eq_true])
  have dv_cache_0013 : a ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_x,
          not_false_eq_true])
  have dv_cache_0014 : a ∉ ((synWbr (.cv p) (synC1st) (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((synCsi (synCcnv (synC2nd)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0016 : a ∉ ((synC2nd)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0017 : b ∉ ((synCcnv (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0018 : b ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_y, not_false_eq_true])
  have dv_cache_0019 : b ∉ ((Wff.classEq (.cv a) (synCsn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_a, fresh_b_ne_y, or_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((synCsn (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_y,
          not_false_eq_true])
  have dv_cache_0021 : a ∉ ((synWbr (.cv p) (synC2nd) (synCsn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_p, fresh_a_ne_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0022 : p ∉ ((synCop (synCsn (.cv x)) (synCsn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_ne_y, or_false, not_false_eq_true])
  have dv_cache_0023 :
    x ∉
      ((synCuni1 (synCima (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
              (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))) (.cv g)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_g_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0024 :
    y ∉
      ((synCuni1 (synCima (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
              (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))) (.cv g)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_g_y), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0025 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show x ≠ y from (by exact dv_x_y))
  have p0000 := @gVex x
  have p0001 := @gVex y
  have p0002 := @gOpex (.cv x) (.cv y) p0000 p0001
  have p0003 :=
    @gEluni1 (synCop (.cv x) (.cv y))
      (synCima (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
          (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))) (.cv g))
      p0002
  have p0004 :=
    @gElima p (synCsn (synCop (.cv x) (.cv y)))
      (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
        (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd)))
      (.cv g) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    @gBrin (.cv p) (synCsn (synCop (.cv x) (.cv y)))
      (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
      (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))
  have p0006 :=
    @gBrco a (.cv p) (synCsn (synCop (.cv x) (.cv y))) (synCsi (synCcnv (synC1st)))
      (synC1st) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0007 :=
    @gAncom (synWbr (.cv p) (synC1st) (.cv a))
      (synWbr (.cv a) (synCsi (synCcnv (synC1st))) (synCsn (synCop (.cv x) (.cv y))))
  have p0008 :=
    @gBrsnsi2 b (synCop (.cv x) (.cv y)) (.cv a) (synCcnv (synC1st)) dv_cache_0008
      dv_cache_0009 dv_cache_0010 p0002
  have p0009 :=
    @gAncom (.classEq (.cv a) (synCsn (.cv b)))
      (synWbr (.cv b) (synCcnv (synC1st)) (synCop (.cv x) (.cv y)))
  have p0010 := @gBrcnv (.cv b) (synCop (.cv x) (.cv y)) (synC1st)
  have p0011 := @gOpbr1st (.cv x) (.cv y) (.cv b) p0000 p0001
  have p0012 := @gEqucom x b
  have p0013_e01_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv x) (.cv y)) (synC1st) (.cv b)) (.objEq x b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC1st synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0013 :=
    @gN3bitri (synWbr (.cv b) (synCcnv (synC1st)) (synCop (.cv x) (.cv y)))
      (synWbr (synCop (.cv x) (.cv y)) (synC1st) (.cv b)) (.objEq x b) (.objEq b x)
      p0010 p0013_e01_recanon p0012
  have p0014 :=
    @gAnbi1i (synWbr (.cv b) (synCcnv (synC1st)) (synCop (.cv x) (.cv y)))
      (.objEq b x) (.classEq (.cv a) (synCsn (.cv b))) p0013
  have p0015 :=
    @gBitri
      (synWa (.classEq (.cv a) (synCsn (.cv b)))
        (synWbr (.cv b) (synCcnv (synC1st)) (synCop (.cv x) (.cv y))))
      (synWa (synWbr (.cv b) (synCcnv (synC1st)) (synCop (.cv x) (.cv y)))
        (.classEq (.cv a) (synCsn (.cv b))))
      (synWa (.objEq b x) (.classEq (.cv a) (synCsn (.cv b)))) p0009 p0014
  have p0016 :=
    @gExbii
      (synWa (.classEq (.cv a) (synCsn (.cv b)))
        (synWbr (.cv b) (synCcnv (synC1st)) (synCop (.cv x) (.cv y))))
      (synWa (.objEq b x) (.classEq (.cv a) (synCsn (.cv b)))) b p0015
  have p0017 := @gSneq (.cv b) (.cv x)
  have p0018_e00_recanon :
    Nominal.NPrf (.imp (.objEq b x) (.classEq (synCsn (.cv b)) (synCsn (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0018 :=
    @gEqeq2d (.objEq b x) (synCsn (.cv b)) (synCsn (.cv x)) (.cv a) p0018_e00_recanon
  have p0019_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (.cv x)) (synWb (.classEq (.cv a) (synCsn (.cv b)))
          (.classEq (.cv a) (synCsn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0019 :=
    @gCeqsexv (.classEq (.cv a) (synCsn (.cv b))) (.classEq (.cv a) (synCsn (.cv x))) b
      (.cv x) dv_cache_0011 dv_cache_0012 p0000 p0019_e01_recanon
  have p0020_e02_recanon :
    Nominal.NPrf
      (synWb (synWex b (synWa (.objEq b x) (.classEq (.cv a) (synCsn (.cv b)))))
        (.classEq (.cv a) (synCsn (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0019
  have p0020 :=
    @gN3bitri
      (synWbr (.cv a) (synCsi (synCcnv (synC1st))) (synCsn (synCop (.cv x) (.cv y))))
      (synWex b (synWa (.classEq (.cv a) (synCsn (.cv b)))
          (synWbr (.cv b) (synCcnv (synC1st)) (synCop (.cv x) (.cv y)))))
      (synWex b (synWa (.objEq b x) (.classEq (.cv a) (synCsn (.cv b)))))
      (.classEq (.cv a) (synCsn (.cv x))) p0008 p0016 p0020_e02_recanon
  have p0021 :=
    @gAnbi1i
      (synWbr (.cv a) (synCsi (synCcnv (synC1st))) (synCsn (synCop (.cv x) (.cv y))))
      (.classEq (.cv a) (synCsn (.cv x))) (synWbr (.cv p) (synC1st) (.cv a)) p0020
  have p0022 :=
    @gBitri
      (synWa (synWbr (.cv p) (synC1st) (.cv a))
        (synWbr (.cv a) (synCsi (synCcnv (synC1st))) (synCsn (synCop (.cv x) (.cv y)))))
      (synWa (synWbr (.cv a) (synCsi (synCcnv (synC1st)))
          (synCsn (synCop (.cv x) (.cv y)))) (synWbr (.cv p) (synC1st) (.cv a)))
      (synWa (.classEq (.cv a) (synCsn (.cv x))) (synWbr (.cv p) (synC1st) (.cv a)))
      p0007 p0021
  have p0023 :=
    @gExbii
      (synWa (synWbr (.cv p) (synC1st) (.cv a))
        (synWbr (.cv a) (synCsi (synCcnv (synC1st))) (synCsn (synCop (.cv x) (.cv y)))))
      (synWa (.classEq (.cv a) (synCsn (.cv x))) (synWbr (.cv p) (synC1st) (.cv a))) a
      p0022
  have p0024 := @gSnex (.cv x)
  have p0025 := @gBreq2 (.cv a) (synCsn (.cv x)) (.cv p) (synC1st)
  have p0026 :=
    @gCeqsexv (synWbr (.cv p) (synC1st) (.cv a))
      (synWbr (.cv p) (synC1st) (synCsn (.cv x))) a (synCsn (.cv x)) dv_cache_0013
      dv_cache_0014 p0024 p0025
  have p0027 :=
    @gN3bitri
      (synWbr (.cv p) (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
        (synCsn (synCop (.cv x) (.cv y))))
      (synWex a (synWa (synWbr (.cv p) (synC1st) (.cv a))
          (synWbr (.cv a) (synCsi (synCcnv (synC1st)))
            (synCsn (synCop (.cv x) (.cv y))))))
      (synWex a (synWa (.classEq (.cv a) (synCsn (.cv x)))
          (synWbr (.cv p) (synC1st) (.cv a))))
      (synWbr (.cv p) (synC1st) (synCsn (.cv x))) p0006 p0023 p0026
  have p0028 :=
    @gBrco a (.cv p) (synCsn (synCop (.cv x) (.cv y))) (synCsi (synCcnv (synC2nd)))
      (synC2nd) dv_cache_0004 dv_cache_0005 dv_cache_0015 dv_cache_0016
  have p0029 :=
    @gBrsnsi2 b (synCop (.cv x) (.cv y)) (.cv a) (synCcnv (synC2nd)) dv_cache_0008
      dv_cache_0009 dv_cache_0017 p0002
  have p0030 := @gBrcnv (.cv b) (synCop (.cv x) (.cv y)) (synC2nd)
  have p0031 := @gOpbr2nd (.cv x) (.cv y) (.cv b) p0000 p0001
  have p0032 := @gEqucom y b
  have p0033_e01_recanon :
    Nominal.NPrf
      (synWb (synWbr (synCop (.cv x) (.cv y)) (synC2nd) (.cv b)) (.objEq y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synC2nd synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0031
  have p0033 :=
    @gN3bitri (synWbr (.cv b) (synCcnv (synC2nd)) (synCop (.cv x) (.cv y)))
      (synWbr (synCop (.cv x) (.cv y)) (synC2nd) (.cv b)) (.objEq y b) (.objEq b y)
      p0030 p0033_e01_recanon p0032
  have p0034 :=
    @gAnbi2i (synWbr (.cv b) (synCcnv (synC2nd)) (synCop (.cv x) (.cv y)))
      (.objEq b y) (.classEq (.cv a) (synCsn (.cv b))) p0033
  have p0035 := @gAncom (.classEq (.cv a) (synCsn (.cv b))) (.objEq b y)
  have p0036 :=
    @gBitri
      (synWa (.classEq (.cv a) (synCsn (.cv b)))
        (synWbr (.cv b) (synCcnv (synC2nd)) (synCop (.cv x) (.cv y))))
      (synWa (.classEq (.cv a) (synCsn (.cv b))) (.objEq b y))
      (synWa (.objEq b y) (.classEq (.cv a) (synCsn (.cv b)))) p0034 p0035
  have p0037 :=
    @gExbii
      (synWa (.classEq (.cv a) (synCsn (.cv b)))
        (synWbr (.cv b) (synCcnv (synC2nd)) (synCop (.cv x) (.cv y))))
      (synWa (.objEq b y) (.classEq (.cv a) (synCsn (.cv b)))) b p0036
  have p0038 := @gSneq (.cv b) (.cv y)
  have p0039_e00_recanon :
    Nominal.NPrf (.imp (.objEq b y) (.classEq (synCsn (.cv b)) (synCsn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @gEqeq2d (.objEq b y) (synCsn (.cv b)) (synCsn (.cv y)) (.cv a) p0039_e00_recanon
  have p0040_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (.cv y)) (synWb (.classEq (.cv a) (synCsn (.cv b)))
          (.classEq (.cv a) (synCsn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0039
  have p0040 :=
    @gCeqsexv (.classEq (.cv a) (synCsn (.cv b))) (.classEq (.cv a) (synCsn (.cv y))) b
      (.cv y) dv_cache_0018 dv_cache_0019 p0001 p0040_e01_recanon
  have p0041_e02_recanon :
    Nominal.NPrf
      (synWb (synWex b (synWa (.objEq b y) (.classEq (.cv a) (synCsn (.cv b)))))
        (.classEq (.cv a) (synCsn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWex synWa synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0040
  have p0041 :=
    @gN3bitri
      (synWbr (.cv a) (synCsi (synCcnv (synC2nd))) (synCsn (synCop (.cv x) (.cv y))))
      (synWex b (synWa (.classEq (.cv a) (synCsn (.cv b)))
          (synWbr (.cv b) (synCcnv (synC2nd)) (synCop (.cv x) (.cv y)))))
      (synWex b (synWa (.objEq b y) (.classEq (.cv a) (synCsn (.cv b)))))
      (.classEq (.cv a) (synCsn (.cv y))) p0029 p0037 p0041_e02_recanon
  have p0042 :=
    @gAnbi2i
      (synWbr (.cv a) (synCsi (synCcnv (synC2nd))) (synCsn (synCop (.cv x) (.cv y))))
      (.classEq (.cv a) (synCsn (.cv y))) (synWbr (.cv p) (synC2nd) (.cv a)) p0041
  have p0043 :=
    @gAncom (synWbr (.cv p) (synC2nd) (.cv a)) (.classEq (.cv a) (synCsn (.cv y)))
  have p0044 :=
    @gBitri
      (synWa (synWbr (.cv p) (synC2nd) (.cv a))
        (synWbr (.cv a) (synCsi (synCcnv (synC2nd))) (synCsn (synCop (.cv x) (.cv y)))))
      (synWa (synWbr (.cv p) (synC2nd) (.cv a)) (.classEq (.cv a) (synCsn (.cv y))))
      (synWa (.classEq (.cv a) (synCsn (.cv y))) (synWbr (.cv p) (synC2nd) (.cv a)))
      p0042 p0043
  have p0045 :=
    @gExbii
      (synWa (synWbr (.cv p) (synC2nd) (.cv a))
        (synWbr (.cv a) (synCsi (synCcnv (synC2nd))) (synCsn (synCop (.cv x) (.cv y)))))
      (synWa (.classEq (.cv a) (synCsn (.cv y))) (synWbr (.cv p) (synC2nd) (.cv a))) a
      p0044
  have p0046 := @gSnex (.cv y)
  have p0047 := @gBreq2 (.cv a) (synCsn (.cv y)) (.cv p) (synC2nd)
  have p0048 :=
    @gCeqsexv (synWbr (.cv p) (synC2nd) (.cv a))
      (synWbr (.cv p) (synC2nd) (synCsn (.cv y))) a (synCsn (.cv y)) dv_cache_0020
      dv_cache_0021 p0046 p0047
  have p0049 :=
    @gN3bitri
      (synWbr (.cv p) (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))
        (synCsn (synCop (.cv x) (.cv y))))
      (synWex a (synWa (synWbr (.cv p) (synC2nd) (.cv a))
          (synWbr (.cv a) (synCsi (synCcnv (synC2nd)))
            (synCsn (synCop (.cv x) (.cv y))))))
      (synWex a (synWa (.classEq (.cv a) (synCsn (.cv y)))
          (synWbr (.cv p) (synC2nd) (.cv a))))
      (synWbr (.cv p) (synC2nd) (synCsn (.cv y))) p0028 p0045 p0048
  have p0050 :=
    @gAnbi12i
      (synWbr (.cv p) (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
        (synCsn (synCop (.cv x) (.cv y))))
      (synWbr (.cv p) (synC1st) (synCsn (.cv x)))
      (synWbr (.cv p) (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))
        (synCsn (synCop (.cv x) (.cv y))))
      (synWbr (.cv p) (synC2nd) (synCsn (.cv y))) p0027 p0049
  have p0051 := @gOp1st2nd (synCsn (.cv x)) (synCsn (.cv y)) (.cv p) p0024 p0046
  have p0052 :=
    @gN3bitri
      (synWbr (.cv p) (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
          (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd)))
        (synCsn (synCop (.cv x) (.cv y))))
      (synWa (synWbr (.cv p) (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
          (synCsn (synCop (.cv x) (.cv y))))
        (synWbr (.cv p) (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))
          (synCsn (synCop (.cv x) (.cv y)))))
      (synWa (synWbr (.cv p) (synC1st) (synCsn (.cv x)))
        (synWbr (.cv p) (synC2nd) (synCsn (.cv y))))
      (.classEq (.cv p) (synCop (synCsn (.cv x)) (synCsn (.cv y)))) p0005 p0050 p0051
  have p0053 :=
    @gRexbii
      (synWbr (.cv p) (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
          (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd)))
        (synCsn (synCop (.cv x) (.cv y))))
      (.classEq (.cv p) (synCop (synCsn (.cv x)) (synCsn (.cv y)))) p (.cv g) p0052
  have p0054 :=
    @gBitri
      (.classMem (synCsn (synCop (.cv x) (.cv y))) (synCima
          (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
            (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))) (.cv g)))
      (synWrex p (.cv g) (synWbr (.cv p)
          (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
            (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd)))
          (synCsn (synCop (.cv x) (.cv y)))))
      (synWrex p (.cv g) (.classEq (.cv p) (synCop (synCsn (.cv x)) (synCsn (.cv y)))))
      p0004 p0053
  have p0055 := (Nominal.biimpRefl (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
  have p0056 :=
    @gRisset p (synCop (synCsn (.cv x)) (synCsn (.cv y))) (.cv g) dv_cache_0022
      dv_cache_0003
  have p0057 :=
    @gBitr2i (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (.classMem (synCop (synCsn (.cv x)) (synCsn (.cv y))) (.cv g))
      (synWrex p (.cv g) (.classEq (.cv p) (synCop (synCsn (.cv x)) (synCsn (.cv y)))))
      p0055 p0056
  have p0058 :=
    @gN3bitri
      (.classMem (synCop (.cv x) (.cv y)) (synCuni1 (synCima
            (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
              (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))) (.cv g))))
      (.classMem (synCsn (synCop (.cv x) (.cv y))) (synCima
          (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
            (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))) (.cv g)))
      (synWrex p (.cv g) (.classEq (.cv p) (synCop (synCsn (.cv x)) (synCsn (.cv y)))))
      (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))) p0003 p0054 p0057
  have p0059 :=
    @gOpabbi2i (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))) x y
      (synCuni1 (synCima (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
            (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))) (.cv g)))
      dv_cache_0023 dv_cache_0024 dv_cache_0025 p0058
  have p0060 := @gN1stex
  have p0061 := @gCnvex (synC1st) p0060
  have p0062 := @gSiex (synCcnv (synC1st)) p0061
  have p0064 := @gCoex (synCsi (synCcnv (synC1st))) (synC1st) p0062 p0060
  have p0065 := @gN2ndex
  have p0066 := @gCnvex (synC2nd) p0065
  have p0067 := @gSiex (synCcnv (synC2nd)) p0066
  have p0069 := @gCoex (synCsi (synCcnv (synC2nd))) (synC2nd) p0067 p0065
  have p0070 :=
    @gInex (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
      (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd)) p0064 p0069
  have p0071 := @gVex g
  have p0072 :=
    @gImaex
      (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
        (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd)))
      (.cv g) p0070 p0071
  have p0073 :=
    @gUni1ex
      (synCima (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
          (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))) (.cv g))
      p0072
  have p0074 :=
    @gEqeltrri
      (synCuni1 (synCima (synCin (synCcom (synCsi (synCcnv (synC1st))) (synC1st))
            (synCcom (synCsi (synCcnv (synC2nd))) (synC2nd))) (.cv g)))
      (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (synCvv)
      p0059 p0073
  exact p0074


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part035`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_enpw1`. -/
@[expose]
noncomputable def gEnpw1 (A : Class) (B : Class) :
    Nominal.NPrf
      (synWb (synWbr A (synCen) B) (synWbr (synCpw1 A) (synCen) (synCpw1 B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let f : Var := freshVar proofSupport 2
  let g : Var := freshVar proofSupport 3
  let x : Var := freshVar proofSupport 4
  let y : Var := freshVar proofSupport 5
  let z : Var := freshVar proofSupport 6
  let w : Var := freshVar proofSupport 7
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (h))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_f : a ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_f_ne_a : f ≠ a := Ne.symm fresh_a_ne_f
  have fresh_a_ne_g : a ≠ g :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_g_ne_a : g ≠ a := Ne.symm fresh_a_ne_g
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_y : a ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_y_ne_a : y ≠ a := Ne.symm fresh_a_ne_y
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 0) (j := 6) (by decide)
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_ne_w : a ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 0) (j := 7) (by decide)
  have fresh_w_ne_a : w ≠ a := Ne.symm fresh_a_ne_w
  have fresh_b_ne_f : b ≠ f :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_f_ne_b : f ≠ b := Ne.symm fresh_b_ne_f
  have fresh_b_ne_g : b ≠ g :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_g_ne_b : g ≠ b := Ne.symm fresh_b_ne_g
  have fresh_b_ne_x : b ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_x_ne_b : x ≠ b := Ne.symm fresh_b_ne_x
  have fresh_b_ne_y : b ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_y_ne_b : y ≠ b := Ne.symm fresh_b_ne_y
  have fresh_b_ne_z : b ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_z_ne_b : z ≠ b := Ne.symm fresh_b_ne_z
  have fresh_b_ne_w : b ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 1) (j := 7) (by decide)
  have fresh_w_ne_b : w ≠ b := Ne.symm fresh_b_ne_w
  have fresh_g_ne_x : g ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_x_ne_g : x ≠ g := Ne.symm fresh_g_ne_x
  have fresh_g_ne_y : g ≠ y :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_y_ne_g : y ≠ g := Ne.symm fresh_g_ne_y
  have fresh_g_ne_z : g ≠ z :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 3) (j := 6) (by decide)
  have fresh_z_ne_g : z ≠ g := Ne.symm fresh_g_ne_z
  have fresh_g_ne_w : g ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 3) (j := 7) (by decide)
  have fresh_w_ne_g : w ≠ g := Ne.symm fresh_g_ne_w
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 4) (j := 7) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 5) (j := 7) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 6 ≠ freshVar proofSupport 7
    exact freshVar_injective proofSupport (i := 6) (j := 7) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : f ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_a, not_false_eq_true])
  have dv_cache_0002 : f ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_b, not_false_eq_true])
  have dv_cache_0003 :
    f ∉ ((synWbr (synCpw1 (.cv a)) (synCen) (synCpw1 (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          Finset.mem_singleton, fresh_f_ne_a, fresh_f_ne_b, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((synCpw1 (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_g_ne_a,
          not_false_eq_true])
  have dv_cache_0005 : g ∉ ((synCpw1 (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_g_ne_b,
          not_false_eq_true])
  have dv_cache_0006 :
    y ∉ ((synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, fresh_y_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0007 :
    z ∉ ((synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_b, fresh_z_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0008 : z ∉ ((synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0009 : y ∉ ((synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, fresh_y_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0010 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0011 :
    x ∉ ((synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, fresh_x_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0012 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : z ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
          not_false_eq_true])
  have dv_cache_0014 : z ∉ ((Class.cv g)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_g, not_false_eq_true])
  have dv_cache_0015 : w ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0016 : w ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_b, not_false_eq_true])
  have dv_cache_0017 : y ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_w, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_w, fresh_y_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0019 :
    w ∉
      ((Wff.imp (synWbr (synCsn (.cv x)) (.cv g) (.cv z))
          (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z,
          fresh_w_ne_g, fresh_w_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0020 :
    z ∉ ((synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_g, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0021 : y ∉ ((Wff.classMem (synCsn (.cv x)) (synCdm (.cv g)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdm, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_g, or_false, not_false_eq_true])
  have dv_cache_0022 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((synWbr (synCsn (.cv z)) (.cv g) (synCsn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_y, fresh_x_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0024 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0025 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0026 : z ∉ ((synCsn (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_y,
          not_false_eq_true])
  have dv_cache_0027 : w ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_a, not_false_eq_true])
  have dv_cache_0028 : x ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_w, not_false_eq_true])
  have dv_cache_0029 : x ∉ ((synWbr (synCsn (.cv w)) (.cv g) (synCsn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_y, fresh_x_ne_g, or_false,
          not_false_eq_true])
  have dv_cache_0030 :
    w ∉
      ((Wff.imp (synWbr (.cv z) (.cv g) (synCsn (.cv y)))
          (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y,
          fresh_w_ne_g, fresh_w_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0031 :
    z ∉ ((synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_g, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0032 : x ∉ ((Wff.classMem (synCsn (.cv y)) (synCrn (.cv g)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_g, or_false, not_false_eq_true])
  have dv_cache_0033 : y ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_b, not_false_eq_true])
  have dv_cache_0034 : g ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show g ≠ x from (by exact fresh_g_ne_x))
  have dv_cache_0035 : g ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show g ≠ y from (by exact fresh_g_ne_y))
  have dv_cache_0036 : g ∉ ((synWbr (.cv a) (synCen) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_a, fresh_g_ne_b, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0037 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0038 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0039 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0040 :
    b ∉
      ((synWb (synWbr A (synCen) B) (synWbr (synCpw1 A) (synCen) (synCpw1 B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0041 :
    a ∉
      ((synWb (synWbr A (synCen) (.cv b))
          (synWbr (synCpw1 A) (synCen) (synCpw1 (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wb,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := @gBrex A B (synCen)
  have p0001 := @gBrex (synCpw1 A) (synCpw1 B) (synCen)
  have p0002 := @gPw1exb A
  have p0003 := @gPw1exb B
  have p0004 :=
    @gAnbi12i (.classMem (synCpw1 A) (synCvv)) (.classMem A (synCvv))
      (.classMem (synCpw1 B) (synCvv)) (.classMem B (synCvv)) p0002 p0003
  have p0005 :=
    @gSylib (synWbr (synCpw1 A) (synCen) (synCpw1 B))
      (synWa (.classMem (synCpw1 A) (synCvv)) (.classMem (synCpw1 B) (synCvv)))
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv))) p0001 p0004
  have p0006 := @gBreq1 (.cv a) A (.cv b) (synCen)
  have p0007 := @gPw1eq (.cv a) A
  have p0008 :=
    @gBreq1d (.classEq (.cv a) A) (synCpw1 (.cv a)) (synCpw1 A) (synCpw1 (.cv b))
      (synCen) p0007
  have p0009 :=
    @gBibi12d (.classEq (.cv a) A) (synWbr (.cv a) (synCen) (.cv b))
      (synWbr A (synCen) (.cv b))
      (synWbr (synCpw1 (.cv a)) (synCen) (synCpw1 (.cv b)))
      (synWbr (synCpw1 A) (synCen) (synCpw1 (.cv b))) p0006 p0008
  have p0010 := @gBreq2 (.cv b) B A (synCen)
  have p0011 := @gPw1eq (.cv b) B
  have p0012 :=
    @gBreq2d (.classEq (.cv b) B) (synCpw1 (.cv b)) (synCpw1 B) (synCpw1 A) (synCen)
      p0011
  have p0013 :=
    @gBibi12d (.classEq (.cv b) B) (synWbr A (synCen) (.cv b)) (synWbr A (synCen) B)
      (synWbr (synCpw1 A) (synCen) (synCpw1 (.cv b)))
      (synWbr (synCpw1 A) (synCen) (synCpw1 B)) p0010 p0012
  have p0014 := @gBren (.cv a) (.cv b) f dv_cache_0001 dv_cache_0002
  have p0015 := @gF1ofun (.cv a) (.cv b) (.cv f)
  have p0016 := @gFunsi (.cv f)
  have p0017 :=
    @gSyl (synWf1o (.cv f) (.cv a) (.cv b)) (synWfun (.cv f))
      (synWfun (synCsi (.cv f))) p0015 p0016
  have p0018 := @gF1odm (.cv a) (.cv b) (.cv f)
  have p0019 := @gDmsi (.cv f)
  have p0020 := @gPw1eq (synCdm (.cv f)) (.cv a)
  have p0021 :=
    @gSyl5eq (.classEq (synCdm (.cv f)) (.cv a)) (synCdm (synCsi (.cv f)))
      (synCpw1 (synCdm (.cv f))) (synCpw1 (.cv a)) p0019 p0020
  have p0022 :=
    @gSyl (synWf1o (.cv f) (.cv a) (.cv b)) (.classEq (synCdm (.cv f)) (.cv a))
      (.classEq (synCdm (synCsi (.cv f))) (synCpw1 (.cv a))) p0018 p0021
  have p0023 := (Nominal.biimpRefl (synWfn (synCsi (.cv f)) (synCpw1 (.cv a))))
  have p0024 :=
    @gSylanbrc (synWf1o (.cv f) (.cv a) (.cv b)) (synWfun (synCsi (.cv f)))
      (.classEq (synCdm (synCsi (.cv f))) (synCpw1 (.cv a)))
      (synWfn (synCsi (.cv f)) (synCpw1 (.cv a))) p0017 p0022 p0023
  have p0025 := @gF1of1 (.cv a) (.cv b) (.cv f)
  have p0026 := (Nominal.biimpRefl (synWf1 (.cv f) (.cv a) (.cv b)))
  have p0027 :=
    @gSimprbi (synWf1 (.cv f) (.cv a) (.cv b)) (synWf (.cv f) (.cv a) (.cv b))
      (synWfun (synCcnv (.cv f))) p0026
  have p0028 := @gFunsi (synCcnv (.cv f))
  have p0029 :=
    @gN3syl (synWf1o (.cv f) (.cv a) (.cv b)) (synWf1 (.cv f) (.cv a) (.cv b))
      (synWfun (synCcnv (.cv f))) (synWfun (synCsi (synCcnv (.cv f)))) p0025 p0027
      p0028
  have p0030 := @gCnvsi (.cv f)
  have p0031 := @gFuneqi (synCcnv (synCsi (.cv f))) (synCsi (synCcnv (.cv f))) p0030
  have p0032 :=
    @gSylibr (synWf1o (.cv f) (.cv a) (.cv b)) (synWfun (synCsi (synCcnv (.cv f))))
      (synWfun (synCcnv (synCsi (.cv f)))) p0029 p0031
  have p0033 := @gF1ofo (.cv a) (.cv b) (.cv f)
  have p0034 := @gForn (.cv a) (.cv b) (.cv f)
  have p0035 := @gRnsi (.cv f)
  have p0036 := @gDfrn4 (synCsi (.cv f))
  have p0037 :=
    @gEqtr3i (synCrn (synCsi (.cv f))) (synCpw1 (synCrn (.cv f)))
      (synCdm (synCcnv (synCsi (.cv f)))) p0035 p0036
  have p0038 := @gPw1eq (synCrn (.cv f)) (.cv b)
  have p0039 :=
    @gSyl5eqr (.classEq (synCrn (.cv f)) (.cv b)) (synCdm (synCcnv (synCsi (.cv f))))
      (synCpw1 (synCrn (.cv f))) (synCpw1 (.cv b)) p0037 p0038
  have p0040 :=
    @gN3syl (synWf1o (.cv f) (.cv a) (.cv b)) (synWfo (.cv f) (.cv a) (.cv b))
      (.classEq (synCrn (.cv f)) (.cv b))
      (.classEq (synCdm (synCcnv (synCsi (.cv f)))) (synCpw1 (.cv b))) p0033 p0034
      p0039
  have p0041 :=
    (Nominal.biimpRefl (synWfn (synCcnv (synCsi (.cv f))) (synCpw1 (.cv b))))
  have p0042 :=
    @gSylanbrc (synWf1o (.cv f) (.cv a) (.cv b)) (synWfun (synCcnv (synCsi (.cv f))))
      (.classEq (synCdm (synCcnv (synCsi (.cv f)))) (synCpw1 (.cv b)))
      (synWfn (synCcnv (synCsi (.cv f))) (synCpw1 (.cv b))) p0032 p0040 p0041
  have p0043 := @gDff1o4 (synCpw1 (.cv a)) (synCpw1 (.cv b)) (synCsi (.cv f))
  have p0044 :=
    @gSylanbrc (synWf1o (.cv f) (.cv a) (.cv b))
      (synWfn (synCsi (.cv f)) (synCpw1 (.cv a)))
      (synWfn (synCcnv (synCsi (.cv f))) (synCpw1 (.cv b)))
      (synWf1o (synCsi (.cv f)) (synCpw1 (.cv a)) (synCpw1 (.cv b))) p0024 p0042 p0043
  have p0045 := @gVex f
  have p0046 := @gSiex (.cv f) p0045
  have p0047 := @gF1oen (synCpw1 (.cv a)) (synCpw1 (.cv b)) (synCsi (.cv f)) p0046
  have p0048 :=
    @gSyl (synWf1o (.cv f) (.cv a) (.cv b))
      (synWf1o (synCsi (.cv f)) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWbr (synCpw1 (.cv a)) (synCen) (synCpw1 (.cv b))) p0044 p0047
  have p0049 :=
    @gExlimiv (synWf1o (.cv f) (.cv a) (.cv b))
      (synWbr (synCpw1 (.cv a)) (synCen) (synCpw1 (.cv b))) f dv_cache_0003 p0048
  have p0050 :=
    @gSylbi (synWbr (.cv a) (synCen) (.cv b))
      (synWex f (synWf1o (.cv f) (.cv a) (.cv b)))
      (synWbr (synCpw1 (.cv a)) (synCen) (synCpw1 (.cv b))) p0014 p0049
  have p0051 :=
    @gBren (synCpw1 (.cv a)) (synCpw1 (.cv b)) g dv_cache_0004 dv_cache_0005
  have p0052 := @gF1ofun (synCpw1 (.cv a)) (synCpw1 (.cv b)) (.cv g)
  have p0053 := @gFununiq (synCsn (.cv x)) (synCsn (.cv y)) (synCsn (.cv z)) (.cv g)
  have p0054 := @gVex y
  have p0055 := @gSneqb (.cv y) (.cv z) p0054
  have p0056_e01_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv y)) (synCsn (.cv z))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0055
  have p0056 :=
    @gSylib
      (synW3a (synWfun (.cv g)) (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
        (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv z))))
      (.classEq (synCsn (.cv y)) (synCsn (.cv z))) (.objEq y z) p0053 p0056_e01_recanon
  have p0057 :=
    @gN3expib (synWfun (.cv g)) (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv z))) (.objEq y z) p0056
  have p0058 :=
    @gSyl (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b))) (synWfun (.cv g))
      (.imp (synWa (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
          (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv z)))) (.objEq y z))
      p0052 p0057
  have p0059 :=
    @gAlrimivv (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.imp (synWa (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
          (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv z)))) (.objEq y z))
      y z dv_cache_0006 dv_cache_0007 p0058
  have p0060 := @gSneq (.cv y) (.cv z)
  have p0061_e00_recanon :
    Nominal.NPrf (.imp (.objEq y z) (.classEq (synCsn (.cv y)) (synCsn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0060
  have p0061 :=
    @gBreq2d (.objEq y z) (synCsn (.cv y)) (synCsn (.cv z)) (synCsn (.cv x)) (.cv g)
      p0061_e00_recanon
  have p0062 :=
    @gMo4 (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv z))) y z dv_cache_0008
      dv_cache_0009 dv_cache_0010 p0061
  have p0063 :=
    @gSylibr (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.all y (.all z (.imp (synWa (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
              (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv z)))) (.objEq y z))))
      (synWmo y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0059 p0062
  have p0064 :=
    @gAlrimiv (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWmo y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) x dv_cache_0011
      p0063
  have p0065 :=
    @gFunopab (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))) x y dv_cache_0012
  have p0066 :=
    @gSylibr (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.all x (synWmo y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      (synWfun (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      p0064 p0065
  have p0067 :=
    @gDmopab (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))) x y dv_cache_0012
  have p0068 := @gEldm z (synCsn (.cv x)) (.cv g) dv_cache_0013 dv_cache_0014
  have p0069 := @gBrelrn (synCsn (.cv x)) (.cv z) (.cv g)
  have p0070 := @gF1ofo (synCpw1 (.cv a)) (synCpw1 (.cv b)) (.cv g)
  have p0071 := @gForn (synCpw1 (.cv a)) (synCpw1 (.cv b)) (.cv g)
  have p0072 :=
    @gSyl (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWfo (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.classEq (synCrn (.cv g)) (synCpw1 (.cv b))) p0070 p0071
  have p0073 :=
    @gEleq2d (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b))) (synCrn (.cv g))
      (synCpw1 (.cv b)) (.cv z) p0072
  have p0074 := @gElpw1 w (.cv z) (.cv b) dv_cache_0015 dv_cache_0016
  have p0075 := @gBreq2 (.cv z) (synCsn (.cv w)) (synCsn (.cv x)) (.cv g)
  have p0076 := @gVex w
  have p0077 := @gSneq (.cv y) (.cv w)
  have p0078_e00_recanon :
    Nominal.NPrf (.imp (.objEq y w) (.classEq (synCsn (.cv y)) (synCsn (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0077
  have p0078 :=
    @gBreq2d (.objEq y w) (synCsn (.cv y)) (synCsn (.cv w)) (synCsn (.cv x)) (.cv g)
      p0078_e00_recanon
  have p0079_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv w))
        (synWb (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
          (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv w))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0078
  have p0079 :=
    @gSpcev (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv w))) y (.cv w) dv_cache_0017
      dv_cache_0018 p0076 p0079_e01_recanon
  have p0080 :=
    @gSyl6bi (.classEq (.cv z) (synCsn (.cv w)))
      (synWbr (synCsn (.cv x)) (.cv g) (.cv z))
      (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv w)))
      (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0075 p0079
  have p0081 :=
    @gRexlimivw (.classEq (.cv z) (synCsn (.cv w)))
      (.imp (synWbr (synCsn (.cv x)) (.cv g) (.cv z))
        (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      w (.cv b) dv_cache_0019 p0080
  have p0082 :=
    @gSylbi (.classMem (.cv z) (synCpw1 (.cv b)))
      (synWrex w (.cv b) (.classEq (.cv z) (synCsn (.cv w))))
      (.imp (synWbr (synCsn (.cv x)) (.cv g) (.cv z))
        (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      p0074 p0081
  have p0083 :=
    @gSyl6bi (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.classMem (.cv z) (synCrn (.cv g))) (.classMem (.cv z) (synCpw1 (.cv b)))
      (.imp (synWbr (synCsn (.cv x)) (.cv g) (.cv z))
        (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      p0073 p0082
  have p0084 :=
    @gCom23 (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.classMem (.cv z) (synCrn (.cv g))) (synWbr (synCsn (.cv x)) (.cv g) (.cv z))
      (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0083
  have p0085 :=
    @gMpdi (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWbr (synCsn (.cv x)) (.cv g) (.cv z)) (.classMem (.cv z) (synCrn (.cv g)))
      (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0069 p0084
  have p0086 :=
    @gExlimdv (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWbr (synCsn (.cv x)) (.cv g) (.cv z))
      (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) z dv_cache_0020
      dv_cache_0007 p0085
  have p0087 :=
    @gSyl5bi (.classMem (synCsn (.cv x)) (synCdm (.cv g)))
      (synWex z (synWbr (synCsn (.cv x)) (.cv g) (.cv z)))
      (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0068 p0086
  have p0088 := @gBreldm (synCsn (.cv x)) (synCsn (.cv y)) (.cv g)
  have p0089 :=
    @gExlimiv (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (.classMem (synCsn (.cv x)) (synCdm (.cv g))) y dv_cache_0021 p0088
  have p0090 :=
    @gImpbid1 (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.classMem (synCsn (.cv x)) (synCdm (.cv g)))
      (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0087 p0089
  have p0091 := @gF1odm (synCpw1 (.cv a)) (synCpw1 (.cv b)) (.cv g)
  have p0092 :=
    @gEleq2d (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b))) (synCdm (.cv g))
      (synCpw1 (.cv a)) (synCsn (.cv x)) p0091
  have p0093 :=
    @gBitr3d (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.classMem (synCsn (.cv x)) (synCdm (.cv g)))
      (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
      (.classMem (synCsn (.cv x)) (synCpw1 (.cv a))) p0090 p0092
  have p0094 := @gSnelpw1 (.cv x) (.cv a)
  have p0095_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv x)) (synCpw1 (.cv a))) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn synCpw1 synCin synCcompl synCnin synWnan synWa synCpw
          synWss synC1c synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0094
  have p0095 :=
    @gSyl6bb (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
      (.classMem (synCsn (.cv x)) (synCpw1 (.cv a))) (.objMem x a) p0093
      p0095_e01_recanon
  have p0096_e00_recanon :
    Nominal.NPrf
      (.imp (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
        (synWb (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
          (.classMem (.cv x) (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWf1o synWa synWf1 synWfo synCpw1 synCin synCcompl synCnin
          synWnan synCpw synWss synC1c synWex synCsn synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0095
  have p0096 :=
    @gEqabcdv (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) x (.cv a)
      dv_cache_0022 dv_cache_0011 p0096_e00_recanon
  have p0097 :=
    @gSyl5eq (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synCdm (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      (.cab x (synWex y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))) (.cv a)
      p0067 p0096
  have p0098 :=
    (Nominal.biimpRefl
      (synWfn (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv a)))
  have p0099 :=
    @gSylanbrc (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWfun (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      (.classEq (synCdm (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
        (.cv a))
      (synWfn (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv a))
      p0066 p0097 p0098
  have p0100 := @gF1ocnv (synCpw1 (.cv a)) (synCpw1 (.cv b)) (.cv g)
  have p0101 := @gF1ofun (synCpw1 (.cv b)) (synCpw1 (.cv a)) (synCcnv (.cv g))
  have p0102 :=
    @gFununiq (synCsn (.cv y)) (synCsn (.cv x)) (synCsn (.cv z)) (synCcnv (.cv g))
  have p0103 :=
    @gN3expib (synWfun (synCcnv (.cv g)))
      (synWbr (synCsn (.cv y)) (synCcnv (.cv g)) (synCsn (.cv x)))
      (synWbr (synCsn (.cv y)) (synCcnv (.cv g)) (synCsn (.cv z)))
      (.classEq (synCsn (.cv x)) (synCsn (.cv z))) p0102
  have p0104 := @gBrcnv (synCsn (.cv y)) (synCsn (.cv x)) (.cv g)
  have p0105 := @gBrcnv (synCsn (.cv y)) (synCsn (.cv z)) (.cv g)
  have p0106 :=
    @gAnbi12i (synWbr (synCsn (.cv y)) (synCcnv (.cv g)) (synCsn (.cv x)))
      (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (synWbr (synCsn (.cv y)) (synCcnv (.cv g)) (synCsn (.cv z)))
      (synWbr (synCsn (.cv z)) (.cv g) (synCsn (.cv y))) p0104 p0105
  have p0107 := @gVex x
  have p0108 := @gSneqb (.cv x) (.cv z) p0107
  have p0109_e02_recanon :
    Nominal.NPrf (synWb (.classEq (synCsn (.cv x)) (synCsn (.cv z))) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0108
  have p0109 :=
    @gN3imtr3g (synWfun (synCcnv (.cv g)))
      (synWa (synWbr (synCsn (.cv y)) (synCcnv (.cv g)) (synCsn (.cv x)))
        (synWbr (synCsn (.cv y)) (synCcnv (.cv g)) (synCsn (.cv z))))
      (.classEq (synCsn (.cv x)) (synCsn (.cv z)))
      (synWa (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
        (synWbr (synCsn (.cv z)) (.cv g) (synCsn (.cv y))))
      (.objEq x z) p0103 p0106 p0109_e02_recanon
  have p0110 :=
    @gN3syl (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWf1o (synCcnv (.cv g)) (synCpw1 (.cv b)) (synCpw1 (.cv a)))
      (synWfun (synCcnv (.cv g)))
      (.imp (synWa (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
          (synWbr (synCsn (.cv z)) (.cv g) (synCsn (.cv y)))) (.objEq x z))
      p0100 p0101 p0109
  have p0111 :=
    @gAlrimivv (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.imp (synWa (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
          (synWbr (synCsn (.cv z)) (.cv g) (synCsn (.cv y)))) (.objEq x z))
      x z dv_cache_0011 dv_cache_0007 p0110
  have p0112 := @gSneq (.cv x) (.cv z)
  have p0113_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (synCsn (.cv x)) (synCsn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0112
  have p0113 :=
    @gBreq1d (.objEq x z) (synCsn (.cv x)) (synCsn (.cv z)) (synCsn (.cv y)) (.cv g)
      p0113_e00_recanon
  have p0114 :=
    @gMo4 (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (synWbr (synCsn (.cv z)) (.cv g) (synCsn (.cv y))) x z dv_cache_0008
      dv_cache_0023 dv_cache_0024 p0113
  have p0115 :=
    @gSylibr (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.all x (.all z (.imp (synWa (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
              (synWbr (synCsn (.cv z)) (.cv g) (synCsn (.cv y)))) (.objEq x z))))
      (synWmo x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0111 p0114
  have p0116 :=
    @gAlrimiv (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWmo x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) y dv_cache_0006
      p0115
  have p0117 :=
    @gFunopab (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))) y x dv_cache_0025
  have p0118 :=
    @gSylibr (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.all y (synWmo x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      (synWfun (synCopab y x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      p0116 p0117
  have p0119 :=
    @gDmopab (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))) y x dv_cache_0025
  have p0120 := @gElrn z (synCsn (.cv y)) (.cv g) dv_cache_0026 dv_cache_0014
  have p0121 := @gBreldm (.cv z) (synCsn (.cv y)) (.cv g)
  have p0122 :=
    @gEleq2d (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b))) (synCdm (.cv g))
      (synCpw1 (.cv a)) (.cv z) p0091
  have p0123 := @gElpw1 w (.cv z) (.cv a) dv_cache_0015 dv_cache_0027
  have p0124 := @gBreq1 (.cv z) (synCsn (.cv w)) (synCsn (.cv y)) (.cv g)
  have p0125 := @gSneq (.cv x) (.cv w)
  have p0126_e00_recanon :
    Nominal.NPrf (.imp (.objEq x w) (.classEq (synCsn (.cv x)) (synCsn (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0125
  have p0126 :=
    @gBreq1d (.objEq x w) (synCsn (.cv x)) (synCsn (.cv w)) (synCsn (.cv y)) (.cv g)
      p0126_e00_recanon
  have p0127_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv w))
        (synWb (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
          (synWbr (synCsn (.cv w)) (.cv g) (synCsn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWbr synCop synCun synCnin synWnan synWa synCcompl synWrex
          synWex synCphi synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0126
  have p0127 :=
    @gSpcev (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (synWbr (synCsn (.cv w)) (.cv g) (synCsn (.cv y))) x (.cv w) dv_cache_0028
      dv_cache_0029 p0076 p0127_e01_recanon
  have p0128 :=
    @gSyl6bi (.classEq (.cv z) (synCsn (.cv w)))
      (synWbr (.cv z) (.cv g) (synCsn (.cv y)))
      (synWbr (synCsn (.cv w)) (.cv g) (synCsn (.cv y)))
      (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0124 p0127
  have p0129 :=
    @gRexlimivw (.classEq (.cv z) (synCsn (.cv w)))
      (.imp (synWbr (.cv z) (.cv g) (synCsn (.cv y)))
        (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      w (.cv a) dv_cache_0030 p0128
  have p0130 :=
    @gSylbi (.classMem (.cv z) (synCpw1 (.cv a)))
      (synWrex w (.cv a) (.classEq (.cv z) (synCsn (.cv w))))
      (.imp (synWbr (.cv z) (.cv g) (synCsn (.cv y)))
        (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      p0123 p0129
  have p0131 :=
    @gSyl6bi (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.classMem (.cv z) (synCdm (.cv g))) (.classMem (.cv z) (synCpw1 (.cv a)))
      (.imp (synWbr (.cv z) (.cv g) (synCsn (.cv y)))
        (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      p0122 p0130
  have p0132 :=
    @gCom23 (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.classMem (.cv z) (synCdm (.cv g))) (synWbr (.cv z) (.cv g) (synCsn (.cv y)))
      (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0131
  have p0133 :=
    @gMpdi (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWbr (.cv z) (.cv g) (synCsn (.cv y))) (.classMem (.cv z) (synCdm (.cv g)))
      (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0121 p0132
  have p0134 :=
    @gExlimdv (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWbr (.cv z) (.cv g) (synCsn (.cv y)))
      (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) z dv_cache_0031
      dv_cache_0007 p0133
  have p0135 :=
    @gSyl5bi (.classMem (synCsn (.cv y)) (synCrn (.cv g)))
      (synWex z (synWbr (.cv z) (.cv g) (synCsn (.cv y))))
      (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0120 p0134
  have p0136 := @gBrelrn (synCsn (.cv x)) (synCsn (.cv y)) (.cv g)
  have p0137 :=
    @gExlimiv (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))
      (.classMem (synCsn (.cv y)) (synCrn (.cv g))) x dv_cache_0032 p0136
  have p0138 :=
    @gImpbid1 (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.classMem (synCsn (.cv y)) (synCrn (.cv g)))
      (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0135 p0137
  have p0139 :=
    @gEleq2d (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b))) (synCrn (.cv g))
      (synCpw1 (.cv b)) (synCsn (.cv y)) p0072
  have p0140 :=
    @gBitr3d (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (.classMem (synCsn (.cv y)) (synCrn (.cv g)))
      (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
      (.classMem (synCsn (.cv y)) (synCpw1 (.cv b))) p0138 p0139
  have p0141 := @gSnelpw1 (.cv y) (.cv b)
  have p0142_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCsn (.cv y)) (synCpw1 (.cv b))) (.objMem y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCsn synCpw1 synCin synCcompl synCnin synWnan synWa synCpw
          synWss synC1c synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0141
  have p0142 :=
    @gSyl6bb (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
      (.classMem (synCsn (.cv y)) (synCpw1 (.cv b))) (.objMem y b) p0140
      p0142_e01_recanon
  have p0143_e00_recanon :
    Nominal.NPrf
      (.imp (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
        (synWb (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
          (.classMem (.cv y) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWf1o synWa synWf1 synWfo synCpw1 synCin synCcompl synCnin
          synWnan synCpw synWss synC1c synWex synCsn synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0142
  have p0143 :=
    @gEqabcdv (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) y (.cv b)
      dv_cache_0033 dv_cache_0006 p0143_e00_recanon
  have p0144 :=
    @gSyl5eq (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synCdm (synCopab y x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      (.cab y (synWex x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))) (.cv b)
      p0119 p0143
  have p0145 :=
    (Nominal.biimpRefl
      (synWfn (synCopab y x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv b)))
  have p0146 :=
    @gSylanbrc (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWfun (synCopab y x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      (.classEq (synCdm (synCopab y x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
        (.cv b))
      (synWfn (synCopab y x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv b))
      p0118 p0144 p0145
  have p0147 :=
    @gCnvopab (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))) x y dv_cache_0012
  have p0148 :=
    @gFneq1i (.cv b)
      (synCcnv (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
      (synCopab y x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0147
  have p0149 :=
    @gSylibr (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWfn (synCopab y x (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv b))
      (synWfn (synCcnv (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
        (.cv b))
      p0146 p0148
  have p0150 :=
    @gDff1o4 (.cv a) (.cv b)
      (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
  have p0151 :=
    @gSylanbrc (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWfn (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) (.cv a))
      (synWfn (synCcnv (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))))
        (.cv b))
      (synWf1o (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
        (.cv a) (.cv b))
      p0099 p0149 p0150
  have p0152 := @gEnpw1lem1 x y g dv_cache_0034 dv_cache_0035 dv_cache_0012
  have p0153 :=
    @gF1oen (.cv a) (.cv b)
      (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y)))) p0152
  have p0154 :=
    @gSyl (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWf1o (synCopab x y (synWbr (synCsn (.cv x)) (.cv g) (synCsn (.cv y))))
        (.cv a) (.cv b))
      (synWbr (.cv a) (synCen) (.cv b)) p0151 p0153
  have p0155 :=
    @gExlimiv (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b)))
      (synWbr (.cv a) (synCen) (.cv b)) g dv_cache_0036 p0154
  have p0156 :=
    @gSylbi (synWbr (synCpw1 (.cv a)) (synCen) (synCpw1 (.cv b)))
      (synWex g (synWf1o (.cv g) (synCpw1 (.cv a)) (synCpw1 (.cv b))))
      (synWbr (.cv a) (synCen) (.cv b)) p0051 p0155
  have p0157 :=
    @gImpbii (synWbr (.cv a) (synCen) (.cv b))
      (synWbr (synCpw1 (.cv a)) (synCen) (synCpw1 (.cv b))) p0050 p0156
  have p0158 :=
    @gVtocl2g
      (synWb (synWbr (.cv a) (synCen) (.cv b))
        (synWbr (synCpw1 (.cv a)) (synCen) (synCpw1 (.cv b))))
      (synWb (synWbr A (synCen) (.cv b)) (synWbr (synCpw1 A) (synCen) (synCpw1 (.cv b))))
      (synWb (synWbr A (synCen) B) (synWbr (synCpw1 A) (synCen) (synCpw1 B))) a b A
      B (synCvv) (synCvv) dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
      dv_cache_0041 p0009 p0013 p0157
  have p0159 :=
    @gPm521nii (synWbr A (synCen) B)
      (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWbr (synCpw1 A) (synCen) (synCpw1 B)) p0000 p0005 p0158
  exact p0159


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part036`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_enmap2lem1`. -/
@[expose]
noncomputable def gEnmap2lem1 (A : Class) (G : Class) (W : Class) (s : Var) (r : Var)
    (dv_A_s : s ∉ A.fv) (dv_G_s : s ∉ G.fv) (dv_r_s : r ≠ s)
    (hyp_enmap2lem1_1 : Nominal.NPrf (.classEq W
          (synCmpt s (synCo G (synCmap) A) (synCcom (.cv s) (synCcnv (.cv r)))))) :
    Nominal.NPrf (.classMem W (synCvv)) :=
  by
  let proofSupport : Finset Var :=
    A.fv ∪ G.fv ∪ W.fv ∪ ({ s } : Finset Var) ∪ ({ r } : Finset Var)
  let x : Var := freshVar proofSupport 0
  let p : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_x_ne_s : x ≠ s := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_s_ne_x : s ≠ x := Ne.symm fresh_x_ne_s
  have fresh_x_ne_r : x ≠ r := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_p_ne_s : p ≠ s := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have dv_cache_0001 : x ∉ ((synCo G (synCmap) A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union,
          fresh_x_not_G, fresh_x_not_A, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCcom (.cv s) (synCcnv (.cv r)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_s, fresh_x_ne_r, or_false, not_false_eq_true])
  have dv_cache_0003 : s ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show s ≠ x from (by exact fresh_s_ne_x))
  have dv_cache_0004 : x ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_p, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv s)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_s, not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
            (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synC1st)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synCop (.cv s) (synCcnv (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_s, fresh_x_ne_r, or_false, not_false_eq_true])
  have dv_cache_0009 :
    x ∉ ((synWbr (.cv p) (synC1st) (synCop (.cv s) (synCcnv (.cv r))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_p, fresh_x_ne_s, fresh_x_ne_r,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : p ∉ ((synCop (.cv s) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_s, fresh_p_ne_x, or_false, not_false_eq_true])
  have dv_cache_0011 :
    p ∉
      ((synCtxp (synCcom (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
            (synC1st)) (synC2nd))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_r, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 : p ∉ ((synCcompose)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompose,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((synCop (synCop (.cv s) (synCcnv (.cv r))) (.cv x))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_s, fresh_p_ne_r, fresh_p_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    s ∉
      ((synCres (synCima (synCtxp (synCcom (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                    (synCvv))) (synC1st)) (synC2nd)) (synCcompose))
          (synCo G (synCmap) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompose,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_r_s), dv_G_s, dv_A_s,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    x ∉
      ((synCres (synCima (synCtxp (synCcom (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                    (synCvv))) (synC1st)) (synC2nd)) (synCcompose))
          (synCo G (synCmap) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompose,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_r, fresh_x_not_G, fresh_x_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMpt s x
      (synCo G (synCmap) A) (synCcom (.cv s) (synCcnv (.cv r))) dv_cache_0001
      dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gOpelres (.cv s) (.cv x)
      (synCima (synCtxp (synCcom (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
            (synC1st)) (synC2nd)) (synCcompose))
      (synCo G (synCmap) A)
  have p0002 :=
    @gTrtxp (.cv p) (.cv s) (.cv x)
      (synCcom (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
        (synC1st))
      (synC2nd)
  have p0003 :=
    @gBrco x (.cv p) (.cv s)
      (synCin (synC1st)
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
      (synC1st) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @gAncom (synWbr (.cv p) (synC1st) (.cv x))
      (synWbr (.cv x) (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
        (.cv s))
  have p0005 :=
    @gBrin (.cv x) (.cv s) (synC1st)
      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv))
  have p0006 := @gVex s
  have p0007 :=
    @gBrxp (.cv x) (.cv s) (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
      (synCvv)
  have p0008 :=
    @gMpbiran2
      (synWbr (.cv x)
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv))
        (.cv s))
      (.classMem (.cv x) (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))))
      (.classMem (.cv s) (synCvv)) p0006 p0007
  have p0009 := @gEliniseg (synC2nd) (synCcnv (.cv r)) (.cv x)
  have p0010 :=
    @gBitri
      (synWbr (.cv x)
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv))
        (.cv s))
      (.classMem (.cv x) (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))))
      (synWbr (.cv x) (synC2nd) (synCcnv (.cv r))) p0008 p0009
  have p0011 :=
    @gAnbi2i
      (synWbr (.cv x)
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv))
        (.cv s))
      (synWbr (.cv x) (synC2nd) (synCcnv (.cv r))) (synWbr (.cv x) (synC1st) (.cv s))
      p0010
  have p0012 := @gVex r
  have p0013 := @gCnvex (.cv r) p0012
  have p0014 := @gOp1st2nd (.cv s) (synCcnv (.cv r)) (.cv x) p0006 p0013
  have p0015 :=
    @gN3bitri
      (synWbr (.cv x) (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
        (.cv s))
      (synWa (synWbr (.cv x) (synC1st) (.cv s)) (synWbr (.cv x)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv))
          (.cv s)))
      (synWa (synWbr (.cv x) (synC1st) (.cv s))
        (synWbr (.cv x) (synC2nd) (synCcnv (.cv r))))
      (.classEq (.cv x) (synCop (.cv s) (synCcnv (.cv r)))) p0005 p0011 p0014
  have p0016 :=
    @gAnbi1i
      (synWbr (.cv x) (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
        (.cv s))
      (.classEq (.cv x) (synCop (.cv s) (synCcnv (.cv r))))
      (synWbr (.cv p) (synC1st) (.cv x)) p0015
  have p0017 :=
    @gBitri
      (synWa (synWbr (.cv p) (synC1st) (.cv x)) (synWbr (.cv x) (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
          (.cv s)))
      (synWa (synWbr (.cv x) (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
          (.cv s)) (synWbr (.cv p) (synC1st) (.cv x)))
      (synWa (.classEq (.cv x) (synCop (.cv s) (synCcnv (.cv r))))
        (synWbr (.cv p) (synC1st) (.cv x)))
      p0004 p0016
  have p0018 :=
    @gExbii
      (synWa (synWbr (.cv p) (synC1st) (.cv x)) (synWbr (.cv x) (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
          (.cv s)))
      (synWa (.classEq (.cv x) (synCop (.cv s) (synCcnv (.cv r))))
        (synWbr (.cv p) (synC1st) (.cv x)))
      x p0017
  have p0019 := @gOpex (.cv s) (synCcnv (.cv r)) p0006 p0013
  have p0020 := @gBreq2 (.cv x) (synCop (.cv s) (synCcnv (.cv r))) (.cv p) (synC1st)
  have p0021 :=
    @gCeqsexv (synWbr (.cv p) (synC1st) (.cv x))
      (synWbr (.cv p) (synC1st) (synCop (.cv s) (synCcnv (.cv r)))) x
      (synCop (.cv s) (synCcnv (.cv r))) dv_cache_0008 dv_cache_0009 p0019 p0020
  have p0022 :=
    @gN3bitri
      (synWbr (.cv p) (synCcom (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
          (synC1st)) (.cv s))
      (synWex x (synWa (synWbr (.cv p) (synC1st) (.cv x)) (synWbr (.cv x)
            (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
            (.cv s))))
      (synWex x (synWa (.classEq (.cv x) (synCop (.cv s) (synCcnv (.cv r))))
          (synWbr (.cv p) (synC1st) (.cv x))))
      (synWbr (.cv p) (synC1st) (synCop (.cv s) (synCcnv (.cv r)))) p0003 p0018 p0021
  have p0023 :=
    @gAnbi1i
      (synWbr (.cv p) (synCcom (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
          (synC1st)) (.cv s))
      (synWbr (.cv p) (synC1st) (synCop (.cv s) (synCcnv (.cv r))))
      (synWbr (.cv p) (synC2nd) (.cv x)) p0022
  have p0024 := @gVex x
  have p0025 :=
    @gOp1st2nd (synCop (.cv s) (synCcnv (.cv r))) (.cv x) (.cv p) p0019 p0024
  have p0026 :=
    @gN3bitri
      (synWbr (.cv p) (synCtxp (synCcom (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
            (synC1st)) (synC2nd)) (synCop (.cv s) (.cv x)))
      (synWa (synWbr (.cv p) (synCcom (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
            (synC1st)) (.cv s)) (synWbr (.cv p) (synC2nd) (.cv x)))
      (synWa (synWbr (.cv p) (synC1st) (synCop (.cv s) (synCcnv (.cv r))))
        (synWbr (.cv p) (synC2nd) (.cv x)))
      (.classEq (.cv p) (synCop (synCop (.cv s) (synCcnv (.cv r))) (.cv x))) p0002
      p0023 p0025
  have p0027 :=
    @gRexbii
      (synWbr (.cv p) (synCtxp (synCcom (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
            (synC1st)) (synC2nd)) (synCop (.cv s) (.cv x)))
      (.classEq (.cv p) (synCop (synCop (.cv s) (synCcnv (.cv r))) (.cv x))) p
      (synCcompose) p0026
  have p0028 :=
    @gElima p (synCop (.cv s) (.cv x))
      (synCtxp (synCcom (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
          (synC1st)) (synC2nd))
      (synCcompose) dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0029 :=
    @gRisset p (synCop (synCop (.cv s) (synCcnv (.cv r))) (.cv x)) (synCcompose)
      dv_cache_0013 dv_cache_0012
  have p0030 :=
    @gN3bitr4i
      (synWrex p (synCcompose) (synWbr (.cv p) (synCtxp (synCcom (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                  (synCvv))) (synC1st)) (synC2nd)) (synCop (.cv s) (.cv x))))
      (synWrex p (synCcompose)
        (.classEq (.cv p) (synCop (synCop (.cv s) (synCcnv (.cv r))) (.cv x))))
      (.classMem (synCop (.cv s) (.cv x)) (synCima (synCtxp (synCcom (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                  (synCvv))) (synC1st)) (synC2nd)) (synCcompose)))
      (.classMem (synCop (synCop (.cv s) (synCcnv (.cv r))) (.cv x)) (synCcompose))
      p0027 p0028 p0029
  have p0031 :=
    (Nominal.biimpRefl (synWbr (synCop (.cv s) (synCcnv (.cv r))) (synCcompose) (.cv x)))
  have p0032 := @gBrcomposeg (.cv s) (synCcnv (.cv r)) (.cv x) (synCvv) (synCvv)
  have p0033 :=
    @gMp2an (.classMem (.cv s) (synCvv)) (.classMem (synCcnv (.cv r)) (synCvv))
      (synWb (synWbr (synCop (.cv s) (synCcnv (.cv r))) (synCcompose) (.cv x))
        (.classEq (synCcom (.cv s) (synCcnv (.cv r))) (.cv x)))
      p0006 p0013 p0032
  have p0034 := @gEqcom (synCcom (.cv s) (synCcnv (.cv r))) (.cv x)
  have p0035 :=
    @gBitri (synWbr (synCop (.cv s) (synCcnv (.cv r))) (synCcompose) (.cv x))
      (.classEq (synCcom (.cv s) (synCcnv (.cv r))) (.cv x))
      (.classEq (.cv x) (synCcom (.cv s) (synCcnv (.cv r)))) p0033 p0034
  have p0036 :=
    @gN3bitr2i
      (.classMem (synCop (.cv s) (.cv x)) (synCima (synCtxp (synCcom (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                  (synCvv))) (synC1st)) (synC2nd)) (synCcompose)))
      (.classMem (synCop (synCop (.cv s) (synCcnv (.cv r))) (.cv x)) (synCcompose))
      (synWbr (synCop (.cv s) (synCcnv (.cv r))) (synCcompose) (.cv x))
      (.classEq (.cv x) (synCcom (.cv s) (synCcnv (.cv r)))) p0030 p0031 p0035
  have p0037 :=
    @gAnbi2ci
      (.classMem (synCop (.cv s) (.cv x)) (synCima (synCtxp (synCcom (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                  (synCvv))) (synC1st)) (synC2nd)) (synCcompose)))
      (.classEq (.cv x) (synCcom (.cv s) (synCcnv (.cv r))))
      (.classMem (.cv s) (synCo G (synCmap) A)) p0036
  have p0038 :=
    @gBitri
      (.classMem (synCop (.cv s) (.cv x)) (synCres (synCima (synCtxp (synCcom
                (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                    (synCvv))) (synC1st)) (synC2nd)) (synCcompose))
          (synCo G (synCmap) A)))
      (synWa (.classMem (synCop (.cv s) (.cv x)) (synCima (synCtxp (synCcom
                (synCin (synC1st)
                  (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                    (synCvv))) (synC1st)) (synC2nd)) (synCcompose)))
        (.classMem (.cv s) (synCo G (synCmap) A)))
      (synWa (.classMem (.cv s) (synCo G (synCmap) A))
        (.classEq (.cv x) (synCcom (.cv s) (synCcnv (.cv r)))))
      p0001 p0037
  have p0039 :=
    @gOpabbi2i
      (synWa (.classMem (.cv s) (synCo G (synCmap) A))
        (.classEq (.cv x) (synCcom (.cv s) (synCcnv (.cv r)))))
      s x
      (synCres (synCima (synCtxp (synCcom (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                  (synCvv))) (synC1st)) (synC2nd)) (synCcompose)) (synCo G (synCmap) A))
      dv_cache_0014 dv_cache_0015 dv_cache_0003 p0038
  have p0040 :=
    @gN3eqtr4i
      (synCmpt s (synCo G (synCmap) A) (synCcom (.cv s) (synCcnv (.cv r))))
      (synCopab s x (synWa (.classMem (.cv s) (synCo G (synCmap) A))
          (.classEq (.cv x) (synCcom (.cv s) (synCcnv (.cv r))))))
      W
      (synCres (synCima (synCtxp (synCcom (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                  (synCvv))) (synC1st)) (synC2nd)) (synCcompose)) (synCo G (synCmap) A))
      p0000 hyp_enmap2lem1_1 p0039
  have p0041 := @gN1stex
  have p0042 := @gN2ndex
  have p0043 := @gCnvex (synC2nd) p0042
  have p0044 := @gSnex (synCcnv (.cv r))
  have p0045 := @gImaex (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))) p0043 p0044
  have p0046 := @gVvex
  have p0047 :=
    @gXpex (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv) p0045
      p0046
  have p0048 :=
    @gInex (synC1st)
      (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv))
      p0041 p0047
  have p0050 :=
    @gCoex
      (synCin (synC1st)
        (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
      (synC1st) p0048 p0041
  have p0052 :=
    @gTxpex
      (synCcom (synCin (synC1st)
          (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
        (synC1st))
      (synC2nd) p0050 p0042
  have p0053 := @gComposeex
  have p0054 :=
    @gImaex
      (synCtxp (synCcom (synCin (synC1st)
            (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
          (synC1st)) (synC2nd))
      (synCcompose) p0052 p0053
  have p0055 := @gOvex G A (synCmap)
  have p0056 :=
    @gResex
      (synCima (synCtxp (synCcom (synCin (synC1st)
              (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r)))) (synCvv)))
            (synC1st)) (synC2nd)) (synCcompose))
      (synCo G (synCmap) A) p0054 p0055
  have p0057 :=
    @gEqeltri W
      (synCres (synCima (synCtxp (synCcom (synCin (synC1st)
                (synCxp (synCima (synCcnv (synC2nd)) (synCsn (synCcnv (.cv r))))
                  (synCvv))) (synC1st)) (synC2nd)) (synCcompose)) (synCo G (synCmap) A))
      (synCvv) p0040 p0056
  exact p0057

/-- Checked nominal proof certificate identified upstream as `g_enmap2lem2`. -/
@[expose]
noncomputable def gEnmap2lem2 (G : Class) (W : Class) (s : Var) (r : Var) (a : Var)
    (dv_G_s : s ∉ G.fv) (dv_a_s : a ≠ s)
    (hyp_enmap2lem2_1 : Nominal.NPrf (.classEq W (synCmpt s (synCo G (synCmap) (.cv a))
            (synCcom (.cv s) (synCcnv (.cv r)))))) :
    Nominal.NPrf (synWfn W (synCo G (synCmap) (.cv a))) :=
  by
  have dv_cache_0001 : s ∉ ((synCo G (synCmap) (.cv a))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_G_s, (Ne.symm dv_a_s), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    @gFnmpt s (synCo G (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r))) W
      (synCvv) dv_cache_0001 hyp_enmap2lem2_1
  have p0001 := @gVex s
  have p0002 := @gVex r
  have p0003 := @gCnvex (.cv r) p0002
  have p0004 := @gCoex (.cv s) (synCcnv (.cv r)) p0001 p0003
  have p0005 :=
    @gA1i (.classMem (synCcom (.cv s) (synCcnv (.cv r))) (synCvv))
      (.classMem (.cv s) (synCo G (synCmap) (.cv a))) p0004
  have p0006 :=
    @gMprg (.classMem (synCcom (.cv s) (synCcnv (.cv r))) (synCvv))
      (synWfn W (synCo G (synCmap) (.cv a))) s (synCo G (synCmap) (.cv a)) p0000
      p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_enmap2lem3`. -/
@[expose]
noncomputable def gEnmap2lem3 (S : Class) (T : Class) (G : Class) (W : Class) (s : Var)
    (r : Var) (a : Var) (b : Var) (dv_G_s : s ∉ G.fv) (dv_S_s : s ∉ S.fv) (dv_a_s : a ≠ s)
    (dv_r_s : r ≠ s)
    (hyp_enmap2lem3_1 : Nominal.NPrf (.classEq W (synCmpt s (synCo G (synCmap) (.cv a))
            (synCcom (.cv s) (synCcnv (.cv r)))))) :
    Nominal.NPrf
      (.imp (synWf1o (.cv r) (.cv a) (.cv b))
        (.imp (synWbr S W T) (.classEq S (synCcom T (.cv r))))) :=
  by
  have dv_cache_0001 : s ∉ (G).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_s, not_false_eq_true])
  have dv_cache_0002 : a ≠ s := by
    clear dv_cache_0001
    exact (show a ≠ s from (by exact dv_a_s))
  have dv_cache_0003 : s ∉ (S).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_S_s, not_false_eq_true])
  have dv_cache_0004 : s ∉ ((synCcom S (synCcnv (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_S_s, (Ne.symm dv_r_s), or_false, not_false_eq_true])
  have dv_cache_0005 : s ∉ ((synCo G (synCmap) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_G_s, (Ne.symm dv_a_s), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := @gBreldm S T W
  have p0001 := @gEnmap2lem2 G W s r a dv_cache_0001 dv_cache_0002 hyp_enmap2lem3_1
  have p0002 := @gFndm (synCo G (synCmap) (.cv a)) W
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gSyl6eleq (synWbr S W T) S (synCdm W) (synCo G (synCmap) (.cv a)) p0000 p0003
  have p0005 := @gFnbrfvb (synCo G (synCmap) (.cv a)) S T W
  have p0006 :=
    @gMpan (synWfn W (synCo G (synCmap) (.cv a)))
      (.classMem S (synCo G (synCmap) (.cv a)))
      (synWb (.classEq (synCfv W S) T) (synWbr S W T)) p0001 p0005
  have p0007 := @gVex r
  have p0008 := @gCnvex (.cv r) p0007
  have p0009 := @gCoexg S (synCcnv (.cv r)) (synCo G (synCmap) (.cv a)) (synCvv)
  have p0010 :=
    @gMpan2 (.classMem S (synCo G (synCmap) (.cv a)))
      (.classMem (synCcnv (.cv r)) (synCvv))
      (.classMem (synCcom S (synCcnv (.cv r))) (synCvv)) p0008 p0009
  have p0011 := @gCoeq1 (.cv s) S (synCcnv (.cv r))
  have p0012 :=
    @gFvmptg s S (synCcom (.cv s) (synCcnv (.cv r))) (synCcom S (synCcnv (.cv r)))
      (synCo G (synCmap) (.cv a)) (synCvv) W dv_cache_0003 dv_cache_0004 dv_cache_0005
      p0011 hyp_enmap2lem3_1
  have p0013 :=
    @gMpdan (.classMem S (synCo G (synCmap) (.cv a)))
      (.classMem (synCcom S (synCcnv (.cv r))) (synCvv))
      (.classEq (synCfv W S) (synCcom S (synCcnv (.cv r)))) p0010 p0012
  have p0014 :=
    @gEqeq1d (.classMem S (synCo G (synCmap) (.cv a))) (synCfv W S)
      (synCcom S (synCcnv (.cv r))) T p0013
  have p0015 := @gEqcom (synCcom S (synCcnv (.cv r))) T
  have p0016 :=
    @gSyl6bb (.classMem S (synCo G (synCmap) (.cv a))) (.classEq (synCfv W S) T)
      (.classEq (synCcom S (synCcnv (.cv r))) T)
      (.classEq T (synCcom S (synCcnv (.cv r)))) p0014 p0015
  have p0017 :=
    @gBiimpd (.classMem S (synCo G (synCmap) (.cv a))) (.classEq (synCfv W S) T)
      (.classEq T (synCcom S (synCcnv (.cv r)))) p0016
  have p0018 :=
    @gSylbird (.classMem S (synCo G (synCmap) (.cv a))) (synWbr S W T)
      (.classEq (synCfv W S) T) (.classEq T (synCcom S (synCcnv (.cv r)))) p0006 p0017
  have p0019 :=
    @gMpcom (.classMem S (synCo G (synCmap) (.cv a))) (synWbr S W T)
      (.classEq T (synCcom S (synCcnv (.cv r)))) p0004 p0018
  have p0020 :=
    @gJca (synWbr S W T) (.classMem S (synCo G (synCmap) (.cv a)))
      (.classEq T (synCcom S (synCcnv (.cv r)))) p0004 p0019
  have p0021 := @gF1ococnv1 (.cv a) (.cv b) (.cv r)
  have p0022 :=
    @gCoeq2d (synWf1o (.cv r) (.cv a) (.cv b)) (synCcom (synCcnv (.cv r)) (.cv r))
      (synCres (synCid) (.cv a)) S p0021
  have p0023 :=
    @gAdantr (synWf1o (.cv r) (.cv a) (.cv b))
      (.classEq (synCcom S (synCcom (synCcnv (.cv r)) (.cv r)))
        (synCcom S (synCres (synCid) (.cv a))))
      (.classMem S (synCo G (synCmap) (.cv a))) p0022
  have p0024 := @gElmapi S G (.cv a)
  have p0025 := @gFcoi1 (.cv a) G S
  have p0026 :=
    @gSyl (.classMem S (synCo G (synCmap) (.cv a))) (synWf S (.cv a) G)
      (.classEq (synCcom S (synCres (synCid) (.cv a))) S) p0024 p0025
  have p0027 :=
    @gAdantl (.classMem S (synCo G (synCmap) (.cv a)))
      (.classEq (synCcom S (synCres (synCid) (.cv a))) S)
      (synWf1o (.cv r) (.cv a) (.cv b)) p0026
  have p0028 :=
    @gEqtr2d
      (synWa (synWf1o (.cv r) (.cv a) (.cv b)) (.classMem S (synCo G (synCmap) (.cv a))))
      (synCcom S (synCcom (synCcnv (.cv r)) (.cv r)))
      (synCcom S (synCres (synCid) (.cv a))) S p0023 p0027
  have p0029 := @gCoeq1 T (synCcom S (synCcnv (.cv r))) (.cv r)
  have p0030 := @gCoass S (synCcnv (.cv r)) (.cv r)
  have p0031 :=
    @gSyl6eq (.classEq T (synCcom S (synCcnv (.cv r)))) (synCcom T (.cv r))
      (synCcom (synCcom S (synCcnv (.cv r))) (.cv r))
      (synCcom S (synCcom (synCcnv (.cv r)) (.cv r))) p0029 p0030
  have p0032 :=
    @gEqeq2d (.classEq T (synCcom S (synCcnv (.cv r)))) (synCcom T (.cv r))
      (synCcom S (synCcom (synCcnv (.cv r)) (.cv r))) S p0031
  have p0033 :=
    @gSyl5ibrcom
      (synWa (synWf1o (.cv r) (.cv a) (.cv b)) (.classMem S (synCo G (synCmap) (.cv a))))
      (.classEq S (synCcom T (.cv r))) (.classEq T (synCcom S (synCcnv (.cv r))))
      (.classEq S (synCcom S (synCcom (synCcnv (.cv r)) (.cv r)))) p0028 p0032
  have p0034 :=
    @gExpimpd (synWf1o (.cv r) (.cv a) (.cv b))
      (.classMem S (synCo G (synCmap) (.cv a)))
      (.classEq T (synCcom S (synCcnv (.cv r)))) (.classEq S (synCcom T (.cv r))) p0033
  have p0035 :=
    @gSyl5 (synWbr S W T)
      (synWa (.classMem S (synCo G (synCmap) (.cv a)))
        (.classEq T (synCcom S (synCcnv (.cv r)))))
      (synWf1o (.cv r) (.cv a) (.cv b)) (.classEq S (synCcom T (.cv r))) p0020 p0034
  exact p0035

/-- Checked nominal proof certificate identified upstream as `g_enmap2lem4`. -/
@[expose]
noncomputable def gEnmap2lem4 (G : Class) (W : Class) (s : Var) (r : Var) (a : Var)
    (b : Var) (dv_G_s : s ∉ G.fv) (dv_a_s : a ≠ s) (dv_r_s : r ≠ s)
    (hyp_enmap2lem4_1 : Nominal.NPrf (.classEq W (synCmpt s (synCo G (synCmap) (.cv a))
            (synCcom (.cv s) (synCcnv (.cv r)))))) :
    Nominal.NPrf (.imp (synWf1o (.cv r) (.cv a) (.cv b)) (synWfun (synCcnv W))) :=
  by
  let proofSupport : Finset Var :=
    G.fv ∪ W.fv ∪ ({ s } : Finset Var) ∪ ({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪
      ({ b } : Finset Var)
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_W : y ∉ W.fv := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_y_ne_s : y ≠ s := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_s_ne_y : s ≠ y := Ne.symm fresh_y_ne_s
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_a : y ≠ a := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_b : y ≠ b := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_W : x ∉ W.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_x_ne_r : x ≠ r := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_a : x ≠ a := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_b : x ≠ b := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_W : z ∉ W.fv := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_z_ne_s : z ≠ s := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_s_ne_z : s ≠ z := Ne.symm fresh_z_ne_s
  have fresh_z_ne_r : z ≠ r := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_a : z ≠ a := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_b : z ≠ b := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : s ∉ (G).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_s, not_false_eq_true])
  have dv_cache_0002 : s ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_s_ne_y, not_false_eq_true])
  have dv_cache_0003 : a ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ s from (by exact dv_a_s))
  have dv_cache_0004 : r ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show r ≠ s from (by exact dv_r_s))
  have dv_cache_0005 : s ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_s_ne_z, not_false_eq_true])
  have dv_cache_0006 : z ∉ ((synWf1o (.cv r) (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_b, fresh_z_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((synWf1o (.cv r) (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, fresh_x_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synWf1o (.cv r) (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_a, fresh_y_ne_b, fresh_y_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0009 : x ∉ ((synCcnv W)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_x_not_W,
          not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synCcnv W)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_y_not_W,
          not_false_eq_true])
  have dv_cache_0011 : z ∉ ((synCcnv W)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, fresh_z_not_W,
          not_false_eq_true])
  have dv_cache_0012 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0013 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0014 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 :=
    @gEnmap2lem3 (.cv y) (.cv x) G W s r a b dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 hyp_enmap2lem4_1
  have p0001 :=
    @gEnmap2lem3 (.cv z) (.cv x) G W s r a b dv_cache_0001 dv_cache_0005 dv_cache_0003
      dv_cache_0004 hyp_enmap2lem4_1
  have p0002 :=
    @gAnim12d (synWf1o (.cv r) (.cv a) (.cv b)) (synWbr (.cv y) W (.cv x))
      (.classEq (.cv y) (synCcom (.cv x) (.cv r))) (synWbr (.cv z) W (.cv x))
      (.classEq (.cv z) (synCcom (.cv x) (.cv r))) p0000 p0001
  have p0003 := @gEqtr3 (.cv y) (.cv z) (synCcom (.cv x) (.cv r))
  have p0004_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv y) (synCcom (.cv x) (.cv r)))
          (.classEq (.cv z) (synCcom (.cv x) (.cv r)))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCcom synCopab synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0003
  have p0004 :=
    @gSyl6 (synWf1o (.cv r) (.cv a) (.cv b))
      (synWa (synWbr (.cv y) W (.cv x)) (synWbr (.cv z) W (.cv x)))
      (synWa (.classEq (.cv y) (synCcom (.cv x) (.cv r)))
        (.classEq (.cv z) (synCcom (.cv x) (.cv r))))
      (.objEq y z) p0002 p0004_e01_recanon
  have p0005 :=
    @gAlrimiv (synWf1o (.cv r) (.cv a) (.cv b))
      (.imp (synWa (synWbr (.cv y) W (.cv x)) (synWbr (.cv z) W (.cv x))) (.objEq y z))
      z dv_cache_0006 p0004
  have p0006 :=
    @gAlrimivv (synWf1o (.cv r) (.cv a) (.cv b))
      (.all z (.imp (synWa (synWbr (.cv y) W (.cv x)) (synWbr (.cv z) W (.cv x)))
          (.objEq y z)))
      x y dv_cache_0007 dv_cache_0008 p0005
  have p0007 :=
    @gDffun2 x y z (synCcnv W) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014
  have p0008 := @gBrcnv (.cv x) (.cv y) W
  have p0009 := @gBrcnv (.cv x) (.cv z) W
  have p0010 :=
    @gAnbi12i (synWbr (.cv x) (synCcnv W) (.cv y)) (synWbr (.cv y) W (.cv x))
      (synWbr (.cv x) (synCcnv W) (.cv z)) (synWbr (.cv z) W (.cv x)) p0008 p0009
  have p0011 :=
    @gImbi1i
      (synWa (synWbr (.cv x) (synCcnv W) (.cv y)) (synWbr (.cv x) (synCcnv W) (.cv z)))
      (synWa (synWbr (.cv y) W (.cv x)) (synWbr (.cv z) W (.cv x))) (.objEq y z) p0010
  have p0012 :=
    @gAlbii
      (.imp (synWa (synWbr (.cv x) (synCcnv W) (.cv y))
          (synWbr (.cv x) (synCcnv W) (.cv z))) (.objEq y z))
      (.imp (synWa (synWbr (.cv y) W (.cv x)) (synWbr (.cv z) W (.cv x))) (.objEq y z))
      z p0011
  have p0013 :=
    @gN2albii
      (.all z (.imp (synWa (synWbr (.cv x) (synCcnv W) (.cv y))
            (synWbr (.cv x) (synCcnv W) (.cv z))) (.objEq y z)))
      (.all z (.imp (synWa (synWbr (.cv y) W (.cv x)) (synWbr (.cv z) W (.cv x)))
          (.objEq y z)))
      x y p0012
  have p0014 :=
    @gBitri (synWfun (synCcnv W))
      (.all x (.all y (.all z (.imp (synWa (synWbr (.cv x) (synCcnv W) (.cv y))
                (synWbr (.cv x) (synCcnv W) (.cv z))) (.objEq y z)))))
      (.all x (.all y (.all z
            (.imp (synWa (synWbr (.cv y) W (.cv x)) (synWbr (.cv z) W (.cv x)))
              (.objEq y z)))))
      p0007 p0013
  have p0015 :=
    @gSylibr (synWf1o (.cv r) (.cv a) (.cv b))
      (.all x (.all y (.all z
            (.imp (synWa (synWbr (.cv y) W (.cv x)) (synWbr (.cv z) W (.cv x)))
              (.objEq y z)))))
      (synWfun (synCcnv W)) p0006 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part037`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_enmap2lem5`. -/
@[expose]
noncomputable def gEnmap2lem5 (G : Class) (W : Class) (s : Var) (r : Var) (a : Var)
    (b : Var) (dv_G_s : s ∉ G.fv) (dv_a_s : a ≠ s) (dv_r_s : r ≠ s)
    (hyp_enmap2lem5_1 : Nominal.NPrf (.classEq W (synCmpt s (synCo G (synCmap) (.cv a))
            (synCcom (.cv s) (synCcnv (.cv r)))))) :
    Nominal.NPrf
      (.imp (synWf1o (.cv r) (.cv a) (.cv b))
        (.classEq (synCrn W) (synCo G (synCmap) (.cv b)))) :=
  by
  let proofSupport : Finset Var :=
    G.fv ∪ W.fv ∪ ({ s } : Finset Var) ∪ ({ r } : Finset Var) ∪ ({ a } : Finset Var) ∪
      ({ b } : Finset Var)
  let p : Var := freshVar proofSupport 0
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_not_G : p ∉ G.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))))
  have fresh_p_not_W : p ∉ W.fv := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))))
  have fresh_p_ne_s : p ≠ s := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))))
  have fresh_s_ne_p : s ≠ p := Ne.symm fresh_p_ne_s
  have fresh_p_ne_r : p ≠ r := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_p_ne_a : p ≠ a := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_b : p ≠ b := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have dv_cache_0001 : s ∉ (G).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_G_s, not_false_eq_true])
  have dv_cache_0002 : a ≠ s := by
    clear dv_cache_0001
    exact (show a ≠ s from (by exact dv_a_s))
  have dv_cache_0003 : s ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_s_ne_p, not_false_eq_true])
  have dv_cache_0004 : s ∉ ((synCcom (.cv p) (synCcnv (.cv r)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_p, (Ne.symm dv_r_s), or_false,
          not_false_eq_true])
  have dv_cache_0005 : s ∉ ((synCo G (synCmap) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_G_s, (Ne.symm dv_a_s), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0006 : p ∉ ((synWf1o (.cv r) (.cv a) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wf1o,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_a, fresh_p_ne_b, fresh_p_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0007 : p ∉ ((synCo G (synCmap) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_G, fresh_p_ne_a, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 : p ∉ ((synCo G (synCmap) (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_not_G, fresh_p_ne_b, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0009 : p ∉ (W).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_p_not_W, not_false_eq_true])
  have dv_cache_0010 : s ∉ ((synCcom (.cv p) (.cv r))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_p, (Ne.symm dv_r_s), or_false,
          not_false_eq_true])
  have dv_cache_0011 :
    s ∉ ((synCcom (.cv p) (synCcom (.cv r) (synCcnv (.cv r))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv, Finset.mem_union,
          Finset.mem_singleton, fresh_s_ne_p, (Ne.symm dv_r_s), or_false,
          not_false_eq_true])
  have dv_cache_0012 : p ∉ ((synCrn W)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn, fresh_p_not_W,
          not_false_eq_true])
  have p0000 := @gEnmap2lem2 G W s r a dv_cache_0001 dv_cache_0002 hyp_enmap2lem5_1
  have p0001 := @gCoeq1 (.cv s) (.cv p) (synCcnv (.cv r))
  have p0002 := @gVex p
  have p0003 := @gVex r
  have p0004 := @gCnvex (.cv r) p0003
  have p0005 := @gCoex (.cv p) (synCcnv (.cv r)) p0002 p0004
  have p0006 :=
    @gFvmpt s (.cv p) (synCcom (.cv s) (synCcnv (.cv r)))
      (synCcom (.cv p) (synCcnv (.cv r))) (synCo G (synCmap) (.cv a)) W dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0001 hyp_enmap2lem5_1 p0005
  have p0007 :=
    @gAdantl (.classMem (.cv p) (synCo G (synCmap) (.cv a)))
      (.classEq (synCfv W (.cv p)) (synCcom (.cv p) (synCcnv (.cv r))))
      (synWf1o (.cv r) (.cv a) (.cv b)) p0006
  have p0008 := @gElmapi (.cv p) G (.cv a)
  have p0009 := @gF1ocnv (.cv a) (.cv b) (.cv r)
  have p0010 := @gF1of (.cv b) (.cv a) (synCcnv (.cv r))
  have p0011 :=
    @gSyl (synWf1o (.cv r) (.cv a) (.cv b))
      (synWf1o (synCcnv (.cv r)) (.cv b) (.cv a))
      (synWf (synCcnv (.cv r)) (.cv b) (.cv a)) p0009 p0010
  have p0012 := @gFco (.cv b) (.cv a) G (.cv p) (synCcnv (.cv r))
  have p0013 :=
    @gSyl2anr (.classMem (.cv p) (synCo G (synCmap) (.cv a)))
      (synWf (.cv p) (.cv a) G) (synWf (synCcnv (.cv r)) (.cv b) (.cv a))
      (synWf (synCcom (.cv p) (synCcnv (.cv r))) (.cv b) G)
      (synWf1o (.cv r) (.cv a) (.cv b)) p0008 p0011 p0012
  have p0014 := @gElovex1 (.cv p) G (.cv a) (synCmap)
  have p0015 := @gVex b
  have p0016 :=
    @gElmapg G (.cv b) (synCcom (.cv p) (synCcnv (.cv r))) (synCvv) (synCvv)
      (synCvv)
  have p0017 :=
    @gMp3an23 (.classMem G (synCvv)) (.classMem (.cv b) (synCvv))
      (.classMem (synCcom (.cv p) (synCcnv (.cv r))) (synCvv))
      (synWb (.classMem (synCcom (.cv p) (synCcnv (.cv r))) (synCo G (synCmap) (.cv b)))
        (synWf (synCcom (.cv p) (synCcnv (.cv r))) (.cv b) G))
      p0015 p0005 p0016
  have p0018 :=
    @gSyl (.classMem (.cv p) (synCo G (synCmap) (.cv a))) (.classMem G (synCvv))
      (synWb (.classMem (synCcom (.cv p) (synCcnv (.cv r))) (synCo G (synCmap) (.cv b)))
        (synWf (synCcom (.cv p) (synCcnv (.cv r))) (.cv b) G))
      p0014 p0017
  have p0019 :=
    @gAdantl (.classMem (.cv p) (synCo G (synCmap) (.cv a)))
      (synWb (.classMem (synCcom (.cv p) (synCcnv (.cv r))) (synCo G (synCmap) (.cv b)))
        (synWf (synCcom (.cv p) (synCcnv (.cv r))) (.cv b) G))
      (synWf1o (.cv r) (.cv a) (.cv b)) p0018
  have p0020 :=
    @gMpbird
      (synWa (synWf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (synCo G (synCmap) (.cv a))))
      (.classMem (synCcom (.cv p) (synCcnv (.cv r))) (synCo G (synCmap) (.cv b)))
      (synWf (synCcom (.cv p) (synCcnv (.cv r))) (.cv b) G) p0013 p0019
  have p0021 :=
    @gEqeltrd
      (synWa (synWf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (synCo G (synCmap) (.cv a))))
      (synCfv W (.cv p)) (synCcom (.cv p) (synCcnv (.cv r)))
      (synCo G (synCmap) (.cv b)) p0007 p0020
  have p0022 :=
    @gRalrimiva (synWf1o (.cv r) (.cv a) (.cv b))
      (.classMem (synCfv W (.cv p)) (synCo G (synCmap) (.cv b))) p
      (synCo G (synCmap) (.cv a)) dv_cache_0006 p0021
  have p0023 :=
    @gFnfvrnss p (synCo G (synCmap) (.cv a)) (synCo G (synCmap) (.cv b)) W
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0024 :=
    @gSylancr (synWf1o (.cv r) (.cv a) (.cv b))
      (synWfn W (synCo G (synCmap) (.cv a)))
      (synWral p (synCo G (synCmap) (.cv a))
        (.classMem (synCfv W (.cv p)) (synCo G (synCmap) (.cv b))))
      (synWss (synCrn W) (synCo G (synCmap) (.cv b))) p0000 p0022 p0023
  have p0025 := @gElmapi (.cv p) G (.cv b)
  have p0026 := @gF1of (.cv a) (.cv b) (.cv r)
  have p0027 := @gFco (.cv a) (.cv b) G (.cv p) (.cv r)
  have p0028 :=
    @gSyl2anr (.classMem (.cv p) (synCo G (synCmap) (.cv b)))
      (synWf (.cv p) (.cv b) G) (synWf (.cv r) (.cv a) (.cv b))
      (synWf (synCcom (.cv p) (.cv r)) (.cv a) G) (synWf1o (.cv r) (.cv a) (.cv b))
      p0025 p0026 p0027
  have p0029 := @gElovex1 (.cv p) G (.cv b) (synCmap)
  have p0030 := @gVex a
  have p0031 := @gCoex (.cv p) (.cv r) p0002 p0003
  have p0032 :=
    @gElmapg G (.cv a) (synCcom (.cv p) (.cv r)) (synCvv) (synCvv) (synCvv)
  have p0033 :=
    @gMp3an23 (.classMem G (synCvv)) (.classMem (.cv a) (synCvv))
      (.classMem (synCcom (.cv p) (.cv r)) (synCvv))
      (synWb (.classMem (synCcom (.cv p) (.cv r)) (synCo G (synCmap) (.cv a)))
        (synWf (synCcom (.cv p) (.cv r)) (.cv a) G))
      p0030 p0031 p0032
  have p0034 :=
    @gSyl (.classMem (.cv p) (synCo G (synCmap) (.cv b))) (.classMem G (synCvv))
      (synWb (.classMem (synCcom (.cv p) (.cv r)) (synCo G (synCmap) (.cv a)))
        (synWf (synCcom (.cv p) (.cv r)) (.cv a) G))
      p0029 p0033
  have p0035 :=
    @gAdantl (.classMem (.cv p) (synCo G (synCmap) (.cv b)))
      (synWb (.classMem (synCcom (.cv p) (.cv r)) (synCo G (synCmap) (.cv a)))
        (synWf (synCcom (.cv p) (.cv r)) (.cv a) G))
      (synWf1o (.cv r) (.cv a) (.cv b)) p0034
  have p0036 :=
    @gMpbird
      (synWa (synWf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (synCo G (synCmap) (.cv b))))
      (.classMem (synCcom (.cv p) (.cv r)) (synCo G (synCmap) (.cv a)))
      (synWf (synCcom (.cv p) (.cv r)) (.cv a) G) p0028 p0035
  have p0037 := @gCoeq1 (.cv s) (synCcom (.cv p) (.cv r)) (synCcnv (.cv r))
  have p0038 := @gCoass (.cv p) (.cv r) (synCcnv (.cv r))
  have p0039 :=
    @gSyl6eq (.classEq (.cv s) (synCcom (.cv p) (.cv r)))
      (synCcom (.cv s) (synCcnv (.cv r)))
      (synCcom (synCcom (.cv p) (.cv r)) (synCcnv (.cv r)))
      (synCcom (.cv p) (synCcom (.cv r) (synCcnv (.cv r)))) p0037 p0038
  have p0040 := @gCoex (.cv r) (synCcnv (.cv r)) p0003 p0004
  have p0041 := @gCoex (.cv p) (synCcom (.cv r) (synCcnv (.cv r))) p0002 p0040
  have p0042 :=
    @gFvmpt s (synCcom (.cv p) (.cv r)) (synCcom (.cv s) (synCcnv (.cv r)))
      (synCcom (.cv p) (synCcom (.cv r) (synCcnv (.cv r))))
      (synCo G (synCmap) (.cv a)) W dv_cache_0010 dv_cache_0011 dv_cache_0005 p0039
      hyp_enmap2lem5_1 p0041
  have p0043 :=
    @gSyl
      (synWa (synWf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (synCo G (synCmap) (.cv b))))
      (.classMem (synCcom (.cv p) (.cv r)) (synCo G (synCmap) (.cv a)))
      (.classEq (synCfv W (synCcom (.cv p) (.cv r)))
        (synCcom (.cv p) (synCcom (.cv r) (synCcnv (.cv r)))))
      p0036 p0042
  have p0044 := @gF1ococnv2 (.cv a) (.cv b) (.cv r)
  have p0045 :=
    @gCoeq2d (synWf1o (.cv r) (.cv a) (.cv b)) (synCcom (.cv r) (synCcnv (.cv r)))
      (synCres (synCid) (.cv b)) (.cv p) p0044
  have p0046 := @gFcoi1 (.cv b) G (.cv p)
  have p0047 :=
    @gSyl (.classMem (.cv p) (synCo G (synCmap) (.cv b))) (synWf (.cv p) (.cv b) G)
      (.classEq (synCcom (.cv p) (synCres (synCid) (.cv b))) (.cv p)) p0025 p0046
  have p0048 :=
    @gSylan9eq (synWf1o (.cv r) (.cv a) (.cv b))
      (.classMem (.cv p) (synCo G (synCmap) (.cv b)))
      (synCcom (.cv p) (synCcom (.cv r) (synCcnv (.cv r))))
      (synCcom (.cv p) (synCres (synCid) (.cv b))) (.cv p) p0045 p0047
  have p0049 :=
    @gEqtrd
      (synWa (synWf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (synCo G (synCmap) (.cv b))))
      (synCfv W (synCcom (.cv p) (.cv r)))
      (synCcom (.cv p) (synCcom (.cv r) (synCcnv (.cv r)))) (.cv p) p0043 p0048
  have p0050 :=
    @gFnbrfvb (synCo G (synCmap) (.cv a)) (synCcom (.cv p) (.cv r)) (.cv p) W
  have p0051 :=
    @gSylancr
      (synWa (synWf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (synCo G (synCmap) (.cv b))))
      (synWfn W (synCo G (synCmap) (.cv a)))
      (.classMem (synCcom (.cv p) (.cv r)) (synCo G (synCmap) (.cv a)))
      (synWb (.classEq (synCfv W (synCcom (.cv p) (.cv r))) (.cv p))
        (synWbr (synCcom (.cv p) (.cv r)) W (.cv p)))
      p0000 p0036 p0050
  have p0052 :=
    @gMpbid
      (synWa (synWf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (synCo G (synCmap) (.cv b))))
      (.classEq (synCfv W (synCcom (.cv p) (.cv r))) (.cv p))
      (synWbr (synCcom (.cv p) (.cv r)) W (.cv p)) p0049 p0051
  have p0053 := @gBrelrn (synCcom (.cv p) (.cv r)) (.cv p) W
  have p0054 :=
    @gSyl
      (synWa (synWf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (synCo G (synCmap) (.cv b))))
      (synWbr (synCcom (.cv p) (.cv r)) W (.cv p)) (.classMem (.cv p) (synCrn W)) p0052
      p0053
  have p0055 :=
    @gEx (synWf1o (.cv r) (.cv a) (.cv b))
      (.classMem (.cv p) (synCo G (synCmap) (.cv b))) (.classMem (.cv p) (synCrn W))
      p0054
  have p0056 :=
    @gSsrdv (synWf1o (.cv r) (.cv a) (.cv b)) p (synCo G (synCmap) (.cv b))
      (synCrn W) dv_cache_0008 dv_cache_0012 dv_cache_0006 p0055
  have p0057 :=
    @gEqssd (synWf1o (.cv r) (.cv a) (.cv b)) (synCrn W) (synCo G (synCmap) (.cv b))
      p0024 p0056
  exact p0057

/-- Checked nominal proof certificate identified upstream as `g_enmap2`. -/
@[expose]
noncomputable def gEnmap2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (synWbr A (synCen) B)
        (synWbr (synCo C (synCmap) A) (synCen) (synCo C (synCmap) B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let a : Var := freshVar proofSupport 0
  let b : Var := freshVar proofSupport 1
  let r : Var := freshVar proofSupport 2
  let s : Var := freshVar proofSupport 3
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_a_not_C : a ∉ C.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_b_not_A : b ∉ A.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_b_not_B : b ∉ B.fv := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_b_not_C : b ∉ C.fv := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_r_not_C : r ∉ C.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_s : s ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_s_not_C : s ∉ C.fv := by
    intro h
    exact fresh_s (Finset.mem_union_right _ (h))
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_r : a ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_r_ne_a : r ≠ a := Ne.symm fresh_a_ne_r
  have fresh_a_ne_s : a ≠ s :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_s_ne_a : s ≠ a := Ne.symm fresh_a_ne_s
  have fresh_b_ne_r : b ≠ r :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_r_ne_b : r ≠ b := Ne.symm fresh_b_ne_r
  have fresh_r_ne_s : r ≠ s :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : r ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_a, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((Class.cv b)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_b, not_false_eq_true])
  have dv_cache_0003 : s ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_s_not_C, not_false_eq_true])
  have dv_cache_0004 : a ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ s from (by exact fresh_a_ne_s))
  have dv_cache_0005 : r ≠ s :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show r ≠ s from (by exact fresh_r_ne_s))
  have dv_cache_0006 : s ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : s ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_s_ne_a, not_false_eq_true])
  have dv_cache_0007 :
    r ∉
      ((synWbr (synCo C (synCmap) (.cv a)) (synCen) (synCo C (synCmap) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          Finset.mem_singleton, fresh_r_not_C, fresh_r_ne_a, fresh_r_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0009 : b ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_A, not_false_eq_true])
  have dv_cache_0010 : b ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_b_not_B, not_false_eq_true])
  have dv_cache_0011 :
    b ∉
      ((Wff.imp (synWbr A (synCen) B)
          (synWbr (synCo C (synCmap) A) (synCen) (synCo C (synCmap) B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union,
          fresh_b_not_A, fresh_b_not_B, fresh_b_not_C, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    a ∉
      ((Wff.imp (synWbr A (synCen) (.cv b)) (synWbr (synCo C (synCmap) A) (synCen)
            (synCo C (synCmap) (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union,
          Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_b, fresh_a_not_C,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gBrex A B (synCen)
  have p0001 := @gBreq1 (.cv a) A (.cv b) (synCen)
  have p0002 := @gOveq2 (.cv a) A C (synCmap)
  have p0003 :=
    @gBreq1d (.classEq (.cv a) A) (synCo C (synCmap) (.cv a)) (synCo C (synCmap) A)
      (synCo C (synCmap) (.cv b)) (synCen) p0002
  have p0004 :=
    @gImbi12d (.classEq (.cv a) A) (synWbr (.cv a) (synCen) (.cv b))
      (synWbr A (synCen) (.cv b))
      (synWbr (synCo C (synCmap) (.cv a)) (synCen) (synCo C (synCmap) (.cv b)))
      (synWbr (synCo C (synCmap) A) (synCen) (synCo C (synCmap) (.cv b))) p0001
      p0003
  have p0005 := @gBreq2 (.cv b) B A (synCen)
  have p0006 := @gOveq2 (.cv b) B C (synCmap)
  have p0007 :=
    @gBreq2d (.classEq (.cv b) B) (synCo C (synCmap) (.cv b)) (synCo C (synCmap) B)
      (synCo C (synCmap) A) (synCen) p0006
  have p0008 :=
    @gImbi12d (.classEq (.cv b) B) (synWbr A (synCen) (.cv b)) (synWbr A (synCen) B)
      (synWbr (synCo C (synCmap) A) (synCen) (synCo C (synCmap) (.cv b)))
      (synWbr (synCo C (synCmap) A) (synCen) (synCo C (synCmap) B)) p0005 p0007
  have p0009 := @gBren (.cv a) (.cv b) r dv_cache_0001 dv_cache_0002
  have p0010 :=
    @gEqid
      (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r))))
  have p0011 :=
    @gEnmap2lem4 C
      (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r)))) s r
      a b dv_cache_0003 dv_cache_0004 dv_cache_0005 p0010
  have p0012 :=
    @gDfrn4
      (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r))))
  have p0013 :=
    @gEnmap2lem5 C
      (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r)))) s r
      a b dv_cache_0003 dv_cache_0004 dv_cache_0005 p0010
  have p0014 :=
    @gSyl5eqr (synWf1o (.cv r) (.cv a) (.cv b))
      (synCdm (synCcnv (synCmpt s (synCo C (synCmap) (.cv a))
            (synCcom (.cv s) (synCcnv (.cv r))))))
      (synCrn (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r)))))
      (synCo C (synCmap) (.cv b)) p0012 p0013
  have p0015 :=
    @gJca (synWf1o (.cv r) (.cv a) (.cv b))
      (synWfun (synCcnv (synCmpt s (synCo C (synCmap) (.cv a))
            (synCcom (.cv s) (synCcnv (.cv r))))))
      (.classEq (synCdm (synCcnv (synCmpt s (synCo C (synCmap) (.cv a))
              (synCcom (.cv s) (synCcnv (.cv r)))))) (synCo C (synCmap) (.cv b)))
      p0011 p0014
  have p0016 :=
    (Nominal.biimpRefl (synWfn (synCcnv (synCmpt s (synCo C (synCmap) (.cv a))
            (synCcom (.cv s) (synCcnv (.cv r))))) (synCo C (synCmap) (.cv b))))
  have p0017 :=
    @gSylibr (synWf1o (.cv r) (.cv a) (.cv b))
      (synWa (synWfun (synCcnv (synCmpt s (synCo C (synCmap) (.cv a))
              (synCcom (.cv s) (synCcnv (.cv r)))))) (.classEq (synCdm (synCcnv
              (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r))))))
          (synCo C (synCmap) (.cv b))))
      (synWfn (synCcnv (synCmpt s (synCo C (synCmap) (.cv a))
            (synCcom (.cv s) (synCcnv (.cv r))))) (synCo C (synCmap) (.cv b)))
      p0015 p0016
  have p0018 :=
    @gEnmap2lem2 C
      (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r)))) s r
      a dv_cache_0003 dv_cache_0004 p0010
  have p0019 :=
    @gDff1o4 (synCo C (synCmap) (.cv a)) (synCo C (synCmap) (.cv b))
      (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r))))
  have p0020 :=
    @gMpbiran
      (synWf1o (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r))))
        (synCo C (synCmap) (.cv a)) (synCo C (synCmap) (.cv b)))
      (synWfn (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r))))
        (synCo C (synCmap) (.cv a)))
      (synWfn (synCcnv (synCmpt s (synCo C (synCmap) (.cv a))
            (synCcom (.cv s) (synCcnv (.cv r))))) (synCo C (synCmap) (.cv b)))
      p0018 p0019
  have p0021 :=
    @gSylibr (synWf1o (.cv r) (.cv a) (.cv b))
      (synWfn (synCcnv (synCmpt s (synCo C (synCmap) (.cv a))
            (synCcom (.cv s) (synCcnv (.cv r))))) (synCo C (synCmap) (.cv b)))
      (synWf1o (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r))))
        (synCo C (synCmap) (.cv a)) (synCo C (synCmap) (.cv b)))
      p0017 p0020
  have p0022 :=
    @gEnmap2lem1 (.cv a) C
      (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r)))) s r
      dv_cache_0006 dv_cache_0003 dv_cache_0005 p0010
  have p0023 :=
    @gF1oen (synCo C (synCmap) (.cv a)) (synCo C (synCmap) (.cv b))
      (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r))))
      p0022
  have p0024 :=
    @gSyl (synWf1o (.cv r) (.cv a) (.cv b))
      (synWf1o (synCmpt s (synCo C (synCmap) (.cv a)) (synCcom (.cv s) (synCcnv (.cv r))))
        (synCo C (synCmap) (.cv a)) (synCo C (synCmap) (.cv b)))
      (synWbr (synCo C (synCmap) (.cv a)) (synCen) (synCo C (synCmap) (.cv b)))
      p0021 p0023
  have p0025 :=
    @gExlimiv (synWf1o (.cv r) (.cv a) (.cv b))
      (synWbr (synCo C (synCmap) (.cv a)) (synCen) (synCo C (synCmap) (.cv b))) r
      dv_cache_0007 p0024
  have p0026 :=
    @gSylbi (synWbr (.cv a) (synCen) (.cv b))
      (synWex r (synWf1o (.cv r) (.cv a) (.cv b)))
      (synWbr (synCo C (synCmap) (.cv a)) (synCen) (synCo C (synCmap) (.cv b)))
      p0009 p0025
  have p0027 :=
    @gVtocl2g
      (.imp (synWbr (.cv a) (synCen) (.cv b))
        (synWbr (synCo C (synCmap) (.cv a)) (synCen) (synCo C (synCmap) (.cv b))))
      (.imp (synWbr A (synCen) (.cv b))
        (synWbr (synCo C (synCmap) A) (synCen) (synCo C (synCmap) (.cv b))))
      (.imp (synWbr A (synCen) B)
        (synWbr (synCo C (synCmap) A) (synCen) (synCo C (synCmap) B)))
      a b A B (synCvv) (synCvv) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0004 p0008 p0026
  have p0028 :=
    @gMpcom (synWa (.classMem A (synCvv)) (.classMem B (synCvv)))
      (synWbr A (synCen) B)
      (synWbr (synCo C (synCmap) A) (synCen) (synCo C (synCmap) B)) p0000 p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as `g_enpw1pw`. -/
@[expose]
noncomputable def gEnpw1pw (A : Class)
    (hyp_enpw1pw_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (synWbr (synCpw1 (synCpw A)) (synCen) (synCpw (synCpw1 A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have dv_cache_0001 : x ∉ ((synCpw1fn)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCpw1fn)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((synCpw1 (synCpw A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((synCpw1 (synCpw A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0007 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0008 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0009 : z ∉ ((synCpw A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0010 : z ∉ ((synWbr (.cv y) (synCpw1fn) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((synCpw A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0012 : z ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show z ≠ y from (by exact fresh_z_ne_y))
  have dv_cache_0013 : y ∉ ((synCsn (.cv z))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_z,
          not_false_eq_true])
  have dv_cache_0014 : y ∉ ((synWbr (synCsn (.cv z)) (synCpw1fn) (.cv x))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((synCpw (synCpw1 A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_x_not_A,
          not_false_eq_true])
  have p0000 := @gPw1fnf1o
  have p0001 := @gF1of1 (synC1c) (synCpw (synC1c)) (synCpw1fn)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gPw1ss1c (synCpw A)
  have p0004 :=
    @gF1ores (synC1c) (synCpw (synC1c)) (synCpw1 (synCpw A)) (synCpw1fn)
  have p0005 :=
    @gMp2an (synWf1 (synCpw1fn) (synC1c) (synCpw (synC1c)))
      (synWss (synCpw1 (synCpw A)) (synC1c))
      (synWf1o (synCres (synCpw1fn) (synCpw1 (synCpw A))) (synCpw1 (synCpw A))
        (synCima (synCpw1fn) (synCpw1 (synCpw A))))
      p0002 p0003 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma x y (synCpw1fn)
      (synCpw1 (synCpw A)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0007 := @gVex x
  have p0008 := @gElpw (.cv x) (synCpw1 A) p0007
  have p0009 := @gSspw1 z (.cv x) A dv_cache_0006 dv_cache_0007 p0007
  have p0010 :=
    (Nominal.biimpRefl (synWrex z (synCpw A) (.classEq (.cv x) (synCpw1 (.cv z)))))
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPw z A dv_cache_0007
  have p0012 := @gEqabri (synWss (.cv z) A) z (synCpw A) p0011
  have p0013 :=
    @gAnbi1i (.classMem (.cv z) (synCpw A)) (synWss (.cv z) A)
      (.classEq (.cv x) (synCpw1 (.cv z))) p0012
  have p0014 :=
    @gExbii
      (synWa (.classMem (.cv z) (synCpw A)) (.classEq (.cv x) (synCpw1 (.cv z))))
      (synWa (synWss (.cv z) A) (.classEq (.cv x) (synCpw1 (.cv z)))) z p0013
  have p0015 :=
    @gBitr2i (synWrex z (synCpw A) (.classEq (.cv x) (synCpw1 (.cv z))))
      (synWex z (synWa (.classMem (.cv z) (synCpw A)) (.classEq (.cv x) (synCpw1 (.cv z)))))
      (synWex z (synWa (synWss (.cv z) A) (.classEq (.cv x) (synCpw1 (.cv z))))) p0010
      p0014
  have p0016 :=
    @gN3bitri (.classMem (.cv x) (synCpw (synCpw1 A))) (synWss (.cv x) (synCpw1 A))
      (synWex z (synWa (synWss (.cv z) A) (.classEq (.cv x) (synCpw1 (.cv z)))))
      (synWrex z (synCpw A) (.classEq (.cv x) (synCpw1 (.cv z)))) p0008 p0009 p0015
  have p0017 :=
    (Nominal.biimpRefl
      (synWrex y (synCpw1 (synCpw A)) (synWbr (.cv y) (synCpw1fn) (.cv x))))
  have p0018 := @gElpw1 z (.cv y) (synCpw A) dv_cache_0008 dv_cache_0009
  have p0019 :=
    @gAnbi1i (.classMem (.cv y) (synCpw1 (synCpw A)))
      (synWrex z (synCpw A) (.classEq (.cv y) (synCsn (.cv z))))
      (synWbr (.cv y) (synCpw1fn) (.cv x)) p0018
  have p0020 :=
    @gR1941v (.classEq (.cv y) (synCsn (.cv z))) (synWbr (.cv y) (synCpw1fn) (.cv x))
      z (synCpw A) dv_cache_0010
  have p0021 :=
    @gBitr4i
      (synWa (.classMem (.cv y) (synCpw1 (synCpw A))) (synWbr (.cv y) (synCpw1fn) (.cv x)))
      (synWa (synWrex z (synCpw A) (.classEq (.cv y) (synCsn (.cv z))))
        (synWbr (.cv y) (synCpw1fn) (.cv x)))
      (synWrex z (synCpw A) (synWa (.classEq (.cv y) (synCsn (.cv z)))
          (synWbr (.cv y) (synCpw1fn) (.cv x))))
      p0019 p0020
  have p0022 :=
    @gExbii
      (synWa (.classMem (.cv y) (synCpw1 (synCpw A))) (synWbr (.cv y) (synCpw1fn) (.cv x)))
      (synWrex z (synCpw A) (synWa (.classEq (.cv y) (synCsn (.cv z)))
          (synWbr (.cv y) (synCpw1fn) (.cv x))))
      y p0021
  have p0023 :=
    @gRexcom4
      (synWa (.classEq (.cv y) (synCsn (.cv z))) (synWbr (.cv y) (synCpw1fn) (.cv x)))
      z y (synCpw A) dv_cache_0011 dv_cache_0012
  have p0024 := @gSnex (.cv z)
  have p0025 := @gBreq1 (.cv y) (synCsn (.cv z)) (.cv x) (synCpw1fn)
  have p0026 :=
    @gCeqsexv (synWbr (.cv y) (synCpw1fn) (.cv x))
      (synWbr (synCsn (.cv z)) (synCpw1fn) (.cv x)) y (synCsn (.cv z)) dv_cache_0013
      dv_cache_0014 p0024 p0025
  have p0027 := @gVex z
  have p0028 := @gBrpw1fn (.cv z) (.cv x) p0027
  have p0029 :=
    @gBitri
      (synWex y (synWa (.classEq (.cv y) (synCsn (.cv z)))
          (synWbr (.cv y) (synCpw1fn) (.cv x))))
      (synWbr (synCsn (.cv z)) (synCpw1fn) (.cv x))
      (.classEq (.cv x) (synCpw1 (.cv z))) p0026 p0028
  have p0030 :=
    @gRexbii
      (synWex y (synWa (.classEq (.cv y) (synCsn (.cv z)))
          (synWbr (.cv y) (synCpw1fn) (.cv x))))
      (.classEq (.cv x) (synCpw1 (.cv z))) z (synCpw A) p0029
  have p0031 :=
    @gBitr3i
      (synWex y (synWrex z (synCpw A) (synWa (.classEq (.cv y) (synCsn (.cv z)))
            (synWbr (.cv y) (synCpw1fn) (.cv x)))))
      (synWrex z (synCpw A) (synWex y (synWa (.classEq (.cv y) (synCsn (.cv z)))
            (synWbr (.cv y) (synCpw1fn) (.cv x)))))
      (synWrex z (synCpw A) (.classEq (.cv x) (synCpw1 (.cv z)))) p0023 p0030
  have p0032 :=
    @gN3bitri (synWrex y (synCpw1 (synCpw A)) (synWbr (.cv y) (synCpw1fn) (.cv x)))
      (synWex y (synWa (.classMem (.cv y) (synCpw1 (synCpw A)))
          (synWbr (.cv y) (synCpw1fn) (.cv x))))
      (synWex y (synWrex z (synCpw A) (synWa (.classEq (.cv y) (synCsn (.cv z)))
            (synWbr (.cv y) (synCpw1fn) (.cv x)))))
      (synWrex z (synCpw A) (.classEq (.cv x) (synCpw1 (.cv z)))) p0017 p0022 p0031
  have p0033 :=
    @gBitr4i (.classMem (.cv x) (synCpw (synCpw1 A)))
      (synWrex z (synCpw A) (.classEq (.cv x) (synCpw1 (.cv z))))
      (synWrex y (synCpw1 (synCpw A)) (synWbr (.cv y) (synCpw1fn) (.cv x))) p0016
      p0032
  have p0034 :=
    @gEqabi (synWrex y (synCpw1 (synCpw A)) (synWbr (.cv y) (synCpw1fn) (.cv x))) x
      (synCpw (synCpw1 A)) dv_cache_0015 p0033
  have p0035 :=
    @gEqtr4i (synCima (synCpw1fn) (synCpw1 (synCpw A)))
      (.cab x (synWrex y (synCpw1 (synCpw A)) (synWbr (.cv y) (synCpw1fn) (.cv x))))
      (synCpw (synCpw1 A)) p0006 p0034
  have p0036 :=
    @gF1oeq3 (synCima (synCpw1fn) (synCpw1 (synCpw A))) (synCpw (synCpw1 A))
      (synCpw1 (synCpw A)) (synCres (synCpw1fn) (synCpw1 (synCpw A)))
  have p0037 := Nominal.mp p0035 p0036
  have p0038 :=
    @gMpbi
      (synWf1o (synCres (synCpw1fn) (synCpw1 (synCpw A))) (synCpw1 (synCpw A))
        (synCima (synCpw1fn) (synCpw1 (synCpw A))))
      (synWf1o (synCres (synCpw1fn) (synCpw1 (synCpw A))) (synCpw1 (synCpw A))
        (synCpw (synCpw1 A)))
      p0005 p0037
  have p0039 := @gPw1fnex
  have p0040 := @gPwex A hyp_enpw1pw_1
  have p0041 := @gPw1ex (synCpw A) p0040
  have p0042 := @gResex (synCpw1fn) (synCpw1 (synCpw A)) p0039 p0041
  have p0043 :=
    @gF1oen (synCpw1 (synCpw A)) (synCpw (synCpw1 A))
      (synCres (synCpw1fn) (synCpw1 (synCpw A))) p0042
  have p0044 := Nominal.mp p0038 p0043
  exact p0044


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part038`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_enprmaplem1`. -/
@[expose]
noncomputable def gEnprmaplem1 (x : Var) (A : Class) (B : Class) (W : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv) (dv_r_x : r ≠ x)
    (hyp_enprmaplem1_1 : Nominal.NPrf (.classEq W (synCmpt r (synCo A (synCmap) B)
            (synCima (synCcnv (.cv r)) (synCsn (.cv x)))))) :
    Nominal.NPrf (.classMem W (synCvv)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ A.fv ∪ B.fv ∪ W.fv ∪ ({ r } : Finset Var)
  let y : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_y_ne_r : y ≠ r := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_r_ne_y : r ≠ y := Ne.symm fresh_y_ne_r
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_t_ne_r : t ≠ r := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have dv_cache_0001 : t ∉ ((synCop (synCsn (.cv y)) (.cv r))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_r, or_false, not_false_eq_true])
  have dv_cache_0002 :
    t ∉
      ((synCtxp (synCsi
            (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
          (synCsset))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : t ∉ ((synCop (.cv y) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ ((Wff.classMem (synCop (.cv y) (.cv x)) (.cv r))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, fresh_t_ne_r, or_false,
          not_false_eq_true])
  have dv_cache_0005 : r ∉ ((synCo A (synCmap) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, dv_A_r,
          dv_B_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    r ∉
      ((synCima (synCtxp (synCsi
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
            (synCsset)) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, dv_r_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((synCima (synCtxp (synCsi
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
            (synCsset)) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csi,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csset,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ ((synCima (synCcnv (.cv r)) (synCsn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_r, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0009 : r ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show r ≠ y from (by exact fresh_r_ne_y))
  have p0000 :=
    @gElima1c t (synCop (synCsn (.cv y)) (.cv r))
      (synCtxp
        (synCsi (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
        (synCsset))
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gOteltxp (synCsn (.cv t)) (synCsn (.cv y)) (.cv r)
      (synCsi (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
      (synCsset)
  have p0002 := @gVex t
  have p0003 := @gVex y
  have p0004 :=
    @gOpsnelsi (.cv t) (.cv y)
      (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))) p0002 p0003
  have p0005 :=
    (Nominal.biimpRefl (synWbr (.cv t)
        (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))) (.cv y)))
  have p0006 :=
    @gBrres (.cv t) (.cv y) (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))
  have p0007 := @gEliniseg (synC2nd) (.cv x) (.cv t)
  have p0008 :=
    @gAnbi2i (.classMem (.cv t) (synCima (synCcnv (synC2nd)) (synCsn (.cv x))))
      (synWbr (.cv t) (synC2nd) (.cv x)) (synWbr (.cv t) (synC1st) (.cv y)) p0007
  have p0009 :=
    @gBitri
      (synWbr (.cv t)
        (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))) (.cv y))
      (synWa (synWbr (.cv t) (synC1st) (.cv y))
        (.classMem (.cv t) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
      (synWa (synWbr (.cv t) (synC1st) (.cv y)) (synWbr (.cv t) (synC2nd) (.cv x)))
      p0006 p0008
  have p0010 :=
    @gBitr3i
      (.classMem (synCop (.cv t) (.cv y))
        (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
      (synWbr (.cv t)
        (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))) (.cv y))
      (synWa (synWbr (.cv t) (synC1st) (.cv y)) (synWbr (.cv t) (synC2nd) (.cv x)))
      p0005 p0009
  have p0011 := @gVex x
  have p0012 := @gOp1st2nd (.cv y) (.cv x) (.cv t) p0003 p0011
  have p0013 :=
    @gN3bitri
      (.classMem (synCop (synCsn (.cv t)) (synCsn (.cv y))) (synCsi
          (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x))))))
      (.classMem (synCop (.cv t) (.cv y))
        (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
      (synWa (synWbr (.cv t) (synC1st) (.cv y)) (synWbr (.cv t) (synC2nd) (.cv x)))
      (.classEq (.cv t) (synCop (.cv y) (.cv x))) p0004 p0010 p0012
  have p0014 := @gVex r
  have p0015 := @gOpelssetsn (.cv t) (.cv r) p0002 p0014
  have p0016_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCop (synCsn (.cv t)) (.cv r)) (synCsset)) (.objMem t r)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synCsn synCsset synCopab synWss synCin
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @gAnbi12i
      (.classMem (synCop (synCsn (.cv t)) (synCsn (.cv y))) (synCsi
          (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x))))))
      (.classEq (.cv t) (synCop (.cv y) (.cv x)))
      (.classMem (synCop (synCsn (.cv t)) (.cv r)) (synCsset)) (.objMem t r) p0013
      p0016_e01_recanon
  have p0017 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y)) (.cv r))) (synCtxp
          (synCsi (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
          (synCsset)))
      (synWa (.classMem (synCop (synCsn (.cv t)) (synCsn (.cv y))) (synCsi
            (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x))))))
        (.classMem (synCop (synCsn (.cv t)) (.cv r)) (synCsset)))
      (synWa (.classEq (.cv t) (synCop (.cv y) (.cv x))) (.objMem t r)) p0001 p0016
  have p0018 :=
    @gExbii
      (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y)) (.cv r))) (synCtxp
          (synCsi (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
          (synCsset)))
      (synWa (.classEq (.cv t) (synCop (.cv y) (.cv x))) (.objMem t r)) t p0017
  have p0019 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv y)) (.cv r)) (synCima (synCtxp (synCsi
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
            (synCsset)) (synC1c)))
      (synWex t (.classMem (synCop (synCsn (.cv t)) (synCop (synCsn (.cv y)) (.cv r)))
          (synCtxp (synCsi
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
            (synCsset))))
      (synWex t (synWa (.classEq (.cv t) (synCop (.cv y) (.cv x))) (.objMem t r)))
      p0000 p0018
  have p0020 := @gOpex (.cv y) (.cv x) p0003 p0011
  have p0021 := @gEleq1 (.cv t) (synCop (.cv y) (.cv x)) (.cv r)
  have p0022_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv t) (synCop (.cv y) (.cv x)))
        (synWb (.objMem t r) (.classMem (synCop (.cv y) (.cv x)) (.cv r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi synWb
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0021
  have p0022 :=
    @gCeqsexv (.objMem t r) (.classMem (synCop (.cv y) (.cv x)) (.cv r)) t
      (synCop (.cv y) (.cv x)) dv_cache_0003 dv_cache_0004 p0020 p0022_e01_recanon
  have p0023 := (Nominal.biimpRefl (synWbr (.cv y) (.cv r) (.cv x)))
  have p0024 :=
    @gBitr4i
      (synWex t (synWa (.classEq (.cv t) (synCop (.cv y) (.cv x))) (.objMem t r)))
      (.classMem (synCop (.cv y) (.cv x)) (.cv r)) (synWbr (.cv y) (.cv r) (.cv x))
      p0022 p0023
  have p0025 :=
    @gBitri
      (.classMem (synCop (synCsn (.cv y)) (.cv r)) (synCima (synCtxp (synCsi
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
            (synCsset)) (synC1c)))
      (synWex t (synWa (.classEq (.cv t) (synCop (.cv y) (.cv x))) (.objMem t r)))
      (synWbr (.cv y) (.cv r) (.cv x)) p0019 p0024
  have p0026 := @gEliniseg (.cv r) (.cv x) (.cv y)
  have p0027 :=
    @gBitr4i
      (.classMem (synCop (synCsn (.cv y)) (.cv r)) (synCima (synCtxp (synCsi
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
            (synCsset)) (synC1c)))
      (synWbr (.cv y) (.cv r) (.cv x))
      (.classMem (.cv y) (synCima (synCcnv (.cv r)) (synCsn (.cv x)))) p0025 p0026
  have p0028 :=
    @gReleqmpt r y (synCo A (synCmap) B)
      (synCima (synCtxp (synCsi
            (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
          (synCsset)) (synC1c))
      (synCima (synCcnv (.cv r)) (synCsn (.cv x))) dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 p0027
  have p0029 :=
    @gEqtr4i W
      (synCmpt r (synCo A (synCmap) B) (synCima (synCcnv (.cv r)) (synCsn (.cv x))))
      (synCin (synCxp (synCo A (synCmap) B) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCima (synCtxp (synCsi
                        (synCres (synC1st)
                          (synCima (synCcnv (synC2nd)) (synCsn (.cv x))))) (synCsset))
                    (synC1c)))) (synC1c)))))
      hyp_enprmaplem1_1 p0028
  have p0030 := @gOvex A B (synCmap)
  have p0031 := @gN1stex
  have p0032 := @gN2ndex
  have p0033 := @gCnvex (synC2nd) p0032
  have p0034 := @gSnex (.cv x)
  have p0035 := @gImaex (synCcnv (synC2nd)) (synCsn (.cv x)) p0033 p0034
  have p0036 :=
    @gResex (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x))) p0031 p0035
  have p0037 :=
    @gSiex (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))) p0036
  have p0038 := @gSsetex
  have p0039 :=
    @gTxpex
      (synCsi (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
      (synCsset) p0037 p0038
  have p0040 := @gN1cex
  have p0041 :=
    @gImaex
      (synCtxp
        (synCsi (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
        (synCsset))
      (synC1c) p0039 p0040
  have p0042 :=
    @gMptexlem (synCo A (synCmap) B)
      (synCima (synCtxp (synCsi
            (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (.cv x)))))
          (synCsset)) (synC1c))
      p0030 p0041
  have p0043 :=
    @gEqeltri W
      (synCin (synCxp (synCo A (synCmap) B) (synCvv)) (synCcnv (synCcompl (synCima
              (synCsymdif (synCins3 (synCsset)) (synCins2 (synCima (synCtxp (synCsi
                        (synCres (synC1st)
                          (synCima (synCcnv (synC2nd)) (synCsn (.cv x))))) (synCsset))
                    (synC1c)))) (synC1c)))))
      (synCvv) p0029 p0042
  exact p0043

/-- Checked nominal proof certificate identified upstream as `g_enprmaplem2`. -/
@[expose]
noncomputable def gEnprmaplem2 (x : Var) (A : Class) (B : Class) (W : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv)
    (hyp_enprmaplem2_1 : Nominal.NPrf (.classEq W (synCmpt r (synCo A (synCmap) B)
            (synCima (synCcnv (.cv r)) (synCsn (.cv x)))))) :
    Nominal.NPrf (synWfn W (synCo A (synCmap) B)) :=
  by
  have dv_cache_0001 : r ∉ ((synCo A (synCmap) B)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cmap, Finset.mem_union, dv_A_r,
          dv_B_r, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @gFnmpt r (synCo A (synCmap) B) (synCima (synCcnv (.cv r)) (synCsn (.cv x))) W
      (synCvv) dv_cache_0001 hyp_enprmaplem2_1
  have p0001 := @gVex r
  have p0002 := @gCnvex (.cv r) p0001
  have p0003 := @gSnex (.cv x)
  have p0004 := @gImaex (synCcnv (.cv r)) (synCsn (.cv x)) p0002 p0003
  have p0005 :=
    @gA1i (.classMem (synCima (synCcnv (.cv r)) (synCsn (.cv x))) (synCvv))
      (.classMem (.cv r) (synCo A (synCmap) B)) p0004
  have p0006 :=
    @gMprg (.classMem (synCima (synCcnv (.cv r)) (synCsn (.cv x))) (synCvv))
      (synWfn W (synCo A (synCmap) B)) r (synCo A (synCmap) B) p0000 p0005
  exact p0006


end NFChoice.DirectNominalPrf.WPPReplay

end
