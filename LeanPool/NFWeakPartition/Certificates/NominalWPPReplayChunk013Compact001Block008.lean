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

@[expose]
noncomputable def g_enpw1lem1 (x : Var) (y : Var) (g : Var) (dv_g_x : g ≠ x)
    (dv_g_y : g ≠ y) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classMem (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
        (syn_cvv)) :=
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
  have dv_cache_0001 : p ∉ ((syn_csn (syn_cop (.cv x) (.cv y)))).fv := by
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
      ((syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
          (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)))).fv :=
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
  have dv_cache_0005 : a ∉ ((syn_csn (syn_cop (.cv x) (.cv y)))).fv :=
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
  have dv_cache_0006 : a ∉ ((syn_csi (syn_ccnv (syn_c1st)))).fv :=
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
  have dv_cache_0007 : a ∉ ((syn_c1st)).fv :=
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
  have dv_cache_0008 : b ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
  have dv_cache_0010 : b ∉ ((syn_ccnv (syn_c1st))).fv :=
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
  have dv_cache_0012 : b ∉ ((Wff.classEq (.cv a) (syn_csn (.cv x)))).fv :=
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
  have dv_cache_0013 : a ∉ ((syn_csn (.cv x))).fv :=
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
  have dv_cache_0014 : a ∉ ((syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv x)))).fv :=
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
  have dv_cache_0015 : a ∉ ((syn_csi (syn_ccnv (syn_c2nd)))).fv :=
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
  have dv_cache_0016 : a ∉ ((syn_c2nd)).fv :=
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
  have dv_cache_0017 : b ∉ ((syn_ccnv (syn_c2nd))).fv :=
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
  have dv_cache_0019 : b ∉ ((Wff.classEq (.cv a) (syn_csn (.cv y)))).fv :=
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
  have dv_cache_0020 : a ∉ ((syn_csn (.cv y))).fv :=
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
  have dv_cache_0021 : a ∉ ((syn_wbr (.cv p) (syn_c2nd) (syn_csn (.cv y)))).fv :=
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
  have dv_cache_0022 : p ∉ ((syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))).fv :=
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
      ((syn_cuni1 (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
              (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)))).fv :=
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
      ((syn_cuni1 (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
              (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)))).fv :=
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
  have p0000 := @g_vex x
  have p0001 := @g_vex y
  have p0002 := @g_opex (.cv x) (.cv y) p0000 p0001
  have p0003 :=
    @g_eluni1 (syn_cop (.cv x) (.cv y))
      (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
          (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g))
      p0002
  have p0004 :=
    @g_elima p (syn_csn (syn_cop (.cv x) (.cv y)))
      (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
        (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)))
      (.cv g) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0005 :=
    @g_brin (.cv p) (syn_csn (syn_cop (.cv x) (.cv y)))
      (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
      (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))
  have p0006 :=
    @g_brco a (.cv p) (syn_csn (syn_cop (.cv x) (.cv y))) (syn_csi (syn_ccnv (syn_c1st)))
      (syn_c1st) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0007 :=
    @g_ancom (syn_wbr (.cv p) (syn_c1st) (.cv a))
      (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y))))
  have p0008 :=
    @g_brsnsi2 b (syn_cop (.cv x) (.cv y)) (.cv a) (syn_ccnv (syn_c1st)) dv_cache_0008
      dv_cache_0009 dv_cache_0010 p0002
  have p0009 :=
    @g_ancom (.classEq (.cv a) (syn_csn (.cv b)))
      (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y)))
  have p0010 := @g_brcnv (.cv b) (syn_cop (.cv x) (.cv y)) (syn_c1st)
  have p0011 := @g_opbr1st (.cv x) (.cv y) (.cv b) p0000 p0001
  have p0012 := @g_equcom x b
  have p0013_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv b)) (.objEq x b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c1st syn_copab
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
    @g_n_3bitri (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y)))
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c1st) (.cv b)) (.objEq x b) (.objEq b x)
      p0010 p0013_e01_recanon p0012
  have p0014 :=
    @g_anbi1i (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y)))
      (.objEq b x) (.classEq (.cv a) (syn_csn (.cv b))) p0013
  have p0015 :=
    @g_bitri
      (syn_wa (.classEq (.cv a) (syn_csn (.cv b)))
        (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y))))
      (syn_wa (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y)))
        (.classEq (.cv a) (syn_csn (.cv b))))
      (syn_wa (.objEq b x) (.classEq (.cv a) (syn_csn (.cv b)))) p0009 p0014
  have p0016 :=
    @g_exbii
      (syn_wa (.classEq (.cv a) (syn_csn (.cv b)))
        (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y))))
      (syn_wa (.objEq b x) (.classEq (.cv a) (syn_csn (.cv b)))) b p0015
  have p0017 := @g_sneq (.cv b) (.cv x)
  have p0018_e00_recanon :
    Nominal.NPrf (.imp (.objEq b x) (.classEq (syn_csn (.cv b)) (syn_csn (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0017
  have p0018 :=
    @g_eqeq2d (.objEq b x) (syn_csn (.cv b)) (syn_csn (.cv x)) (.cv a) p0018_e00_recanon
  have p0019_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (.cv x)) (syn_wb (.classEq (.cv a) (syn_csn (.cv b)))
          (.classEq (.cv a) (syn_csn (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0019 :=
    @g_ceqsexv (.classEq (.cv a) (syn_csn (.cv b))) (.classEq (.cv a) (syn_csn (.cv x))) b
      (.cv x) dv_cache_0011 dv_cache_0012 p0000 p0019_e01_recanon
  have p0020_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex b (syn_wa (.objEq b x) (.classEq (.cv a) (syn_csn (.cv b)))))
        (.classEq (.cv a) (syn_csn (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_csn
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
    @g_n_3bitri
      (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y))))
      (syn_wex b (syn_wa (.classEq (.cv a) (syn_csn (.cv b)))
          (syn_wbr (.cv b) (syn_ccnv (syn_c1st)) (syn_cop (.cv x) (.cv y)))))
      (syn_wex b (syn_wa (.objEq b x) (.classEq (.cv a) (syn_csn (.cv b)))))
      (.classEq (.cv a) (syn_csn (.cv x))) p0008 p0016 p0020_e02_recanon
  have p0021 :=
    @g_anbi1i
      (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y))))
      (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv p) (syn_c1st) (.cv a)) p0020
  have p0022 :=
    @g_bitri
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv a))
        (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y)))))
      (syn_wa (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st)))
          (syn_csn (syn_cop (.cv x) (.cv y)))) (syn_wbr (.cv p) (syn_c1st) (.cv a)))
      (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv p) (syn_c1st) (.cv a)))
      p0007 p0021
  have p0023 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv a))
        (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st))) (syn_csn (syn_cop (.cv x) (.cv y)))))
      (syn_wa (.classEq (.cv a) (syn_csn (.cv x))) (syn_wbr (.cv p) (syn_c1st) (.cv a))) a
      p0022
  have p0024 := @g_snex (.cv x)
  have p0025 := @g_breq2 (.cv a) (syn_csn (.cv x)) (.cv p) (syn_c1st)
  have p0026 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c1st) (.cv a))
      (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv x))) a (syn_csn (.cv x)) dv_cache_0013
      dv_cache_0014 p0024 p0025
  have p0027 :=
    @g_n_3bitri
      (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
        (syn_csn (syn_cop (.cv x) (.cv y))))
      (syn_wex a (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv a))
          (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c1st)))
            (syn_csn (syn_cop (.cv x) (.cv y))))))
      (syn_wex a (syn_wa (.classEq (.cv a) (syn_csn (.cv x)))
          (syn_wbr (.cv p) (syn_c1st) (.cv a))))
      (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv x))) p0006 p0023 p0026
  have p0028 :=
    @g_brco a (.cv p) (syn_csn (syn_cop (.cv x) (.cv y))) (syn_csi (syn_ccnv (syn_c2nd)))
      (syn_c2nd) dv_cache_0004 dv_cache_0005 dv_cache_0015 dv_cache_0016
  have p0029 :=
    @g_brsnsi2 b (syn_cop (.cv x) (.cv y)) (.cv a) (syn_ccnv (syn_c2nd)) dv_cache_0008
      dv_cache_0009 dv_cache_0017 p0002
  have p0030 := @g_brcnv (.cv b) (syn_cop (.cv x) (.cv y)) (syn_c2nd)
  have p0031 := @g_opbr2nd (.cv x) (.cv y) (.cv b) p0000 p0001
  have p0032 := @g_equcom y b
  have p0033_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv b)) (.objEq y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_c2nd syn_copab
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
    @g_n_3bitri (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (syn_cop (.cv x) (.cv y)))
      (syn_wbr (syn_cop (.cv x) (.cv y)) (syn_c2nd) (.cv b)) (.objEq y b) (.objEq b y)
      p0030 p0033_e01_recanon p0032
  have p0034 :=
    @g_anbi2i (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (syn_cop (.cv x) (.cv y)))
      (.objEq b y) (.classEq (.cv a) (syn_csn (.cv b))) p0033
  have p0035 := @g_ancom (.classEq (.cv a) (syn_csn (.cv b))) (.objEq b y)
  have p0036 :=
    @g_bitri
      (syn_wa (.classEq (.cv a) (syn_csn (.cv b)))
        (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (syn_cop (.cv x) (.cv y))))
      (syn_wa (.classEq (.cv a) (syn_csn (.cv b))) (.objEq b y))
      (syn_wa (.objEq b y) (.classEq (.cv a) (syn_csn (.cv b)))) p0034 p0035
  have p0037 :=
    @g_exbii
      (syn_wa (.classEq (.cv a) (syn_csn (.cv b)))
        (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (syn_cop (.cv x) (.cv y))))
      (syn_wa (.objEq b y) (.classEq (.cv a) (syn_csn (.cv b)))) b p0036
  have p0038 := @g_sneq (.cv b) (.cv y)
  have p0039_e00_recanon :
    Nominal.NPrf (.imp (.objEq b y) (.classEq (syn_csn (.cv b)) (syn_csn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0039 :=
    @g_eqeq2d (.objEq b y) (syn_csn (.cv b)) (syn_csn (.cv y)) (.cv a) p0039_e00_recanon
  have p0040_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv b) (.cv y)) (syn_wb (.classEq (.cv a) (syn_csn (.cv b)))
          (.classEq (.cv a) (syn_csn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0039
  have p0040 :=
    @g_ceqsexv (.classEq (.cv a) (syn_csn (.cv b))) (.classEq (.cv a) (syn_csn (.cv y))) b
      (.cv y) dv_cache_0018 dv_cache_0019 p0001 p0040_e01_recanon
  have p0041_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wex b (syn_wa (.objEq b y) (.classEq (.cv a) (syn_csn (.cv b)))))
        (.classEq (.cv a) (syn_csn (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wex syn_wa syn_csn
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
    @g_n_3bitri
      (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y))))
      (syn_wex b (syn_wa (.classEq (.cv a) (syn_csn (.cv b)))
          (syn_wbr (.cv b) (syn_ccnv (syn_c2nd)) (syn_cop (.cv x) (.cv y)))))
      (syn_wex b (syn_wa (.objEq b y) (.classEq (.cv a) (syn_csn (.cv b)))))
      (.classEq (.cv a) (syn_csn (.cv y))) p0029 p0037 p0041_e02_recanon
  have p0042 :=
    @g_anbi2i
      (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y))))
      (.classEq (.cv a) (syn_csn (.cv y))) (syn_wbr (.cv p) (syn_c2nd) (.cv a)) p0041
  have p0043 :=
    @g_ancom (syn_wbr (.cv p) (syn_c2nd) (.cv a)) (.classEq (.cv a) (syn_csn (.cv y)))
  have p0044 :=
    @g_bitri
      (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv a))
        (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y)))))
      (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv a)) (.classEq (.cv a) (syn_csn (.cv y))))
      (syn_wa (.classEq (.cv a) (syn_csn (.cv y))) (syn_wbr (.cv p) (syn_c2nd) (.cv a)))
      p0042 p0043
  have p0045 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv a))
        (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c2nd))) (syn_csn (syn_cop (.cv x) (.cv y)))))
      (syn_wa (.classEq (.cv a) (syn_csn (.cv y))) (syn_wbr (.cv p) (syn_c2nd) (.cv a))) a
      p0044
  have p0046 := @g_snex (.cv y)
  have p0047 := @g_breq2 (.cv a) (syn_csn (.cv y)) (.cv p) (syn_c2nd)
  have p0048 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c2nd) (.cv a))
      (syn_wbr (.cv p) (syn_c2nd) (syn_csn (.cv y))) a (syn_csn (.cv y)) dv_cache_0020
      dv_cache_0021 p0046 p0047
  have p0049 :=
    @g_n_3bitri
      (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))
        (syn_csn (syn_cop (.cv x) (.cv y))))
      (syn_wex a (syn_wa (syn_wbr (.cv p) (syn_c2nd) (.cv a))
          (syn_wbr (.cv a) (syn_csi (syn_ccnv (syn_c2nd)))
            (syn_csn (syn_cop (.cv x) (.cv y))))))
      (syn_wex a (syn_wa (.classEq (.cv a) (syn_csn (.cv y)))
          (syn_wbr (.cv p) (syn_c2nd) (.cv a))))
      (syn_wbr (.cv p) (syn_c2nd) (syn_csn (.cv y))) p0028 p0045 p0048
  have p0050 :=
    @g_anbi12i
      (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
        (syn_csn (syn_cop (.cv x) (.cv y))))
      (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv x)))
      (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))
        (syn_csn (syn_cop (.cv x) (.cv y))))
      (syn_wbr (.cv p) (syn_c2nd) (syn_csn (.cv y))) p0027 p0049
  have p0051 := @g_op1st2nd (syn_csn (.cv x)) (syn_csn (.cv y)) (.cv p) p0024 p0046
  have p0052 :=
    @g_n_3bitri
      (syn_wbr (.cv p) (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
          (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)))
        (syn_csn (syn_cop (.cv x) (.cv y))))
      (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
          (syn_csn (syn_cop (.cv x) (.cv y))))
        (syn_wbr (.cv p) (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))
          (syn_csn (syn_cop (.cv x) (.cv y)))))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_csn (.cv x)))
        (syn_wbr (.cv p) (syn_c2nd) (syn_csn (.cv y))))
      (.classEq (.cv p) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))) p0005 p0050 p0051
  have p0053 :=
    @g_rexbii
      (syn_wbr (.cv p) (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
          (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)))
        (syn_csn (syn_cop (.cv x) (.cv y))))
      (.classEq (.cv p) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))) p (.cv g) p0052
  have p0054 :=
    @g_bitri
      (.classMem (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cima
          (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
            (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)))
      (syn_wrex p (.cv g) (syn_wbr (.cv p)
          (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
            (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)))
          (syn_csn (syn_cop (.cv x) (.cv y)))))
      (syn_wrex p (.cv g) (.classEq (.cv p) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))))
      p0004 p0053
  have p0055 := (Nominal.biimpRefl (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
  have p0056 :=
    @g_risset p (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) (.cv g) dv_cache_0022
      dv_cache_0003
  have p0057 :=
    @g_bitr2i (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (.classMem (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y))) (.cv g))
      (syn_wrex p (.cv g) (.classEq (.cv p) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))))
      p0055 p0056
  have p0058 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv x) (.cv y)) (syn_cuni1 (syn_cima
            (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
              (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g))))
      (.classMem (syn_csn (syn_cop (.cv x) (.cv y))) (syn_cima
          (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
            (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)))
      (syn_wrex p (.cv g) (.classEq (.cv p) (syn_cop (syn_csn (.cv x)) (syn_csn (.cv y)))))
      (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) p0003 p0054 p0057
  have p0059 :=
    @g_opabbi2i (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) x y
      (syn_cuni1 (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
            (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)))
      dv_cache_0023 dv_cache_0024 dv_cache_0025 p0058
  have p0060 := @g_n_1stex
  have p0061 := @g_cnvex (syn_c1st) p0060
  have p0062 := @g_siex (syn_ccnv (syn_c1st)) p0061
  have p0064 := @g_coex (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st) p0062 p0060
  have p0065 := @g_n_2ndex
  have p0066 := @g_cnvex (syn_c2nd) p0065
  have p0067 := @g_siex (syn_ccnv (syn_c2nd)) p0066
  have p0069 := @g_coex (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd) p0067 p0065
  have p0070 :=
    @g_inex (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
      (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)) p0064 p0069
  have p0071 := @g_vex g
  have p0072 :=
    @g_imaex
      (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
        (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd)))
      (.cv g) p0070 p0071
  have p0073 :=
    @g_uni1ex
      (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
          (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g))
      p0072
  have p0074 :=
    @g_eqeltrri
      (syn_cuni1 (syn_cima (syn_cin (syn_ccom (syn_csi (syn_ccnv (syn_c1st))) (syn_c1st))
            (syn_ccom (syn_csi (syn_ccnv (syn_c2nd))) (syn_c2nd))) (.cv g)))
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (syn_cvv)
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

@[expose]
noncomputable def g_enpw1 (A : Class) (B : Class) :
    Nominal.NPrf
      (syn_wb (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B))) :=
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
    f ∉ ((syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b)))).fv :=
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
  have dv_cache_0004 : g ∉ ((syn_cpw1 (.cv a))).fv :=
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
  have dv_cache_0005 : g ∉ ((syn_cpw1 (.cv b))).fv :=
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
    y ∉ ((syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))).fv :=
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
    z ∉ ((syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))).fv :=
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
  have dv_cache_0008 : z ∉ ((syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))).fv :=
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
  have dv_cache_0009 : y ∉ ((syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z)))).fv :=
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
    x ∉ ((syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))).fv :=
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
  have dv_cache_0013 : z ∉ ((syn_csn (.cv x))).fv :=
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
  have dv_cache_0018 : y ∉ ((syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv w)))).fv :=
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
      ((Wff.imp (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z))
          (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))).fv :=
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
    z ∉ ((syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))).fv :=
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
  have dv_cache_0021 : y ∉ ((Wff.classMem (syn_csn (.cv x)) (syn_cdm (.cv g)))).fv :=
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
  have dv_cache_0023 : x ∉ ((syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y)))).fv :=
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
  have dv_cache_0026 : z ∉ ((syn_csn (.cv y))).fv :=
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
  have dv_cache_0029 : x ∉ ((syn_wbr (syn_csn (.cv w)) (.cv g) (syn_csn (.cv y)))).fv :=
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
      ((Wff.imp (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y)))
          (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))).fv :=
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
    z ∉ ((syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))).fv :=
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
  have dv_cache_0032 : x ∉ ((Wff.classMem (syn_csn (.cv y)) (syn_crn (.cv g)))).fv :=
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
  have dv_cache_0036 : g ∉ ((syn_wbr (.cv a) (syn_cen) (.cv b))).fv :=
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
      ((syn_wb (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B)))).fv :=
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
      ((syn_wb (syn_wbr A (syn_cen) (.cv b))
          (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 (.cv b))))).fv :=
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
  have p0000 := @g_brex A B (syn_cen)
  have p0001 := @g_brex (syn_cpw1 A) (syn_cpw1 B) (syn_cen)
  have p0002 := @g_pw1exb A
  have p0003 := @g_pw1exb B
  have p0004 :=
    @g_anbi12i (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem A (syn_cvv))
      (.classMem (syn_cpw1 B) (syn_cvv)) (.classMem B (syn_cvv)) p0002 p0003
  have p0005 :=
    @g_sylib (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B))
      (syn_wa (.classMem (syn_cpw1 A) (syn_cvv)) (.classMem (syn_cpw1 B) (syn_cvv)))
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv))) p0001 p0004
  have p0006 := @g_breq1 (.cv a) A (.cv b) (syn_cen)
  have p0007 := @g_pw1eq (.cv a) A
  have p0008 :=
    @g_breq1d (.classEq (.cv a) A) (syn_cpw1 (.cv a)) (syn_cpw1 A) (syn_cpw1 (.cv b))
      (syn_cen) p0007
  have p0009 :=
    @g_bibi12d (.classEq (.cv a) A) (syn_wbr (.cv a) (syn_cen) (.cv b))
      (syn_wbr A (syn_cen) (.cv b))
      (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b)))
      (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 (.cv b))) p0006 p0008
  have p0010 := @g_breq2 (.cv b) B A (syn_cen)
  have p0011 := @g_pw1eq (.cv b) B
  have p0012 :=
    @g_breq2d (.classEq (.cv b) B) (syn_cpw1 (.cv b)) (syn_cpw1 B) (syn_cpw1 A) (syn_cen)
      p0011
  have p0013 :=
    @g_bibi12d (.classEq (.cv b) B) (syn_wbr A (syn_cen) (.cv b)) (syn_wbr A (syn_cen) B)
      (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 (.cv b)))
      (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B)) p0010 p0012
  have p0014 := @g_bren (.cv a) (.cv b) f dv_cache_0001 dv_cache_0002
  have p0015 := @g_f1ofun (.cv a) (.cv b) (.cv f)
  have p0016 := @g_funsi (.cv f)
  have p0017 :=
    @g_syl (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfun (.cv f))
      (syn_wfun (syn_csi (.cv f))) p0015 p0016
  have p0018 := @g_f1odm (.cv a) (.cv b) (.cv f)
  have p0019 := @g_dmsi (.cv f)
  have p0020 := @g_pw1eq (syn_cdm (.cv f)) (.cv a)
  have p0021 :=
    @g_syl5eq (.classEq (syn_cdm (.cv f)) (.cv a)) (syn_cdm (syn_csi (.cv f)))
      (syn_cpw1 (syn_cdm (.cv f))) (syn_cpw1 (.cv a)) p0019 p0020
  have p0022 :=
    @g_syl (syn_wf1o (.cv f) (.cv a) (.cv b)) (.classEq (syn_cdm (.cv f)) (.cv a))
      (.classEq (syn_cdm (syn_csi (.cv f))) (syn_cpw1 (.cv a))) p0018 p0021
  have p0023 := (Nominal.biimpRefl (syn_wfn (syn_csi (.cv f)) (syn_cpw1 (.cv a))))
  have p0024 :=
    @g_sylanbrc (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfun (syn_csi (.cv f)))
      (.classEq (syn_cdm (syn_csi (.cv f))) (syn_cpw1 (.cv a)))
      (syn_wfn (syn_csi (.cv f)) (syn_cpw1 (.cv a))) p0017 p0022 p0023
  have p0025 := @g_f1of1 (.cv a) (.cv b) (.cv f)
  have p0026 := (Nominal.biimpRefl (syn_wf1 (.cv f) (.cv a) (.cv b)))
  have p0027 :=
    @g_simprbi (syn_wf1 (.cv f) (.cv a) (.cv b)) (syn_wf (.cv f) (.cv a) (.cv b))
      (syn_wfun (syn_ccnv (.cv f))) p0026
  have p0028 := @g_funsi (syn_ccnv (.cv f))
  have p0029 :=
    @g_n_3syl (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wf1 (.cv f) (.cv a) (.cv b))
      (syn_wfun (syn_ccnv (.cv f))) (syn_wfun (syn_csi (syn_ccnv (.cv f)))) p0025 p0027
      p0028
  have p0030 := @g_cnvsi (.cv f)
  have p0031 := @g_funeqi (syn_ccnv (syn_csi (.cv f))) (syn_csi (syn_ccnv (.cv f))) p0030
  have p0032 :=
    @g_sylibr (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfun (syn_csi (syn_ccnv (.cv f))))
      (syn_wfun (syn_ccnv (syn_csi (.cv f)))) p0029 p0031
  have p0033 := @g_f1ofo (.cv a) (.cv b) (.cv f)
  have p0034 := @g_forn (.cv a) (.cv b) (.cv f)
  have p0035 := @g_rnsi (.cv f)
  have p0036 := @g_dfrn4 (syn_csi (.cv f))
  have p0037 :=
    @g_eqtr3i (syn_crn (syn_csi (.cv f))) (syn_cpw1 (syn_crn (.cv f)))
      (syn_cdm (syn_ccnv (syn_csi (.cv f)))) p0035 p0036
  have p0038 := @g_pw1eq (syn_crn (.cv f)) (.cv b)
  have p0039 :=
    @g_syl5eqr (.classEq (syn_crn (.cv f)) (.cv b)) (syn_cdm (syn_ccnv (syn_csi (.cv f))))
      (syn_cpw1 (syn_crn (.cv f))) (syn_cpw1 (.cv b)) p0037 p0038
  have p0040 :=
    @g_n_3syl (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfo (.cv f) (.cv a) (.cv b))
      (.classEq (syn_crn (.cv f)) (.cv b))
      (.classEq (syn_cdm (syn_ccnv (syn_csi (.cv f)))) (syn_cpw1 (.cv b))) p0033 p0034
      p0039
  have p0041 :=
    (Nominal.biimpRefl (syn_wfn (syn_ccnv (syn_csi (.cv f))) (syn_cpw1 (.cv b))))
  have p0042 :=
    @g_sylanbrc (syn_wf1o (.cv f) (.cv a) (.cv b)) (syn_wfun (syn_ccnv (syn_csi (.cv f))))
      (.classEq (syn_cdm (syn_ccnv (syn_csi (.cv f)))) (syn_cpw1 (.cv b)))
      (syn_wfn (syn_ccnv (syn_csi (.cv f))) (syn_cpw1 (.cv b))) p0032 p0040 p0041
  have p0043 := @g_dff1o4 (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (syn_csi (.cv f))
  have p0044 :=
    @g_sylanbrc (syn_wf1o (.cv f) (.cv a) (.cv b))
      (syn_wfn (syn_csi (.cv f)) (syn_cpw1 (.cv a)))
      (syn_wfn (syn_ccnv (syn_csi (.cv f))) (syn_cpw1 (.cv b)))
      (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) p0024 p0042 p0043
  have p0045 := @g_vex f
  have p0046 := @g_siex (.cv f) p0045
  have p0047 := @g_f1oen (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (syn_csi (.cv f)) p0046
  have p0048 :=
    @g_syl (syn_wf1o (.cv f) (.cv a) (.cv b))
      (syn_wf1o (syn_csi (.cv f)) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))) p0044 p0047
  have p0049 :=
    @g_exlimiv (syn_wf1o (.cv f) (.cv a) (.cv b))
      (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))) f dv_cache_0003 p0048
  have p0050 :=
    @g_sylbi (syn_wbr (.cv a) (syn_cen) (.cv b))
      (syn_wex f (syn_wf1o (.cv f) (.cv a) (.cv b)))
      (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))) p0014 p0049
  have p0051 :=
    @g_bren (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) g dv_cache_0004 dv_cache_0005
  have p0052 := @g_f1ofun (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv g)
  have p0053 := @g_fununiq (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_csn (.cv z)) (.cv g)
  have p0054 := @g_vex y
  have p0055 := @g_sneqb (.cv y) (.cv z) p0054
  have p0056_e01_recanon :
    Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
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
    @g_sylib
      (syn_w3a (syn_wfun (.cv g)) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
        (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z))))
      (.classEq (syn_csn (.cv y)) (syn_csn (.cv z))) (.objEq y z) p0053 p0056_e01_recanon
  have p0057 :=
    @g_n_3expib (syn_wfun (.cv g)) (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z))) (.objEq y z) p0056
  have p0058 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_wfun (.cv g))
      (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
          (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z)))) (.objEq y z))
      p0052 p0057
  have p0059 :=
    @g_alrimivv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
          (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z)))) (.objEq y z))
      y z dv_cache_0006 dv_cache_0007 p0058
  have p0060 := @g_sneq (.cv y) (.cv z)
  have p0061_e00_recanon :
    Nominal.NPrf (.imp (.objEq y z) (.classEq (syn_csn (.cv y)) (syn_csn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0060
  have p0061 :=
    @g_breq2d (.objEq y z) (syn_csn (.cv y)) (syn_csn (.cv z)) (syn_csn (.cv x)) (.cv g)
      p0061_e00_recanon
  have p0062 :=
    @g_mo4 (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z))) y z dv_cache_0008
      dv_cache_0009 dv_cache_0010 p0061
  have p0063 :=
    @g_sylibr (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.all y (.all z (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
              (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv z)))) (.objEq y z))))
      (syn_wmo y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0059 p0062
  have p0064 :=
    @g_alrimiv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wmo y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) x dv_cache_0011
      p0063
  have p0065 :=
    @g_funopab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) x y dv_cache_0012
  have p0066 :=
    @g_sylibr (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.all x (syn_wmo y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      (syn_wfun (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      p0064 p0065
  have p0067 :=
    @g_dmopab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) x y dv_cache_0012
  have p0068 := @g_eldm z (syn_csn (.cv x)) (.cv g) dv_cache_0013 dv_cache_0014
  have p0069 := @g_brelrn (syn_csn (.cv x)) (.cv z) (.cv g)
  have p0070 := @g_f1ofo (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv g)
  have p0071 := @g_forn (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv g)
  have p0072 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wfo (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.classEq (syn_crn (.cv g)) (syn_cpw1 (.cv b))) p0070 p0071
  have p0073 :=
    @g_eleq2d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_crn (.cv g))
      (syn_cpw1 (.cv b)) (.cv z) p0072
  have p0074 := @g_elpw1 w (.cv z) (.cv b) dv_cache_0015 dv_cache_0016
  have p0075 := @g_breq2 (.cv z) (syn_csn (.cv w)) (syn_csn (.cv x)) (.cv g)
  have p0076 := @g_vex w
  have p0077 := @g_sneq (.cv y) (.cv w)
  have p0078_e00_recanon :
    Nominal.NPrf (.imp (.objEq y w) (.classEq (syn_csn (.cv y)) (syn_csn (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0077
  have p0078 :=
    @g_breq2d (.objEq y w) (syn_csn (.cv y)) (syn_csn (.cv w)) (syn_csn (.cv x)) (.cv g)
      p0078_e00_recanon
  have p0079_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv w))
        (syn_wb (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
          (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv w))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0078
  have p0079 :=
    @g_spcev (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv w))) y (.cv w) dv_cache_0017
      dv_cache_0018 p0076 p0079_e01_recanon
  have p0080 :=
    @g_syl6bi (.classEq (.cv z) (syn_csn (.cv w)))
      (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z))
      (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv w)))
      (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0075 p0079
  have p0081 :=
    @g_rexlimivw (.classEq (.cv z) (syn_csn (.cv w)))
      (.imp (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z))
        (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      w (.cv b) dv_cache_0019 p0080
  have p0082 :=
    @g_sylbi (.classMem (.cv z) (syn_cpw1 (.cv b)))
      (syn_wrex w (.cv b) (.classEq (.cv z) (syn_csn (.cv w))))
      (.imp (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z))
        (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      p0074 p0081
  have p0083 :=
    @g_syl6bi (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.classMem (.cv z) (syn_crn (.cv g))) (.classMem (.cv z) (syn_cpw1 (.cv b)))
      (.imp (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z))
        (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      p0073 p0082
  have p0084 :=
    @g_com23 (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.classMem (.cv z) (syn_crn (.cv g))) (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z))
      (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0083
  have p0085 :=
    @g_mpdi (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z)) (.classMem (.cv z) (syn_crn (.cv g)))
      (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0069 p0084
  have p0086 :=
    @g_exlimdv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z))
      (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) z dv_cache_0020
      dv_cache_0007 p0085
  have p0087 :=
    @g_syl5bi (.classMem (syn_csn (.cv x)) (syn_cdm (.cv g)))
      (syn_wex z (syn_wbr (syn_csn (.cv x)) (.cv g) (.cv z)))
      (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0068 p0086
  have p0088 := @g_breldm (syn_csn (.cv x)) (syn_csn (.cv y)) (.cv g)
  have p0089 :=
    @g_exlimiv (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (.classMem (syn_csn (.cv x)) (syn_cdm (.cv g))) y dv_cache_0021 p0088
  have p0090 :=
    @g_impbid1 (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.classMem (syn_csn (.cv x)) (syn_cdm (.cv g)))
      (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0087 p0089
  have p0091 := @g_f1odm (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv g)
  have p0092 :=
    @g_eleq2d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_cdm (.cv g))
      (syn_cpw1 (.cv a)) (syn_csn (.cv x)) p0091
  have p0093 :=
    @g_bitr3d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.classMem (syn_csn (.cv x)) (syn_cdm (.cv g)))
      (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv a))) p0090 p0092
  have p0094 := @g_snelpw1 (.cv x) (.cv a)
  have p0095_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv a))) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw
          syn_wss syn_c1c syn_wex
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
    @g_syl6bb (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
      (.classMem (syn_csn (.cv x)) (syn_cpw1 (.cv a))) (.objMem x a) p0093
      p0095_e01_recanon
  have p0096_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
        (syn_wb (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
          (.classMem (.cv x) (.cv a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wf1o syn_wa syn_wf1 syn_wfo syn_cpw1 syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_wb
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
    @g_eqabcdv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) x (.cv a)
      dv_cache_0022 dv_cache_0011 p0096_e00_recanon
  have p0097 :=
    @g_syl5eq (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_cdm (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      (.cab x (syn_wex y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.cv a)
      p0067 p0096
  have p0098 :=
    (Nominal.biimpRefl
      (syn_wfn (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv a)))
  have p0099 :=
    @g_sylanbrc (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wfun (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      (.classEq (syn_cdm (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
        (.cv a))
      (syn_wfn (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv a))
      p0066 p0097 p0098
  have p0100 := @g_f1ocnv (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)) (.cv g)
  have p0101 := @g_f1ofun (syn_cpw1 (.cv b)) (syn_cpw1 (.cv a)) (syn_ccnv (.cv g))
  have p0102 :=
    @g_fununiq (syn_csn (.cv y)) (syn_csn (.cv x)) (syn_csn (.cv z)) (syn_ccnv (.cv g))
  have p0103 :=
    @g_n_3expib (syn_wfun (syn_ccnv (.cv g)))
      (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv x)))
      (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv z)))
      (.classEq (syn_csn (.cv x)) (syn_csn (.cv z))) p0102
  have p0104 := @g_brcnv (syn_csn (.cv y)) (syn_csn (.cv x)) (.cv g)
  have p0105 := @g_brcnv (syn_csn (.cv y)) (syn_csn (.cv z)) (.cv g)
  have p0106 :=
    @g_anbi12i (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv x)))
      (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv z)))
      (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y))) p0104 p0105
  have p0107 := @g_vex x
  have p0108 := @g_sneqb (.cv x) (.cv z) p0107
  have p0109_e02_recanon :
    Nominal.NPrf (syn_wb (.classEq (syn_csn (.cv x)) (syn_csn (.cv z))) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn
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
    @g_n_3imtr3g (syn_wfun (syn_ccnv (.cv g)))
      (syn_wa (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv x)))
        (syn_wbr (syn_csn (.cv y)) (syn_ccnv (.cv g)) (syn_csn (.cv z))))
      (.classEq (syn_csn (.cv x)) (syn_csn (.cv z)))
      (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
        (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y))))
      (.objEq x z) p0103 p0106 p0109_e02_recanon
  have p0110 :=
    @g_n_3syl (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wf1o (syn_ccnv (.cv g)) (syn_cpw1 (.cv b)) (syn_cpw1 (.cv a)))
      (syn_wfun (syn_ccnv (.cv g)))
      (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
          (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y)))) (.objEq x z))
      p0100 p0101 p0109
  have p0111 :=
    @g_alrimivv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
          (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y)))) (.objEq x z))
      x z dv_cache_0011 dv_cache_0007 p0110
  have p0112 := @g_sneq (.cv x) (.cv z)
  have p0113_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_csn (.cv x)) (syn_csn (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0112
  have p0113 :=
    @g_breq1d (.objEq x z) (syn_csn (.cv x)) (syn_csn (.cv z)) (syn_csn (.cv y)) (.cv g)
      p0113_e00_recanon
  have p0114 :=
    @g_mo4 (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y))) x z dv_cache_0008
      dv_cache_0023 dv_cache_0024 p0113
  have p0115 :=
    @g_sylibr (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.all x (.all z (.imp (syn_wa (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
              (syn_wbr (syn_csn (.cv z)) (.cv g) (syn_csn (.cv y)))) (.objEq x z))))
      (syn_wmo x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0111 p0114
  have p0116 :=
    @g_alrimiv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wmo x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) y dv_cache_0006
      p0115
  have p0117 :=
    @g_funopab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) y x dv_cache_0025
  have p0118 :=
    @g_sylibr (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.all y (syn_wmo x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      (syn_wfun (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      p0116 p0117
  have p0119 :=
    @g_dmopab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) y x dv_cache_0025
  have p0120 := @g_elrn z (syn_csn (.cv y)) (.cv g) dv_cache_0026 dv_cache_0014
  have p0121 := @g_breldm (.cv z) (syn_csn (.cv y)) (.cv g)
  have p0122 :=
    @g_eleq2d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_cdm (.cv g))
      (syn_cpw1 (.cv a)) (.cv z) p0091
  have p0123 := @g_elpw1 w (.cv z) (.cv a) dv_cache_0015 dv_cache_0027
  have p0124 := @g_breq1 (.cv z) (syn_csn (.cv w)) (syn_csn (.cv y)) (.cv g)
  have p0125 := @g_sneq (.cv x) (.cv w)
  have p0126_e00_recanon :
    Nominal.NPrf (.imp (.objEq x w) (.classEq (syn_csn (.cv x)) (syn_csn (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0125
  have p0126 :=
    @g_breq1d (.objEq x w) (syn_csn (.cv x)) (syn_csn (.cv w)) (syn_csn (.cv y)) (.cv g)
      p0126_e00_recanon
  have p0127_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv w))
        (syn_wb (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
          (syn_wbr (syn_csn (.cv w)) (.cv g) (syn_csn (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wbr syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex
          syn_wex syn_cphi syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0126
  have p0127 :=
    @g_spcev (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv w)) (.cv g) (syn_csn (.cv y))) x (.cv w) dv_cache_0028
      dv_cache_0029 p0076 p0127_e01_recanon
  have p0128 :=
    @g_syl6bi (.classEq (.cv z) (syn_csn (.cv w)))
      (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y)))
      (syn_wbr (syn_csn (.cv w)) (.cv g) (syn_csn (.cv y)))
      (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0124 p0127
  have p0129 :=
    @g_rexlimivw (.classEq (.cv z) (syn_csn (.cv w)))
      (.imp (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y)))
        (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      w (.cv a) dv_cache_0030 p0128
  have p0130 :=
    @g_sylbi (.classMem (.cv z) (syn_cpw1 (.cv a)))
      (syn_wrex w (.cv a) (.classEq (.cv z) (syn_csn (.cv w))))
      (.imp (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y)))
        (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      p0123 p0129
  have p0131 :=
    @g_syl6bi (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.classMem (.cv z) (syn_cdm (.cv g))) (.classMem (.cv z) (syn_cpw1 (.cv a)))
      (.imp (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y)))
        (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      p0122 p0130
  have p0132 :=
    @g_com23 (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.classMem (.cv z) (syn_cdm (.cv g))) (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y)))
      (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0131
  have p0133 :=
    @g_mpdi (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y))) (.classMem (.cv z) (syn_cdm (.cv g)))
      (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0121 p0132
  have p0134 :=
    @g_exlimdv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y)))
      (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) z dv_cache_0031
      dv_cache_0007 p0133
  have p0135 :=
    @g_syl5bi (.classMem (syn_csn (.cv y)) (syn_crn (.cv g)))
      (syn_wex z (syn_wbr (.cv z) (.cv g) (syn_csn (.cv y))))
      (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0120 p0134
  have p0136 := @g_brelrn (syn_csn (.cv x)) (syn_csn (.cv y)) (.cv g)
  have p0137 :=
    @g_exlimiv (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))
      (.classMem (syn_csn (.cv y)) (syn_crn (.cv g))) x dv_cache_0032 p0136
  have p0138 :=
    @g_impbid1 (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.classMem (syn_csn (.cv y)) (syn_crn (.cv g)))
      (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0135 p0137
  have p0139 :=
    @g_eleq2d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))) (syn_crn (.cv g))
      (syn_cpw1 (.cv b)) (syn_csn (.cv y)) p0072
  have p0140 :=
    @g_bitr3d (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (.classMem (syn_csn (.cv y)) (syn_crn (.cv g)))
      (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
      (.classMem (syn_csn (.cv y)) (syn_cpw1 (.cv b))) p0138 p0139
  have p0141 := @g_snelpw1 (.cv y) (.cv b)
  have p0142_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_csn (.cv y)) (syn_cpw1 (.cv b))) (.objMem y b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_csn syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw
          syn_wss syn_c1c syn_wex
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
    @g_syl6bb (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
      (.classMem (syn_csn (.cv y)) (syn_cpw1 (.cv b))) (.objMem y b) p0140
      p0142_e01_recanon
  have p0143_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
        (syn_wb (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
          (.classMem (.cv y) (.cv b)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wf1o syn_wa syn_wf1 syn_wfo syn_cpw1 syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cpw syn_wss syn_c1c syn_wex syn_csn syn_wb
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
    @g_eqabcdv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) y (.cv b)
      dv_cache_0033 dv_cache_0006 p0143_e00_recanon
  have p0144 :=
    @g_syl5eq (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_cdm (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      (.cab y (syn_wex x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))) (.cv b)
      p0119 p0143
  have p0145 :=
    (Nominal.biimpRefl
      (syn_wfn (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b)))
  have p0146 :=
    @g_sylanbrc (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wfun (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      (.classEq (syn_cdm (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
        (.cv b))
      (syn_wfn (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b))
      p0118 p0144 p0145
  have p0147 :=
    @g_cnvopab (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))) x y dv_cache_0012
  have p0148 :=
    @g_fneq1i (.cv b)
      (syn_ccnv (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
      (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0147
  have p0149 :=
    @g_sylibr (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wfn (syn_copab y x (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv b))
      (syn_wfn (syn_ccnv (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
        (.cv b))
      p0146 p0148
  have p0150 :=
    @g_dff1o4 (.cv a) (.cv b)
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
  have p0151 :=
    @g_sylanbrc (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wfn (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) (.cv a))
      (syn_wfn (syn_ccnv (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))))
        (.cv b))
      (syn_wf1o (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
        (.cv a) (.cv b))
      p0099 p0149 p0150
  have p0152 := @g_enpw1lem1 x y g dv_cache_0034 dv_cache_0035 dv_cache_0012
  have p0153 :=
    @g_f1oen (.cv a) (.cv b)
      (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y)))) p0152
  have p0154 :=
    @g_syl (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wf1o (syn_copab x y (syn_wbr (syn_csn (.cv x)) (.cv g) (syn_csn (.cv y))))
        (.cv a) (.cv b))
      (syn_wbr (.cv a) (syn_cen) (.cv b)) p0151 p0153
  have p0155 :=
    @g_exlimiv (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b)))
      (syn_wbr (.cv a) (syn_cen) (.cv b)) g dv_cache_0036 p0154
  have p0156 :=
    @g_sylbi (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b)))
      (syn_wex g (syn_wf1o (.cv g) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv b))))
      (syn_wbr (.cv a) (syn_cen) (.cv b)) p0051 p0155
  have p0157 :=
    @g_impbii (syn_wbr (.cv a) (syn_cen) (.cv b))
      (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))) p0050 p0156
  have p0158 :=
    @g_vtocl2g
      (syn_wb (syn_wbr (.cv a) (syn_cen) (.cv b))
        (syn_wbr (syn_cpw1 (.cv a)) (syn_cen) (syn_cpw1 (.cv b))))
      (syn_wb (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 (.cv b))))
      (syn_wb (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B))) a b A
      B (syn_cvv) (syn_cvv) dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
      dv_cache_0041 p0009 p0013 p0157
  have p0159 :=
    @g_pm5_21nii (syn_wbr A (syn_cen) B)
      (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B)) p0000 p0005 p0158
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

@[expose]
noncomputable def g_enmap2lem1 (A : Class) (G : Class) (W : Class) (s : Var) (r : Var)
    (dv_A_s : s ∉ A.fv) (dv_G_s : s ∉ G.fv) (dv_r_s : r ≠ s)
    (hyp_enmap2lem1_1 : Nominal.NPrf (.classEq W
          (syn_cmpt s (syn_co G (syn_cmap) A) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) :
    Nominal.NPrf (.classMem W (syn_cvv)) :=
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
  have dv_cache_0001 : x ∉ ((syn_co G (syn_cmap) A)).fv := by
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
  have dv_cache_0002 : x ∉ ((syn_ccom (.cv s) (syn_ccnv (.cv r)))).fv :=
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
      ((syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
            (syn_cvv)))).fv :=
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
  have dv_cache_0007 : x ∉ ((syn_c1st)).fv :=
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
  have dv_cache_0008 : x ∉ ((syn_cop (.cv s) (syn_ccnv (.cv r)))).fv :=
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
    x ∉ ((syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv s) (syn_ccnv (.cv r))))).fv :=
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
  have dv_cache_0010 : p ∉ ((syn_cop (.cv s) (.cv x))).fv :=
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
      ((syn_ctxp (syn_ccom (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
            (syn_c1st)) (syn_c2nd))).fv :=
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
  have dv_cache_0012 : p ∉ ((syn_ccompose)).fv :=
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
  have dv_cache_0013 : p ∉ ((syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x))).fv :=
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
      ((syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                    (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose))
          (syn_co G (syn_cmap) A))).fv :=
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
      ((syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                    (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose))
          (syn_co G (syn_cmap) A))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_mpt s x
      (syn_co G (syn_cmap) A) (syn_ccom (.cv s) (syn_ccnv (.cv r))) dv_cache_0001
      dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_opelres (.cv s) (.cv x)
      (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
            (syn_c1st)) (syn_c2nd)) (syn_ccompose))
      (syn_co G (syn_cmap) A)
  have p0002 :=
    @g_trtxp (.cv p) (.cv s) (.cv x)
      (syn_ccom (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
        (syn_c1st))
      (syn_c2nd)
  have p0003 :=
    @g_brco x (.cv p) (.cv s)
      (syn_cin (syn_c1st)
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
      (syn_c1st) dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @g_ancom (syn_wbr (.cv p) (syn_c1st) (.cv x))
      (syn_wbr (.cv x) (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
        (.cv s))
  have p0005 :=
    @g_brin (.cv x) (.cv s) (syn_c1st)
      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))
  have p0006 := @g_vex s
  have p0007 :=
    @g_brxp (.cv x) (.cv s) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
      (syn_cvv)
  have p0008 :=
    @g_mpbiran2
      (syn_wbr (.cv x)
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))
        (.cv s))
      (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))))
      (.classMem (.cv s) (syn_cvv)) p0006 p0007
  have p0009 := @g_eliniseg (syn_c2nd) (syn_ccnv (.cv r)) (.cv x)
  have p0010 :=
    @g_bitri
      (syn_wbr (.cv x)
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))
        (.cv s))
      (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))))
      (syn_wbr (.cv x) (syn_c2nd) (syn_ccnv (.cv r))) p0008 p0009
  have p0011 :=
    @g_anbi2i
      (syn_wbr (.cv x)
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))
        (.cv s))
      (syn_wbr (.cv x) (syn_c2nd) (syn_ccnv (.cv r))) (syn_wbr (.cv x) (syn_c1st) (.cv s))
      p0010
  have p0012 := @g_vex r
  have p0013 := @g_cnvex (.cv r) p0012
  have p0014 := @g_op1st2nd (.cv s) (syn_ccnv (.cv r)) (.cv x) p0006 p0013
  have p0015 :=
    @g_n_3bitri
      (syn_wbr (.cv x) (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
        (.cv s))
      (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv s)) (syn_wbr (.cv x)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))
          (.cv s)))
      (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv s))
        (syn_wbr (.cv x) (syn_c2nd) (syn_ccnv (.cv r))))
      (.classEq (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r)))) p0005 p0011 p0014
  have p0016 :=
    @g_anbi1i
      (syn_wbr (.cv x) (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
        (.cv s))
      (.classEq (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r))))
      (syn_wbr (.cv p) (syn_c1st) (.cv x)) p0015
  have p0017 :=
    @g_bitri
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
          (.cv s)))
      (syn_wa (syn_wbr (.cv x) (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
          (.cv s)) (syn_wbr (.cv p) (syn_c1st) (.cv x)))
      (syn_wa (.classEq (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r))))
        (syn_wbr (.cv p) (syn_c1st) (.cv x)))
      p0004 p0016
  have p0018 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x) (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
          (.cv s)))
      (syn_wa (.classEq (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r))))
        (syn_wbr (.cv p) (syn_c1st) (.cv x)))
      x p0017
  have p0019 := @g_opex (.cv s) (syn_ccnv (.cv r)) p0006 p0013
  have p0020 := @g_breq2 (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv p) (syn_c1st)
  have p0021 :=
    @g_ceqsexv (syn_wbr (.cv p) (syn_c1st) (.cv x))
      (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv s) (syn_ccnv (.cv r)))) x
      (syn_cop (.cv s) (syn_ccnv (.cv r))) dv_cache_0008 dv_cache_0009 p0019 p0020
  have p0022 :=
    @g_n_3bitri
      (syn_wbr (.cv p) (syn_ccom (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
          (syn_c1st)) (.cv s))
      (syn_wex x (syn_wa (syn_wbr (.cv p) (syn_c1st) (.cv x)) (syn_wbr (.cv x)
            (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
            (.cv s))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cop (.cv s) (syn_ccnv (.cv r))))
          (syn_wbr (.cv p) (syn_c1st) (.cv x))))
      (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv s) (syn_ccnv (.cv r)))) p0003 p0018 p0021
  have p0023 :=
    @g_anbi1i
      (syn_wbr (.cv p) (syn_ccom (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
          (syn_c1st)) (.cv s))
      (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv s) (syn_ccnv (.cv r))))
      (syn_wbr (.cv p) (syn_c2nd) (.cv x)) p0022
  have p0024 := @g_vex x
  have p0025 :=
    @g_op1st2nd (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x) (.cv p) p0019 p0024
  have p0026 :=
    @g_n_3bitri
      (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
            (syn_c1st)) (syn_c2nd)) (syn_cop (.cv s) (.cv x)))
      (syn_wa (syn_wbr (.cv p) (syn_ccom (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
            (syn_c1st)) (.cv s)) (syn_wbr (.cv p) (syn_c2nd) (.cv x)))
      (syn_wa (syn_wbr (.cv p) (syn_c1st) (syn_cop (.cv s) (syn_ccnv (.cv r))))
        (syn_wbr (.cv p) (syn_c2nd) (.cv x)))
      (.classEq (.cv p) (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x))) p0002
      p0023 p0025
  have p0027 :=
    @g_rexbii
      (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
            (syn_c1st)) (syn_c2nd)) (syn_cop (.cv s) (.cv x)))
      (.classEq (.cv p) (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x))) p
      (syn_ccompose) p0026
  have p0028 :=
    @g_elima p (syn_cop (.cv s) (.cv x))
      (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
          (syn_c1st)) (syn_c2nd))
      (syn_ccompose) dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0029 :=
    @g_risset p (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x)) (syn_ccompose)
      dv_cache_0013 dv_cache_0012
  have p0030 :=
    @g_n_3bitr4i
      (syn_wrex p (syn_ccompose) (syn_wbr (.cv p) (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                  (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_cop (.cv s) (.cv x))))
      (syn_wrex p (syn_ccompose)
        (.classEq (.cv p) (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x))))
      (.classMem (syn_cop (.cv s) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                  (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)))
      (.classMem (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x)) (syn_ccompose))
      p0027 p0028 p0029
  have p0031 :=
    (Nominal.biimpRefl (syn_wbr (syn_cop (.cv s) (syn_ccnv (.cv r))) (syn_ccompose) (.cv x)))
  have p0032 := @g_brcomposeg (.cv s) (syn_ccnv (.cv r)) (.cv x) (syn_cvv) (syn_cvv)
  have p0033 :=
    @g_mp2an (.classMem (.cv s) (syn_cvv)) (.classMem (syn_ccnv (.cv r)) (syn_cvv))
      (syn_wb (syn_wbr (syn_cop (.cv s) (syn_ccnv (.cv r))) (syn_ccompose) (.cv x))
        (.classEq (syn_ccom (.cv s) (syn_ccnv (.cv r))) (.cv x)))
      p0006 p0013 p0032
  have p0034 := @g_eqcom (syn_ccom (.cv s) (syn_ccnv (.cv r))) (.cv x)
  have p0035 :=
    @g_bitri (syn_wbr (syn_cop (.cv s) (syn_ccnv (.cv r))) (syn_ccompose) (.cv x))
      (.classEq (syn_ccom (.cv s) (syn_ccnv (.cv r))) (.cv x))
      (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) p0033 p0034
  have p0036 :=
    @g_n_3bitr2i
      (.classMem (syn_cop (.cv s) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                  (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)))
      (.classMem (syn_cop (syn_cop (.cv s) (syn_ccnv (.cv r))) (.cv x)) (syn_ccompose))
      (syn_wbr (syn_cop (.cv s) (syn_ccnv (.cv r))) (syn_ccompose) (.cv x))
      (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) p0030 p0031 p0035
  have p0037 :=
    @g_anbi2ci
      (.classMem (syn_cop (.cv s) (.cv x)) (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                  (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)))
      (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
      (.classMem (.cv s) (syn_co G (syn_cmap) A)) p0036
  have p0038 :=
    @g_bitri
      (.classMem (syn_cop (.cv s) (.cv x)) (syn_cres (syn_cima (syn_ctxp (syn_ccom
                (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                    (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose))
          (syn_co G (syn_cmap) A)))
      (syn_wa (.classMem (syn_cop (.cv s) (.cv x)) (syn_cima (syn_ctxp (syn_ccom
                (syn_cin (syn_c1st)
                  (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                    (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)))
        (.classMem (.cv s) (syn_co G (syn_cmap) A)))
      (syn_wa (.classMem (.cv s) (syn_co G (syn_cmap) A))
        (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))
      p0001 p0037
  have p0039 :=
    @g_opabbi2i
      (syn_wa (.classMem (.cv s) (syn_co G (syn_cmap) A))
        (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))
      s x
      (syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                  (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A))
      dv_cache_0014 dv_cache_0015 dv_cache_0003 p0038
  have p0040 :=
    @g_n_3eqtr4i
      (syn_cmpt s (syn_co G (syn_cmap) A) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
      (syn_copab s x (syn_wa (.classMem (.cv s) (syn_co G (syn_cmap) A))
          (.classEq (.cv x) (syn_ccom (.cv s) (syn_ccnv (.cv r))))))
      W
      (syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                  (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A))
      p0000 hyp_enmap2lem1_1 p0039
  have p0041 := @g_n_1stex
  have p0042 := @g_n_2ndex
  have p0043 := @g_cnvex (syn_c2nd) p0042
  have p0044 := @g_snex (syn_ccnv (.cv r))
  have p0045 := @g_imaex (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))) p0043 p0044
  have p0046 := @g_vvex
  have p0047 :=
    @g_xpex (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv) p0045
      p0046
  have p0048 :=
    @g_inex (syn_c1st)
      (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv))
      p0041 p0047
  have p0050 :=
    @g_coex
      (syn_cin (syn_c1st)
        (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
      (syn_c1st) p0048 p0041
  have p0052 :=
    @g_txpex
      (syn_ccom (syn_cin (syn_c1st)
          (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
        (syn_c1st))
      (syn_c2nd) p0050 p0042
  have p0053 := @g_composeex
  have p0054 :=
    @g_imaex
      (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
            (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
          (syn_c1st)) (syn_c2nd))
      (syn_ccompose) p0052 p0053
  have p0055 := @g_ovex G A (syn_cmap)
  have p0056 :=
    @g_resex
      (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
              (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r)))) (syn_cvv)))
            (syn_c1st)) (syn_c2nd)) (syn_ccompose))
      (syn_co G (syn_cmap) A) p0054 p0055
  have p0057 :=
    @g_eqeltri W
      (syn_cres (syn_cima (syn_ctxp (syn_ccom (syn_cin (syn_c1st)
                (syn_cxp (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_ccnv (.cv r))))
                  (syn_cvv))) (syn_c1st)) (syn_c2nd)) (syn_ccompose)) (syn_co G (syn_cmap) A))
      (syn_cvv) p0040 p0056
  exact p0057

@[expose]
noncomputable def g_enmap2lem2 (G : Class) (W : Class) (s : Var) (r : Var) (a : Var)
    (dv_G_s : s ∉ G.fv) (dv_a_s : a ≠ s)
    (hyp_enmap2lem2_1 : Nominal.NPrf (.classEq W (syn_cmpt s (syn_co G (syn_cmap) (.cv a))
            (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) :
    Nominal.NPrf (syn_wfn W (syn_co G (syn_cmap) (.cv a))) :=
  by
  have dv_cache_0001 : s ∉ ((syn_co G (syn_cmap) (.cv a))).fv := by
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
    @g_fnmpt s (syn_co G (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))) W
      (syn_cvv) dv_cache_0001 hyp_enmap2lem2_1
  have p0001 := @g_vex s
  have p0002 := @g_vex r
  have p0003 := @g_cnvex (.cv r) p0002
  have p0004 := @g_coex (.cv s) (syn_ccnv (.cv r)) p0001 p0003
  have p0005 :=
    @g_a1i (.classMem (syn_ccom (.cv s) (syn_ccnv (.cv r))) (syn_cvv))
      (.classMem (.cv s) (syn_co G (syn_cmap) (.cv a))) p0004
  have p0006 :=
    @g_mprg (.classMem (syn_ccom (.cv s) (syn_ccnv (.cv r))) (syn_cvv))
      (syn_wfn W (syn_co G (syn_cmap) (.cv a))) s (syn_co G (syn_cmap) (.cv a)) p0000
      p0005
  exact p0006

@[expose]
noncomputable def g_enmap2lem3 (S : Class) (T : Class) (G : Class) (W : Class) (s : Var)
    (r : Var) (a : Var) (b : Var) (dv_G_s : s ∉ G.fv) (dv_S_s : s ∉ S.fv) (dv_a_s : a ≠ s)
    (dv_r_s : r ≠ s)
    (hyp_enmap2lem3_1 : Nominal.NPrf (.classEq W (syn_cmpt s (syn_co G (syn_cmap) (.cv a))
            (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) :
    Nominal.NPrf
      (.imp (syn_wf1o (.cv r) (.cv a) (.cv b))
        (.imp (syn_wbr S W T) (.classEq S (syn_ccom T (.cv r))))) :=
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
  have dv_cache_0004 : s ∉ ((syn_ccom S (syn_ccnv (.cv r)))).fv :=
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
  have dv_cache_0005 : s ∉ ((syn_co G (syn_cmap) (.cv a))).fv :=
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
  have p0000 := @g_breldm S T W
  have p0001 := @g_enmap2lem2 G W s r a dv_cache_0001 dv_cache_0002 hyp_enmap2lem3_1
  have p0002 := @g_fndm (syn_co G (syn_cmap) (.cv a)) W
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_syl6eleq (syn_wbr S W T) S (syn_cdm W) (syn_co G (syn_cmap) (.cv a)) p0000 p0003
  have p0005 := @g_fnbrfvb (syn_co G (syn_cmap) (.cv a)) S T W
  have p0006 :=
    @g_mpan (syn_wfn W (syn_co G (syn_cmap) (.cv a)))
      (.classMem S (syn_co G (syn_cmap) (.cv a)))
      (syn_wb (.classEq (syn_cfv W S) T) (syn_wbr S W T)) p0001 p0005
  have p0007 := @g_vex r
  have p0008 := @g_cnvex (.cv r) p0007
  have p0009 := @g_coexg S (syn_ccnv (.cv r)) (syn_co G (syn_cmap) (.cv a)) (syn_cvv)
  have p0010 :=
    @g_mpan2 (.classMem S (syn_co G (syn_cmap) (.cv a)))
      (.classMem (syn_ccnv (.cv r)) (syn_cvv))
      (.classMem (syn_ccom S (syn_ccnv (.cv r))) (syn_cvv)) p0008 p0009
  have p0011 := @g_coeq1 (.cv s) S (syn_ccnv (.cv r))
  have p0012 :=
    @g_fvmptg s S (syn_ccom (.cv s) (syn_ccnv (.cv r))) (syn_ccom S (syn_ccnv (.cv r)))
      (syn_co G (syn_cmap) (.cv a)) (syn_cvv) W dv_cache_0003 dv_cache_0004 dv_cache_0005
      p0011 hyp_enmap2lem3_1
  have p0013 :=
    @g_mpdan (.classMem S (syn_co G (syn_cmap) (.cv a)))
      (.classMem (syn_ccom S (syn_ccnv (.cv r))) (syn_cvv))
      (.classEq (syn_cfv W S) (syn_ccom S (syn_ccnv (.cv r)))) p0010 p0012
  have p0014 :=
    @g_eqeq1d (.classMem S (syn_co G (syn_cmap) (.cv a))) (syn_cfv W S)
      (syn_ccom S (syn_ccnv (.cv r))) T p0013
  have p0015 := @g_eqcom (syn_ccom S (syn_ccnv (.cv r))) T
  have p0016 :=
    @g_syl6bb (.classMem S (syn_co G (syn_cmap) (.cv a))) (.classEq (syn_cfv W S) T)
      (.classEq (syn_ccom S (syn_ccnv (.cv r))) T)
      (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) p0014 p0015
  have p0017 :=
    @g_biimpd (.classMem S (syn_co G (syn_cmap) (.cv a))) (.classEq (syn_cfv W S) T)
      (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) p0016
  have p0018 :=
    @g_sylbird (.classMem S (syn_co G (syn_cmap) (.cv a))) (syn_wbr S W T)
      (.classEq (syn_cfv W S) T) (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) p0006 p0017
  have p0019 :=
    @g_mpcom (.classMem S (syn_co G (syn_cmap) (.cv a))) (syn_wbr S W T)
      (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) p0004 p0018
  have p0020 :=
    @g_jca (syn_wbr S W T) (.classMem S (syn_co G (syn_cmap) (.cv a)))
      (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) p0004 p0019
  have p0021 := @g_f1ococnv1 (.cv a) (.cv b) (.cv r)
  have p0022 :=
    @g_coeq2d (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_ccom (syn_ccnv (.cv r)) (.cv r))
      (syn_cres (syn_cid) (.cv a)) S p0021
  have p0023 :=
    @g_adantr (syn_wf1o (.cv r) (.cv a) (.cv b))
      (.classEq (syn_ccom S (syn_ccom (syn_ccnv (.cv r)) (.cv r)))
        (syn_ccom S (syn_cres (syn_cid) (.cv a))))
      (.classMem S (syn_co G (syn_cmap) (.cv a))) p0022
  have p0024 := @g_elmapi S G (.cv a)
  have p0025 := @g_fcoi1 (.cv a) G S
  have p0026 :=
    @g_syl (.classMem S (syn_co G (syn_cmap) (.cv a))) (syn_wf S (.cv a) G)
      (.classEq (syn_ccom S (syn_cres (syn_cid) (.cv a))) S) p0024 p0025
  have p0027 :=
    @g_adantl (.classMem S (syn_co G (syn_cmap) (.cv a)))
      (.classEq (syn_ccom S (syn_cres (syn_cid) (.cv a))) S)
      (syn_wf1o (.cv r) (.cv a) (.cv b)) p0026
  have p0028 :=
    @g_eqtr2d
      (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem S (syn_co G (syn_cmap) (.cv a))))
      (syn_ccom S (syn_ccom (syn_ccnv (.cv r)) (.cv r)))
      (syn_ccom S (syn_cres (syn_cid) (.cv a))) S p0023 p0027
  have p0029 := @g_coeq1 T (syn_ccom S (syn_ccnv (.cv r))) (.cv r)
  have p0030 := @g_coass S (syn_ccnv (.cv r)) (.cv r)
  have p0031 :=
    @g_syl6eq (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) (syn_ccom T (.cv r))
      (syn_ccom (syn_ccom S (syn_ccnv (.cv r))) (.cv r))
      (syn_ccom S (syn_ccom (syn_ccnv (.cv r)) (.cv r))) p0029 p0030
  have p0032 :=
    @g_eqeq2d (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) (syn_ccom T (.cv r))
      (syn_ccom S (syn_ccom (syn_ccnv (.cv r)) (.cv r))) S p0031
  have p0033 :=
    @g_syl5ibrcom
      (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classMem S (syn_co G (syn_cmap) (.cv a))))
      (.classEq S (syn_ccom T (.cv r))) (.classEq T (syn_ccom S (syn_ccnv (.cv r))))
      (.classEq S (syn_ccom S (syn_ccom (syn_ccnv (.cv r)) (.cv r)))) p0028 p0032
  have p0034 :=
    @g_expimpd (syn_wf1o (.cv r) (.cv a) (.cv b))
      (.classMem S (syn_co G (syn_cmap) (.cv a)))
      (.classEq T (syn_ccom S (syn_ccnv (.cv r)))) (.classEq S (syn_ccom T (.cv r))) p0033
  have p0035 :=
    @g_syl5 (syn_wbr S W T)
      (syn_wa (.classMem S (syn_co G (syn_cmap) (.cv a)))
        (.classEq T (syn_ccom S (syn_ccnv (.cv r)))))
      (syn_wf1o (.cv r) (.cv a) (.cv b)) (.classEq S (syn_ccom T (.cv r))) p0020 p0034
  exact p0035

@[expose]
noncomputable def g_enmap2lem4 (G : Class) (W : Class) (s : Var) (r : Var) (a : Var)
    (b : Var) (dv_G_s : s ∉ G.fv) (dv_a_s : a ≠ s) (dv_r_s : r ≠ s)
    (hyp_enmap2lem4_1 : Nominal.NPrf (.classEq W (syn_cmpt s (syn_co G (syn_cmap) (.cv a))
            (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) :
    Nominal.NPrf (.imp (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wfun (syn_ccnv W))) :=
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
  have dv_cache_0006 : z ∉ ((syn_wf1o (.cv r) (.cv a) (.cv b))).fv :=
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
  have dv_cache_0007 : x ∉ ((syn_wf1o (.cv r) (.cv a) (.cv b))).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_wf1o (.cv r) (.cv a) (.cv b))).fv :=
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
  have dv_cache_0009 : x ∉ ((syn_ccnv W)).fv :=
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
  have dv_cache_0010 : y ∉ ((syn_ccnv W)).fv :=
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
  have dv_cache_0011 : z ∉ ((syn_ccnv W)).fv :=
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
    @g_enmap2lem3 (.cv y) (.cv x) G W s r a b dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 hyp_enmap2lem4_1
  have p0001 :=
    @g_enmap2lem3 (.cv z) (.cv x) G W s r a b dv_cache_0001 dv_cache_0005 dv_cache_0003
      dv_cache_0004 hyp_enmap2lem4_1
  have p0002 :=
    @g_anim12d (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_wbr (.cv y) W (.cv x))
      (.classEq (.cv y) (syn_ccom (.cv x) (.cv r))) (syn_wbr (.cv z) W (.cv x))
      (.classEq (.cv z) (syn_ccom (.cv x) (.cv r))) p0000 p0001
  have p0003 := @g_eqtr3 (.cv y) (.cv z) (syn_ccom (.cv x) (.cv r))
  have p0004_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv y) (syn_ccom (.cv x) (.cv r)))
          (.classEq (.cv z) (syn_ccom (.cv x) (.cv r)))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_ccom syn_copab syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0003
  have p0004 :=
    @g_syl6 (syn_wf1o (.cv r) (.cv a) (.cv b))
      (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x)))
      (syn_wa (.classEq (.cv y) (syn_ccom (.cv x) (.cv r)))
        (.classEq (.cv z) (syn_ccom (.cv x) (.cv r))))
      (.objEq y z) p0002 p0004_e01_recanon
  have p0005 :=
    @g_alrimiv (syn_wf1o (.cv r) (.cv a) (.cv b))
      (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (.objEq y z))
      z dv_cache_0006 p0004
  have p0006 :=
    @g_alrimivv (syn_wf1o (.cv r) (.cv a) (.cv b))
      (.all z (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x)))
          (.objEq y z)))
      x y dv_cache_0007 dv_cache_0008 p0005
  have p0007 :=
    @g_dffun2 x y z (syn_ccnv W) dv_cache_0009 dv_cache_0010 dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014
  have p0008 := @g_brcnv (.cv x) (.cv y) W
  have p0009 := @g_brcnv (.cv x) (.cv z) W
  have p0010 :=
    @g_anbi12i (syn_wbr (.cv x) (syn_ccnv W) (.cv y)) (syn_wbr (.cv y) W (.cv x))
      (syn_wbr (.cv x) (syn_ccnv W) (.cv z)) (syn_wbr (.cv z) W (.cv x)) p0008 p0009
  have p0011 :=
    @g_imbi1i
      (syn_wa (syn_wbr (.cv x) (syn_ccnv W) (.cv y)) (syn_wbr (.cv x) (syn_ccnv W) (.cv z)))
      (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (.objEq y z) p0010
  have p0012 :=
    @g_albii
      (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv W) (.cv y))
          (syn_wbr (.cv x) (syn_ccnv W) (.cv z))) (.objEq y z))
      (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x))) (.objEq y z))
      z p0011
  have p0013 :=
    @g_n_2albii
      (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv W) (.cv y))
            (syn_wbr (.cv x) (syn_ccnv W) (.cv z))) (.objEq y z)))
      (.all z (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x)))
          (.objEq y z)))
      x y p0012
  have p0014 :=
    @g_bitri (syn_wfun (syn_ccnv W))
      (.all x (.all y (.all z (.imp (syn_wa (syn_wbr (.cv x) (syn_ccnv W) (.cv y))
                (syn_wbr (.cv x) (syn_ccnv W) (.cv z))) (.objEq y z)))))
      (.all x (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x)))
              (.objEq y z)))))
      p0007 p0013
  have p0015 :=
    @g_sylibr (syn_wf1o (.cv r) (.cv a) (.cv b))
      (.all x (.all y (.all z
            (.imp (syn_wa (syn_wbr (.cv y) W (.cv x)) (syn_wbr (.cv z) W (.cv x)))
              (.objEq y z)))))
      (syn_wfun (syn_ccnv W)) p0006 p0014
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

@[expose]
noncomputable def g_enmap2lem5 (G : Class) (W : Class) (s : Var) (r : Var) (a : Var)
    (b : Var) (dv_G_s : s ∉ G.fv) (dv_a_s : a ≠ s) (dv_r_s : r ≠ s)
    (hyp_enmap2lem5_1 : Nominal.NPrf (.classEq W (syn_cmpt s (syn_co G (syn_cmap) (.cv a))
            (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) :
    Nominal.NPrf
      (.imp (syn_wf1o (.cv r) (.cv a) (.cv b))
        (.classEq (syn_crn W) (syn_co G (syn_cmap) (.cv b)))) :=
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
  have dv_cache_0004 : s ∉ ((syn_ccom (.cv p) (syn_ccnv (.cv r)))).fv :=
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
  have dv_cache_0005 : s ∉ ((syn_co G (syn_cmap) (.cv a))).fv :=
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
  have dv_cache_0006 : p ∉ ((syn_wf1o (.cv r) (.cv a) (.cv b))).fv :=
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
  have dv_cache_0007 : p ∉ ((syn_co G (syn_cmap) (.cv a))).fv :=
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
  have dv_cache_0008 : p ∉ ((syn_co G (syn_cmap) (.cv b))).fv :=
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
  have dv_cache_0010 : s ∉ ((syn_ccom (.cv p) (.cv r))).fv :=
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
    s ∉ ((syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r))))).fv :=
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
  have dv_cache_0012 : p ∉ ((syn_crn W)).fv :=
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
  have p0000 := @g_enmap2lem2 G W s r a dv_cache_0001 dv_cache_0002 hyp_enmap2lem5_1
  have p0001 := @g_coeq1 (.cv s) (.cv p) (syn_ccnv (.cv r))
  have p0002 := @g_vex p
  have p0003 := @g_vex r
  have p0004 := @g_cnvex (.cv r) p0003
  have p0005 := @g_coex (.cv p) (syn_ccnv (.cv r)) p0002 p0004
  have p0006 :=
    @g_fvmpt s (.cv p) (syn_ccom (.cv s) (syn_ccnv (.cv r)))
      (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv a)) W dv_cache_0003
      dv_cache_0004 dv_cache_0005 p0001 hyp_enmap2lem5_1 p0005
  have p0007 :=
    @g_adantl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a)))
      (.classEq (syn_cfv W (.cv p)) (syn_ccom (.cv p) (syn_ccnv (.cv r))))
      (syn_wf1o (.cv r) (.cv a) (.cv b)) p0006
  have p0008 := @g_elmapi (.cv p) G (.cv a)
  have p0009 := @g_f1ocnv (.cv a) (.cv b) (.cv r)
  have p0010 := @g_f1of (.cv b) (.cv a) (syn_ccnv (.cv r))
  have p0011 :=
    @g_syl (syn_wf1o (.cv r) (.cv a) (.cv b))
      (syn_wf1o (syn_ccnv (.cv r)) (.cv b) (.cv a))
      (syn_wf (syn_ccnv (.cv r)) (.cv b) (.cv a)) p0009 p0010
  have p0012 := @g_fco (.cv b) (.cv a) G (.cv p) (syn_ccnv (.cv r))
  have p0013 :=
    @g_syl2anr (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a)))
      (syn_wf (.cv p) (.cv a) G) (syn_wf (syn_ccnv (.cv r)) (.cv b) (.cv a))
      (syn_wf (syn_ccom (.cv p) (syn_ccnv (.cv r))) (.cv b) G)
      (syn_wf1o (.cv r) (.cv a) (.cv b)) p0008 p0011 p0012
  have p0014 := @g_elovex1 (.cv p) G (.cv a) (syn_cmap)
  have p0015 := @g_vex b
  have p0016 :=
    @g_elmapg G (.cv b) (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_cvv) (syn_cvv)
      (syn_cvv)
  have p0017 :=
    @g_mp3an23 (.classMem G (syn_cvv)) (.classMem (.cv b) (syn_cvv))
      (.classMem (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_cvv))
      (syn_wb (.classMem (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv b)))
        (syn_wf (syn_ccom (.cv p) (syn_ccnv (.cv r))) (.cv b) G))
      p0015 p0005 p0016
  have p0018 :=
    @g_syl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a))) (.classMem G (syn_cvv))
      (syn_wb (.classMem (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv b)))
        (syn_wf (syn_ccom (.cv p) (syn_ccnv (.cv r))) (.cv b) G))
      p0014 p0017
  have p0019 :=
    @g_adantl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a)))
      (syn_wb (.classMem (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv b)))
        (syn_wf (syn_ccom (.cv p) (syn_ccnv (.cv r))) (.cv b) G))
      (syn_wf1o (.cv r) (.cv a) (.cv b)) p0018
  have p0020 :=
    @g_mpbird
      (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a))))
      (.classMem (syn_ccom (.cv p) (syn_ccnv (.cv r))) (syn_co G (syn_cmap) (.cv b)))
      (syn_wf (syn_ccom (.cv p) (syn_ccnv (.cv r))) (.cv b) G) p0013 p0019
  have p0021 :=
    @g_eqeltrd
      (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (syn_co G (syn_cmap) (.cv a))))
      (syn_cfv W (.cv p)) (syn_ccom (.cv p) (syn_ccnv (.cv r)))
      (syn_co G (syn_cmap) (.cv b)) p0007 p0020
  have p0022 :=
    @g_ralrimiva (syn_wf1o (.cv r) (.cv a) (.cv b))
      (.classMem (syn_cfv W (.cv p)) (syn_co G (syn_cmap) (.cv b))) p
      (syn_co G (syn_cmap) (.cv a)) dv_cache_0006 p0021
  have p0023 :=
    @g_fnfvrnss p (syn_co G (syn_cmap) (.cv a)) (syn_co G (syn_cmap) (.cv b)) W
      dv_cache_0007 dv_cache_0008 dv_cache_0009
  have p0024 :=
    @g_sylancr (syn_wf1o (.cv r) (.cv a) (.cv b))
      (syn_wfn W (syn_co G (syn_cmap) (.cv a)))
      (syn_wral p (syn_co G (syn_cmap) (.cv a))
        (.classMem (syn_cfv W (.cv p)) (syn_co G (syn_cmap) (.cv b))))
      (syn_wss (syn_crn W) (syn_co G (syn_cmap) (.cv b))) p0000 p0022 p0023
  have p0025 := @g_elmapi (.cv p) G (.cv b)
  have p0026 := @g_f1of (.cv a) (.cv b) (.cv r)
  have p0027 := @g_fco (.cv a) (.cv b) G (.cv p) (.cv r)
  have p0028 :=
    @g_syl2anr (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b)))
      (syn_wf (.cv p) (.cv b) G) (syn_wf (.cv r) (.cv a) (.cv b))
      (syn_wf (syn_ccom (.cv p) (.cv r)) (.cv a) G) (syn_wf1o (.cv r) (.cv a) (.cv b))
      p0025 p0026 p0027
  have p0029 := @g_elovex1 (.cv p) G (.cv b) (syn_cmap)
  have p0030 := @g_vex a
  have p0031 := @g_coex (.cv p) (.cv r) p0002 p0003
  have p0032 :=
    @g_elmapg G (.cv a) (syn_ccom (.cv p) (.cv r)) (syn_cvv) (syn_cvv) (syn_cvv)
  have p0033 :=
    @g_mp3an23 (.classMem G (syn_cvv)) (.classMem (.cv a) (syn_cvv))
      (.classMem (syn_ccom (.cv p) (.cv r)) (syn_cvv))
      (syn_wb (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a)))
        (syn_wf (syn_ccom (.cv p) (.cv r)) (.cv a) G))
      p0030 p0031 p0032
  have p0034 :=
    @g_syl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))) (.classMem G (syn_cvv))
      (syn_wb (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a)))
        (syn_wf (syn_ccom (.cv p) (.cv r)) (.cv a) G))
      p0029 p0033
  have p0035 :=
    @g_adantl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b)))
      (syn_wb (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a)))
        (syn_wf (syn_ccom (.cv p) (.cv r)) (.cv a) G))
      (syn_wf1o (.cv r) (.cv a) (.cv b)) p0034
  have p0036 :=
    @g_mpbird
      (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))))
      (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a)))
      (syn_wf (syn_ccom (.cv p) (.cv r)) (.cv a) G) p0028 p0035
  have p0037 := @g_coeq1 (.cv s) (syn_ccom (.cv p) (.cv r)) (syn_ccnv (.cv r))
  have p0038 := @g_coass (.cv p) (.cv r) (syn_ccnv (.cv r))
  have p0039 :=
    @g_syl6eq (.classEq (.cv s) (syn_ccom (.cv p) (.cv r)))
      (syn_ccom (.cv s) (syn_ccnv (.cv r)))
      (syn_ccom (syn_ccom (.cv p) (.cv r)) (syn_ccnv (.cv r)))
      (syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r)))) p0037 p0038
  have p0040 := @g_coex (.cv r) (syn_ccnv (.cv r)) p0003 p0004
  have p0041 := @g_coex (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r))) p0002 p0040
  have p0042 :=
    @g_fvmpt s (syn_ccom (.cv p) (.cv r)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))
      (syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r))))
      (syn_co G (syn_cmap) (.cv a)) W dv_cache_0010 dv_cache_0011 dv_cache_0005 p0039
      hyp_enmap2lem5_1 p0041
  have p0043 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))))
      (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a)))
      (.classEq (syn_cfv W (syn_ccom (.cv p) (.cv r)))
        (syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r)))))
      p0036 p0042
  have p0044 := @g_f1ococnv2 (.cv a) (.cv b) (.cv r)
  have p0045 :=
    @g_coeq2d (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_ccom (.cv r) (syn_ccnv (.cv r)))
      (syn_cres (syn_cid) (.cv b)) (.cv p) p0044
  have p0046 := @g_fcoi1 (.cv b) G (.cv p)
  have p0047 :=
    @g_syl (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))) (syn_wf (.cv p) (.cv b) G)
      (.classEq (syn_ccom (.cv p) (syn_cres (syn_cid) (.cv b))) (.cv p)) p0025 p0046
  have p0048 :=
    @g_sylan9eq (syn_wf1o (.cv r) (.cv a) (.cv b))
      (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b)))
      (syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r))))
      (syn_ccom (.cv p) (syn_cres (syn_cid) (.cv b))) (.cv p) p0045 p0047
  have p0049 :=
    @g_eqtrd
      (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))))
      (syn_cfv W (syn_ccom (.cv p) (.cv r)))
      (syn_ccom (.cv p) (syn_ccom (.cv r) (syn_ccnv (.cv r)))) (.cv p) p0043 p0048
  have p0050 :=
    @g_fnbrfvb (syn_co G (syn_cmap) (.cv a)) (syn_ccom (.cv p) (.cv r)) (.cv p) W
  have p0051 :=
    @g_sylancr
      (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))))
      (syn_wfn W (syn_co G (syn_cmap) (.cv a)))
      (.classMem (syn_ccom (.cv p) (.cv r)) (syn_co G (syn_cmap) (.cv a)))
      (syn_wb (.classEq (syn_cfv W (syn_ccom (.cv p) (.cv r))) (.cv p))
        (syn_wbr (syn_ccom (.cv p) (.cv r)) W (.cv p)))
      p0000 p0036 p0050
  have p0052 :=
    @g_mpbid
      (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))))
      (.classEq (syn_cfv W (syn_ccom (.cv p) (.cv r))) (.cv p))
      (syn_wbr (syn_ccom (.cv p) (.cv r)) W (.cv p)) p0049 p0051
  have p0053 := @g_brelrn (syn_ccom (.cv p) (.cv r)) (.cv p) W
  have p0054 :=
    @g_syl
      (syn_wa (syn_wf1o (.cv r) (.cv a) (.cv b))
        (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))))
      (syn_wbr (syn_ccom (.cv p) (.cv r)) W (.cv p)) (.classMem (.cv p) (syn_crn W)) p0052
      p0053
  have p0055 :=
    @g_ex (syn_wf1o (.cv r) (.cv a) (.cv b))
      (.classMem (.cv p) (syn_co G (syn_cmap) (.cv b))) (.classMem (.cv p) (syn_crn W))
      p0054
  have p0056 :=
    @g_ssrdv (syn_wf1o (.cv r) (.cv a) (.cv b)) p (syn_co G (syn_cmap) (.cv b))
      (syn_crn W) dv_cache_0008 dv_cache_0012 dv_cache_0006 p0055
  have p0057 :=
    @g_eqssd (syn_wf1o (.cv r) (.cv a) (.cv b)) (syn_crn W) (syn_co G (syn_cmap) (.cv b))
      p0024 p0056
  exact p0057

@[expose]
noncomputable def g_enmap2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf
      (.imp (syn_wbr A (syn_cen) B)
        (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) B))) :=
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
      ((syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b)))).fv :=
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
      ((Wff.imp (syn_wbr A (syn_cen) B)
          (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) B)))).fv :=
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
      ((Wff.imp (syn_wbr A (syn_cen) (.cv b)) (syn_wbr (syn_co C (syn_cmap) A) (syn_cen)
            (syn_co C (syn_cmap) (.cv b))))).fv :=
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
  have p0000 := @g_brex A B (syn_cen)
  have p0001 := @g_breq1 (.cv a) A (.cv b) (syn_cen)
  have p0002 := @g_oveq2 (.cv a) A C (syn_cmap)
  have p0003 :=
    @g_breq1d (.classEq (.cv a) A) (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) A)
      (syn_co C (syn_cmap) (.cv b)) (syn_cen) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv a) A) (syn_wbr (.cv a) (syn_cen) (.cv b))
      (syn_wbr A (syn_cen) (.cv b))
      (syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b)))
      (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) (.cv b))) p0001
      p0003
  have p0005 := @g_breq2 (.cv b) B A (syn_cen)
  have p0006 := @g_oveq2 (.cv b) B C (syn_cmap)
  have p0007 :=
    @g_breq2d (.classEq (.cv b) B) (syn_co C (syn_cmap) (.cv b)) (syn_co C (syn_cmap) B)
      (syn_co C (syn_cmap) A) (syn_cen) p0006
  have p0008 :=
    @g_imbi12d (.classEq (.cv b) B) (syn_wbr A (syn_cen) (.cv b)) (syn_wbr A (syn_cen) B)
      (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) (.cv b)))
      (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) B)) p0005 p0007
  have p0009 := @g_bren (.cv a) (.cv b) r dv_cache_0001 dv_cache_0002
  have p0010 :=
    @g_eqid
      (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
  have p0011 :=
    @g_enmap2lem4 C
      (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) s r
      a b dv_cache_0003 dv_cache_0004 dv_cache_0005 p0010
  have p0012 :=
    @g_dfrn4
      (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
  have p0013 :=
    @g_enmap2lem5 C
      (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) s r
      a b dv_cache_0003 dv_cache_0004 dv_cache_0005 p0010
  have p0014 :=
    @g_syl5eqr (syn_wf1o (.cv r) (.cv a) (.cv b))
      (syn_cdm (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a))
            (syn_ccom (.cv s) (syn_ccnv (.cv r))))))
      (syn_crn (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))))
      (syn_co C (syn_cmap) (.cv b)) p0012 p0013
  have p0015 :=
    @g_jca (syn_wf1o (.cv r) (.cv a) (.cv b))
      (syn_wfun (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a))
            (syn_ccom (.cv s) (syn_ccnv (.cv r))))))
      (.classEq (syn_cdm (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a))
              (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) (syn_co C (syn_cmap) (.cv b)))
      p0011 p0014
  have p0016 :=
    (Nominal.biimpRefl (syn_wfn (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a))
            (syn_ccom (.cv s) (syn_ccnv (.cv r))))) (syn_co C (syn_cmap) (.cv b))))
  have p0017 :=
    @g_sylibr (syn_wf1o (.cv r) (.cv a) (.cv b))
      (syn_wa (syn_wfun (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a))
              (syn_ccom (.cv s) (syn_ccnv (.cv r)))))) (.classEq (syn_cdm (syn_ccnv
              (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))))
          (syn_co C (syn_cmap) (.cv b))))
      (syn_wfn (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a))
            (syn_ccom (.cv s) (syn_ccnv (.cv r))))) (syn_co C (syn_cmap) (.cv b)))
      p0015 p0016
  have p0018 :=
    @g_enmap2lem2 C
      (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) s r
      a dv_cache_0003 dv_cache_0004 p0010
  have p0019 :=
    @g_dff1o4 (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) (.cv b))
      (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
  have p0020 :=
    @g_mpbiran
      (syn_wf1o (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
        (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) (.cv b)))
      (syn_wfn (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
        (syn_co C (syn_cmap) (.cv a)))
      (syn_wfn (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a))
            (syn_ccom (.cv s) (syn_ccnv (.cv r))))) (syn_co C (syn_cmap) (.cv b)))
      p0018 p0019
  have p0021 :=
    @g_sylibr (syn_wf1o (.cv r) (.cv a) (.cv b))
      (syn_wfn (syn_ccnv (syn_cmpt s (syn_co C (syn_cmap) (.cv a))
            (syn_ccom (.cv s) (syn_ccnv (.cv r))))) (syn_co C (syn_cmap) (.cv b)))
      (syn_wf1o (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
        (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) (.cv b)))
      p0017 p0020
  have p0022 :=
    @g_enmap2lem1 (.cv a) C
      (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r)))) s r
      dv_cache_0006 dv_cache_0003 dv_cache_0005 p0010
  have p0023 :=
    @g_f1oen (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) (.cv b))
      (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
      p0022
  have p0024 :=
    @g_syl (syn_wf1o (.cv r) (.cv a) (.cv b))
      (syn_wf1o (syn_cmpt s (syn_co C (syn_cmap) (.cv a)) (syn_ccom (.cv s) (syn_ccnv (.cv r))))
        (syn_co C (syn_cmap) (.cv a)) (syn_co C (syn_cmap) (.cv b)))
      (syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b)))
      p0021 p0023
  have p0025 :=
    @g_exlimiv (syn_wf1o (.cv r) (.cv a) (.cv b))
      (syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b))) r
      dv_cache_0007 p0024
  have p0026 :=
    @g_sylbi (syn_wbr (.cv a) (syn_cen) (.cv b))
      (syn_wex r (syn_wf1o (.cv r) (.cv a) (.cv b)))
      (syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b)))
      p0009 p0025
  have p0027 :=
    @g_vtocl2g
      (.imp (syn_wbr (.cv a) (syn_cen) (.cv b))
        (syn_wbr (syn_co C (syn_cmap) (.cv a)) (syn_cen) (syn_co C (syn_cmap) (.cv b))))
      (.imp (syn_wbr A (syn_cen) (.cv b))
        (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) (.cv b))))
      (.imp (syn_wbr A (syn_cen) B)
        (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) B)))
      a b A B (syn_cvv) (syn_cvv) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 p0004 p0008 p0026
  have p0028 :=
    @g_mpcom (syn_wa (.classMem A (syn_cvv)) (.classMem B (syn_cvv)))
      (syn_wbr A (syn_cen) B)
      (syn_wbr (syn_co C (syn_cmap) A) (syn_cen) (syn_co C (syn_cmap) B)) p0000 p0027
  exact p0028

@[expose]
noncomputable def g_enpw1pw (A : Class)
    (hyp_enpw1pw_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (syn_wbr (syn_cpw1 (syn_cpw A)) (syn_cen) (syn_cpw (syn_cpw1 A))) :=
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
  have dv_cache_0001 : x ∉ ((syn_cpw1fn)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1fn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cpw1fn)).fv :=
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
  have dv_cache_0003 : x ∉ ((syn_cpw1 (syn_cpw A))).fv :=
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
  have dv_cache_0004 : y ∉ ((syn_cpw1 (syn_cpw A))).fv :=
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
  have dv_cache_0009 : z ∉ ((syn_cpw A)).fv :=
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
  have dv_cache_0010 : z ∉ ((syn_wbr (.cv y) (syn_cpw1fn) (.cv x))).fv :=
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
  have dv_cache_0011 : y ∉ ((syn_cpw A)).fv :=
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
  have dv_cache_0013 : y ∉ ((syn_csn (.cv z))).fv :=
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
  have dv_cache_0014 : y ∉ ((syn_wbr (syn_csn (.cv z)) (syn_cpw1fn) (.cv x))).fv :=
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
  have dv_cache_0015 : x ∉ ((syn_cpw (syn_cpw1 A))).fv :=
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
  have p0000 := @g_pw1fnf1o
  have p0001 := @g_f1of1 (syn_c1c) (syn_cpw (syn_c1c)) (syn_cpw1fn)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_pw1ss1c (syn_cpw A)
  have p0004 :=
    @g_f1ores (syn_c1c) (syn_cpw (syn_c1c)) (syn_cpw1 (syn_cpw A)) (syn_cpw1fn)
  have p0005 :=
    @g_mp2an (syn_wf1 (syn_cpw1fn) (syn_c1c) (syn_cpw (syn_c1c)))
      (syn_wss (syn_cpw1 (syn_cpw A)) (syn_c1c))
      (syn_wf1o (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) (syn_cpw1 (syn_cpw A))
        (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw A))))
      p0002 p0003 p0004
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_ima x y (syn_cpw1fn)
      (syn_cpw1 (syn_cpw A)) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005
  have p0007 := @g_vex x
  have p0008 := @g_elpw (.cv x) (syn_cpw1 A) p0007
  have p0009 := @g_sspw1 z (.cv x) A dv_cache_0006 dv_cache_0007 p0007
  have p0010 :=
    (Nominal.biimpRefl (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z)))))
  have p0011 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_pw z A dv_cache_0007
  have p0012 := @g_eqabri (syn_wss (.cv z) A) z (syn_cpw A) p0011
  have p0013 :=
    @g_anbi1i (.classMem (.cv z) (syn_cpw A)) (syn_wss (.cv z) A)
      (.classEq (.cv x) (syn_cpw1 (.cv z))) p0012
  have p0014 :=
    @g_exbii
      (syn_wa (.classMem (.cv z) (syn_cpw A)) (.classEq (.cv x) (syn_cpw1 (.cv z))))
      (syn_wa (syn_wss (.cv z) A) (.classEq (.cv x) (syn_cpw1 (.cv z)))) z p0013
  have p0015 :=
    @g_bitr2i (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z))))
      (syn_wex z (syn_wa (.classMem (.cv z) (syn_cpw A)) (.classEq (.cv x) (syn_cpw1 (.cv z)))))
      (syn_wex z (syn_wa (syn_wss (.cv z) A) (.classEq (.cv x) (syn_cpw1 (.cv z))))) p0010
      p0014
  have p0016 :=
    @g_n_3bitri (.classMem (.cv x) (syn_cpw (syn_cpw1 A))) (syn_wss (.cv x) (syn_cpw1 A))
      (syn_wex z (syn_wa (syn_wss (.cv z) A) (.classEq (.cv x) (syn_cpw1 (.cv z)))))
      (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z)))) p0008 p0009 p0015
  have p0017 :=
    (Nominal.biimpRefl
      (syn_wrex y (syn_cpw1 (syn_cpw A)) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))))
  have p0018 := @g_elpw1 z (.cv y) (syn_cpw A) dv_cache_0008 dv_cache_0009
  have p0019 :=
    @g_anbi1i (.classMem (.cv y) (syn_cpw1 (syn_cpw A)))
      (syn_wrex z (syn_cpw A) (.classEq (.cv y) (syn_csn (.cv z))))
      (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)) p0018
  have p0020 :=
    @g_r19_41v (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))
      z (syn_cpw A) dv_cache_0010
  have p0021 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw A))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
      (syn_wa (syn_wrex z (syn_cpw A) (.classEq (.cv y) (syn_csn (.cv z))))
        (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
      (syn_wrex z (syn_cpw A) (syn_wa (.classEq (.cv y) (syn_csn (.cv z)))
          (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))))
      p0019 p0020
  have p0022 :=
    @g_exbii
      (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw A))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
      (syn_wrex z (syn_cpw A) (syn_wa (.classEq (.cv y) (syn_csn (.cv z)))
          (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))))
      y p0021
  have p0023 :=
    @g_rexcom4
      (syn_wa (.classEq (.cv y) (syn_csn (.cv z))) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
      z y (syn_cpw A) dv_cache_0011 dv_cache_0012
  have p0024 := @g_snex (.cv z)
  have p0025 := @g_breq1 (.cv y) (syn_csn (.cv z)) (.cv x) (syn_cpw1fn)
  have p0026 :=
    @g_ceqsexv (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))
      (syn_wbr (syn_csn (.cv z)) (syn_cpw1fn) (.cv x)) y (syn_csn (.cv z)) dv_cache_0013
      dv_cache_0014 p0024 p0025
  have p0027 := @g_vex z
  have p0028 := @g_brpw1fn (.cv z) (.cv x) p0027
  have p0029 :=
    @g_bitri
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z)))
          (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))))
      (syn_wbr (syn_csn (.cv z)) (syn_cpw1fn) (.cv x))
      (.classEq (.cv x) (syn_cpw1 (.cv z))) p0026 p0028
  have p0030 :=
    @g_rexbii
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z)))
          (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))))
      (.classEq (.cv x) (syn_cpw1 (.cv z))) z (syn_cpw A) p0029
  have p0031 :=
    @g_bitr3i
      (syn_wex y (syn_wrex z (syn_cpw A) (syn_wa (.classEq (.cv y) (syn_csn (.cv z)))
            (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))))
      (syn_wrex z (syn_cpw A) (syn_wex y (syn_wa (.classEq (.cv y) (syn_csn (.cv z)))
            (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))))
      (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z)))) p0023 p0030
  have p0032 :=
    @g_n_3bitri (syn_wrex y (syn_cpw1 (syn_cpw A)) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))
      (syn_wex y (syn_wa (.classMem (.cv y) (syn_cpw1 (syn_cpw A)))
          (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))))
      (syn_wex y (syn_wrex z (syn_cpw A) (syn_wa (.classEq (.cv y) (syn_csn (.cv z)))
            (syn_wbr (.cv y) (syn_cpw1fn) (.cv x)))))
      (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z)))) p0017 p0022 p0031
  have p0033 :=
    @g_bitr4i (.classMem (.cv x) (syn_cpw (syn_cpw1 A)))
      (syn_wrex z (syn_cpw A) (.classEq (.cv x) (syn_cpw1 (.cv z))))
      (syn_wrex y (syn_cpw1 (syn_cpw A)) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))) p0016
      p0032
  have p0034 :=
    @g_eqabi (syn_wrex y (syn_cpw1 (syn_cpw A)) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))) x
      (syn_cpw (syn_cpw1 A)) dv_cache_0015 p0033
  have p0035 :=
    @g_eqtr4i (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw A)))
      (.cab x (syn_wrex y (syn_cpw1 (syn_cpw A)) (syn_wbr (.cv y) (syn_cpw1fn) (.cv x))))
      (syn_cpw (syn_cpw1 A)) p0006 p0034
  have p0036 :=
    @g_f1oeq3 (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) (syn_cpw (syn_cpw1 A))
      (syn_cpw1 (syn_cpw A)) (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw A)))
  have p0037 := Nominal.mp p0035 p0036
  have p0038 :=
    @g_mpbi
      (syn_wf1o (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) (syn_cpw1 (syn_cpw A))
        (syn_cima (syn_cpw1fn) (syn_cpw1 (syn_cpw A))))
      (syn_wf1o (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) (syn_cpw1 (syn_cpw A))
        (syn_cpw (syn_cpw1 A)))
      p0005 p0037
  have p0039 := @g_pw1fnex
  have p0040 := @g_pwex A hyp_enpw1pw_1
  have p0041 := @g_pw1ex (syn_cpw A) p0040
  have p0042 := @g_resex (syn_cpw1fn) (syn_cpw1 (syn_cpw A)) p0039 p0041
  have p0043 :=
    @g_f1oen (syn_cpw1 (syn_cpw A)) (syn_cpw (syn_cpw1 A))
      (syn_cres (syn_cpw1fn) (syn_cpw1 (syn_cpw A))) p0042
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

@[expose]
noncomputable def g_enprmaplem1 (x : Var) (A : Class) (B : Class) (W : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv) (dv_r_x : r ≠ x)
    (hyp_enprmaplem1_1 : Nominal.NPrf (.classEq W (syn_cmpt r (syn_co A (syn_cmap) B)
            (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))))) :
    Nominal.NPrf (.classMem W (syn_cvv)) :=
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
  have dv_cache_0001 : t ∉ ((syn_cop (syn_csn (.cv y)) (.cv r))).fv := by
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
      ((syn_ctxp (syn_csi
            (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
          (syn_csset))).fv :=
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
  have dv_cache_0003 : t ∉ ((syn_cop (.cv y) (.cv x))).fv :=
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
  have dv_cache_0004 : t ∉ ((Wff.classMem (syn_cop (.cv y) (.cv x)) (.cv r))).fv :=
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
  have dv_cache_0005 : r ∉ ((syn_co A (syn_cmap) B)).fv :=
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
      ((syn_cima (syn_ctxp (syn_csi
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
            (syn_csset)) (syn_c1c))).fv :=
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
      ((syn_cima (syn_ctxp (syn_csi
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
            (syn_csset)) (syn_c1c))).fv :=
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
  have dv_cache_0008 : y ∉ ((syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))).fv :=
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
    @g_elima1c t (syn_cop (syn_csn (.cv y)) (.cv r))
      (syn_ctxp
        (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
        (syn_csset))
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_oteltxp (syn_csn (.cv t)) (syn_csn (.cv y)) (.cv r)
      (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
      (syn_csset)
  have p0002 := @g_vex t
  have p0003 := @g_vex y
  have p0004 :=
    @g_opsnelsi (.cv t) (.cv y)
      (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) p0002 p0003
  have p0005 :=
    (Nominal.biimpRefl (syn_wbr (.cv t)
        (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) (.cv y)))
  have p0006 :=
    @g_brres (.cv t) (.cv y) (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))
  have p0007 := @g_eliniseg (syn_c2nd) (.cv x) (.cv t)
  have p0008 :=
    @g_anbi2i (.classMem (.cv t) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))
      (syn_wbr (.cv t) (syn_c2nd) (.cv x)) (syn_wbr (.cv t) (syn_c1st) (.cv y)) p0007
  have p0009 :=
    @g_bitri
      (syn_wbr (.cv t)
        (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) (.cv y))
      (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv y))
        (.classMem (.cv t) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
      (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv y)) (syn_wbr (.cv t) (syn_c2nd) (.cv x)))
      p0006 p0008
  have p0010 :=
    @g_bitr3i
      (.classMem (syn_cop (.cv t) (.cv y))
        (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
      (syn_wbr (.cv t)
        (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) (.cv y))
      (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv y)) (syn_wbr (.cv t) (syn_c2nd) (.cv x)))
      p0005 p0009
  have p0011 := @g_vex x
  have p0012 := @g_op1st2nd (.cv y) (.cv x) (.cv t) p0003 p0011
  have p0013 :=
    @g_n_3bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (.cv y))) (syn_csi
          (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))))
      (.classMem (syn_cop (.cv t) (.cv y))
        (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
      (syn_wa (syn_wbr (.cv t) (syn_c1st) (.cv y)) (syn_wbr (.cv t) (syn_c2nd) (.cv x)))
      (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) p0004 p0010 p0012
  have p0014 := @g_vex r
  have p0015 := @g_opelssetsn (.cv t) (.cv r) p0002 p0014
  have p0016_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cop (syn_csn (.cv t)) (.cv r)) (syn_csset)) (.objMem t r)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_csn syn_csset syn_copab syn_wss syn_cin
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
    @g_anbi12i
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (.cv y))) (syn_csi
          (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))))
      (.classEq (.cv t) (syn_cop (.cv y) (.cv x)))
      (.classMem (syn_cop (syn_csn (.cv t)) (.cv r)) (syn_csset)) (.objMem t r) p0013
      p0016_e01_recanon
  have p0017 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (.cv r))) (syn_ctxp
          (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
          (syn_csset)))
      (syn_wa (.classMem (syn_cop (syn_csn (.cv t)) (syn_csn (.cv y))) (syn_csi
            (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))))
        (.classMem (syn_cop (syn_csn (.cv t)) (.cv r)) (syn_csset)))
      (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.objMem t r)) p0001 p0016
  have p0018 :=
    @g_exbii
      (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (.cv r))) (syn_ctxp
          (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
          (syn_csset)))
      (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.objMem t r)) t p0017
  have p0019 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_cima (syn_ctxp (syn_csi
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
            (syn_csset)) (syn_c1c)))
      (syn_wex t (.classMem (syn_cop (syn_csn (.cv t)) (syn_cop (syn_csn (.cv y)) (.cv r)))
          (syn_ctxp (syn_csi
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
            (syn_csset))))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.objMem t r)))
      p0000 p0018
  have p0020 := @g_opex (.cv y) (.cv x) p0003 p0011
  have p0021 := @g_eleq1 (.cv t) (syn_cop (.cv y) (.cv x)) (.cv r)
  have p0022_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv t) (syn_cop (.cv y) (.cv x)))
        (syn_wb (.objMem t r) (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cop syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_wrex syn_wex
          syn_cphi syn_wb
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
    @g_ceqsexv (.objMem t r) (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)) t
      (syn_cop (.cv y) (.cv x)) dv_cache_0003 dv_cache_0004 p0020 p0022_e01_recanon
  have p0023 := (Nominal.biimpRefl (syn_wbr (.cv y) (.cv r) (.cv x)))
  have p0024 :=
    @g_bitr4i
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.objMem t r)))
      (.classMem (syn_cop (.cv y) (.cv x)) (.cv r)) (syn_wbr (.cv y) (.cv r) (.cv x))
      p0022 p0023
  have p0025 :=
    @g_bitri
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_cima (syn_ctxp (syn_csi
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
            (syn_csset)) (syn_c1c)))
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_cop (.cv y) (.cv x))) (.objMem t r)))
      (syn_wbr (.cv y) (.cv r) (.cv x)) p0019 p0024
  have p0026 := @g_eliniseg (.cv r) (.cv x) (.cv y)
  have p0027 :=
    @g_bitr4i
      (.classMem (syn_cop (syn_csn (.cv y)) (.cv r)) (syn_cima (syn_ctxp (syn_csi
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
            (syn_csset)) (syn_c1c)))
      (syn_wbr (.cv y) (.cv r) (.cv x))
      (.classMem (.cv y) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))) p0025 p0026
  have p0028 :=
    @g_releqmpt r y (syn_co A (syn_cmap) B)
      (syn_cima (syn_ctxp (syn_csi
            (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
          (syn_csset)) (syn_c1c))
      (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 p0027
  have p0029 :=
    @g_eqtr4i W
      (syn_cmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))))
      (syn_cin (syn_cxp (syn_co A (syn_cmap) B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_ctxp (syn_csi
                        (syn_cres (syn_c1st)
                          (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset))
                    (syn_c1c)))) (syn_c1c)))))
      hyp_enprmaplem1_1 p0028
  have p0030 := @g_ovex A B (syn_cmap)
  have p0031 := @g_n_1stex
  have p0032 := @g_n_2ndex
  have p0033 := @g_cnvex (syn_c2nd) p0032
  have p0034 := @g_snex (.cv x)
  have p0035 := @g_imaex (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)) p0033 p0034
  have p0036 :=
    @g_resex (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))) p0031 p0035
  have p0037 :=
    @g_siex (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))) p0036
  have p0038 := @g_ssetex
  have p0039 :=
    @g_txpex
      (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
      (syn_csset) p0037 p0038
  have p0040 := @g_n_1cex
  have p0041 :=
    @g_imaex
      (syn_ctxp
        (syn_csi (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
        (syn_csset))
      (syn_c1c) p0039 p0040
  have p0042 :=
    @g_mptexlem (syn_co A (syn_cmap) B)
      (syn_cima (syn_ctxp (syn_csi
            (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x)))))
          (syn_csset)) (syn_c1c))
      p0030 p0041
  have p0043 :=
    @g_eqeltri W
      (syn_cin (syn_cxp (syn_co A (syn_cmap) B) (syn_cvv)) (syn_ccnv (syn_ccompl (syn_cima
              (syn_csymdif (syn_cins3 (syn_csset)) (syn_cins2 (syn_cima (syn_ctxp (syn_csi
                        (syn_cres (syn_c1st)
                          (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (.cv x))))) (syn_csset))
                    (syn_c1c)))) (syn_c1c)))))
      (syn_cvv) p0029 p0042
  exact p0043

@[expose]
noncomputable def g_enprmaplem2 (x : Var) (A : Class) (B : Class) (W : Class) (r : Var)
    (dv_A_r : r ∉ A.fv) (dv_B_r : r ∉ B.fv)
    (hyp_enprmaplem2_1 : Nominal.NPrf (.classEq W (syn_cmpt r (syn_co A (syn_cmap) B)
            (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x)))))) :
    Nominal.NPrf (syn_wfn W (syn_co A (syn_cmap) B)) :=
  by
  have dv_cache_0001 : r ∉ ((syn_co A (syn_cmap) B)).fv := by
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
    @g_fnmpt r (syn_co A (syn_cmap) B) (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) W
      (syn_cvv) dv_cache_0001 hyp_enprmaplem2_1
  have p0001 := @g_vex r
  have p0002 := @g_cnvex (.cv r) p0001
  have p0003 := @g_snex (.cv x)
  have p0004 := @g_imaex (syn_ccnv (.cv r)) (syn_csn (.cv x)) p0002 p0003
  have p0005 :=
    @g_a1i (.classMem (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cvv))
      (.classMem (.cv r) (syn_co A (syn_cmap) B)) p0004
  have p0006 :=
    @g_mprg (.classMem (syn_cima (syn_ccnv (.cv r)) (syn_csn (.cv x))) (syn_cvv))
      (syn_wfn W (syn_co A (syn_cmap) B)) r (syn_co A (syn_cmap) B) p0000 p0005
  exact p0006


end NFChoice.DirectNominalPrf.WPPReplay

end
