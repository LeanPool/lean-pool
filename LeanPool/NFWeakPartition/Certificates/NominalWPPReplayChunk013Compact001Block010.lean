/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part044`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_ovmuc (g : Var) (M : Class) (N : Class) (a : Var) (b : Var)
    (dv_M_a : a ∉ M.fv) (dv_M_b : b ∉ M.fv) (dv_N_a : a ∉ N.fv) (dv_N_b : b ∉ N.fv)
    (dv_N_g : g ∉ N.fv) (dv_a_b : a ≠ b) (dv_a_g : a ≠ g) (dv_b_g : b ≠ g) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
        (.classEq (syn_co M (syn_cmuc) N) (.cab a (syn_wrex b M
              (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))))) :=
  by
  let proofSupport : Finset Var :=
    ({ g } : Finset Var) ∪ M.fv ∪ N.fv ∪ ({ a } : Finset Var) ∪ ({ b } : Finset Var)
  let c : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  have fresh_c : c ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_c_ne_g : c ≠ g := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_c_ne_a : c ≠ a := by
    intro h
    exact
      fresh_c
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_c : a ≠ c := Ne.symm fresh_c_ne_a
  have fresh_c_ne_b : c ≠ b := by
    intro h
    exact fresh_c (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_ne_g : m ≠ g := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_m : g ≠ m := Ne.symm fresh_m_ne_g
  have fresh_m_not_M : m ∉ M.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_m_not_N : m ∉ N.fv := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_m_ne_a : m ≠ a := by
    intro h
    exact
      fresh_m
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_m : a ≠ m := Ne.symm fresh_m_ne_a
  have fresh_m_ne_b : m ≠ b := by
    intro h
    exact fresh_m (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_m : b ≠ m := Ne.symm fresh_m_ne_b
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_ne_g : n ≠ g := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
              (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))))
  have fresh_g_ne_n : g ≠ n := Ne.symm fresh_n_ne_g
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_n_ne_a : n ≠ a := by
    intro h
    exact
      fresh_n
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_n : a ≠ n := Ne.symm fresh_n_ne_a
  have fresh_n_ne_b : n ≠ b := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_n : b ≠ n := Ne.symm fresh_n_ne_b
  have fresh_m_ne_n : m ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : b ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_a_b), not_false_eq_true])
  have dv_cache_0002 :
    b ∉
      ((syn_cima (syn_crn (syn_cin (syn_cins4
                (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
              (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, dv_N_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : b ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_M_b, not_false_eq_true])
  have dv_cache_0004 : g ∉ ((syn_cop (.cv b) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_b_g), (Ne.symm dv_a_g), or_false,
          not_false_eq_true])
  have dv_cache_0005 :
    g ∉
      ((syn_crn (syn_cin
            (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
            (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : g ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_N_g, not_false_eq_true])
  have dv_cache_0007 : c ∉ ((syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_g, fresh_c_ne_b, fresh_c_ne_a, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    c ∉
      ((syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
          (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((syn_cop (.cv c) (syn_cop (.cv g) (.cv b)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_c, dv_a_g, dv_a_b, or_false,
          not_false_eq_true])
  have dv_cache_0010 :
    a ∉ ((syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : a ∉ ((syn_cop (.cv b) (.cv g))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_a_b, dv_a_g, or_false, not_false_eq_true])
  have dv_cache_0012 :
    a ∉ ((syn_wbr (syn_cop (.cv b) (.cv g)) (syn_ccross) (.cv c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross, Finset.mem_union,
          Finset.mem_singleton, dv_a_b, dv_a_g, fresh_a_ne_c, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0013 : c ∉ ((syn_cxp (.cv b) (.cv g))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_b, fresh_c_ne_g, or_false, not_false_eq_true])
  have dv_cache_0014 : c ∉ ((syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : c ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_singleton, fresh_c_ne_a, fresh_c_ne_b, fresh_c_ne_g,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    a ∉
      ((syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4
                  (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
                (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins4,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_ccross,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union, dv_N_a,
          dv_M_a, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : b ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_m, not_false_eq_true])
  have dv_cache_0017 : a ∉ ((Wff.classEq (.cv m) M)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_m, dv_M_a, or_false, not_false_eq_true])
  have dv_cache_0018 : g ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_n, not_false_eq_true])
  have dv_cache_0019 : b ∉ ((Wff.classEq (.cv n) N)).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_n, dv_N_b, or_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((Wff.classEq (.cv n) N)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_n, dv_N_a, or_false, not_false_eq_true])
  have dv_cache_0021 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact (show a ≠ b from (by exact dv_a_b))
  have dv_cache_0022 : a ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact (show a ≠ g from (by exact dv_a_g))
  have dv_cache_0023 : a ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show a ≠ m from (by exact fresh_a_ne_m))
  have dv_cache_0024 : a ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact (show a ≠ n from (by exact fresh_a_ne_n))
  have dv_cache_0025 : b ≠ g :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show b ≠ g from (by exact dv_b_g))
  have dv_cache_0026 : b ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show b ≠ m from (by exact fresh_b_ne_m))
  have dv_cache_0027 : b ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show b ≠ n from (by exact fresh_b_ne_n))
  have dv_cache_0028 : g ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact (show g ≠ m from (by exact fresh_g_ne_m))
  have dv_cache_0029 : g ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show g ≠ n from (by exact fresh_g_ne_n))
  have dv_cache_0030 : m ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact (show m ≠ n from (by exact fresh_m_ne_n))
  have dv_cache_0031 : m ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_M, not_false_eq_true])
  have dv_cache_0032 : n ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_M, not_false_eq_true])
  have dv_cache_0033 : m ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_N, not_false_eq_true])
  have dv_cache_0034 : n ∉ (N).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_N, not_false_eq_true])
  have dv_cache_0035 : m ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0036 : n ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0037 :
    m ∉
      ((Class.cab a (syn_wrex b M (syn_wrex g (.cv n)
              (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))).fv :=
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
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_not_M, fresh_m_ne_n,
          fresh_m_ne_a, fresh_m_ne_b, fresh_m_ne_g, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0038 :
    m ∉
      ((Class.cab a (syn_wrex b M
            (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))).fv :=
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
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_not_M, fresh_m_not_N,
          fresh_m_ne_a, fresh_m_ne_b, fresh_m_ne_g, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0039 :
    n ∉
      ((Class.cab a (syn_wrex b M
            (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_not_M, fresh_n_not_N,
          fresh_n_ne_a, fresh_n_ne_b, fresh_n_ne_g, compact_fv_not_mem_empty, or_false,
          and_false, not_false_eq_true])
  have p0000 :=
    @g_elima b (.cv a)
      (syn_cima (syn_crn (syn_cin
            (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
            (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N)
      M dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (Nominal.biimpRefl (syn_wbr (.cv b) (syn_cima (syn_crn (syn_cin (syn_cins4
                (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
              (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (.cv a)))
  have p0002 :=
    @g_elima g (syn_cop (.cv b) (.cv a))
      (syn_crn (syn_cin
          (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
          (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))))
      N dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    (Nominal.biimpRefl (syn_wbr (.cv g) (syn_crn (syn_cin
            (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
            (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_cop (.cv b) (.cv a))))
  have p0004 :=
    @g_elrn2 c (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))
      (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
        (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))
      dv_cache_0007 dv_cache_0008
  have p0005 :=
    @g_elin (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))))
      (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))
  have p0006 := @g_vex a
  have p0007 :=
    @g_oqelins4 (.cv c) (.cv g) (.cv b) (.cv a)
      (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))) p0006
  have p0008 :=
    @g_elrn a (syn_cop (.cv c) (syn_cop (.cv g) (.cv b)))
      (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))) dv_cache_0009 dv_cache_0010
  have p0009 :=
    @g_trtxp (.cv a) (.cv c) (syn_cop (.cv g) (.cv b)) (syn_ccross)
      (syn_ctxp (syn_c2nd) (syn_c1st))
  have p0010 := @g_trtxp (.cv a) (.cv g) (.cv b) (syn_c2nd) (syn_c1st)
  have p0011 :=
    @g_ancom (syn_wbr (.cv a) (syn_c2nd) (.cv g)) (syn_wbr (.cv a) (syn_c1st) (.cv b))
  have p0012 := @g_vex b
  have p0013 := @g_vex g
  have p0014 := @g_op1st2nd (.cv b) (.cv g) (.cv a) p0012 p0013
  have p0015 :=
    @g_n_3bitri
      (syn_wbr (.cv a) (syn_ctxp (syn_c2nd) (syn_c1st)) (syn_cop (.cv g) (.cv b)))
      (syn_wa (syn_wbr (.cv a) (syn_c2nd) (.cv g)) (syn_wbr (.cv a) (syn_c1st) (.cv b)))
      (syn_wa (syn_wbr (.cv a) (syn_c1st) (.cv b)) (syn_wbr (.cv a) (syn_c2nd) (.cv g)))
      (.classEq (.cv a) (syn_cop (.cv b) (.cv g))) p0010 p0011 p0014
  have p0016 :=
    @g_anbi2i (syn_wbr (.cv a) (syn_ctxp (syn_c2nd) (syn_c1st)) (syn_cop (.cv g) (.cv b)))
      (.classEq (.cv a) (syn_cop (.cv b) (.cv g))) (syn_wbr (.cv a) (syn_ccross) (.cv c))
      p0015
  have p0017 :=
    @g_ancom (syn_wbr (.cv a) (syn_ccross) (.cv c))
      (.classEq (.cv a) (syn_cop (.cv b) (.cv g)))
  have p0018 :=
    @g_n_3bitri
      (syn_wbr (.cv a) (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))
        (syn_cop (.cv c) (syn_cop (.cv g) (.cv b))))
      (syn_wa (syn_wbr (.cv a) (syn_ccross) (.cv c))
        (syn_wbr (.cv a) (syn_ctxp (syn_c2nd) (syn_c1st)) (syn_cop (.cv g) (.cv b))))
      (syn_wa (syn_wbr (.cv a) (syn_ccross) (.cv c))
        (.classEq (.cv a) (syn_cop (.cv b) (.cv g))))
      (syn_wa (.classEq (.cv a) (syn_cop (.cv b) (.cv g)))
        (syn_wbr (.cv a) (syn_ccross) (.cv c)))
      p0009 p0016 p0017
  have p0019 :=
    @g_exbii
      (syn_wbr (.cv a) (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))
        (syn_cop (.cv c) (syn_cop (.cv g) (.cv b))))
      (syn_wa (.classEq (.cv a) (syn_cop (.cv b) (.cv g)))
        (syn_wbr (.cv a) (syn_ccross) (.cv c)))
      a p0018
  have p0020 := @g_opex (.cv b) (.cv g) p0012 p0013
  have p0021 := @g_breq1 (.cv a) (syn_cop (.cv b) (.cv g)) (.cv c) (syn_ccross)
  have p0022 :=
    @g_ceqsexv (syn_wbr (.cv a) (syn_ccross) (.cv c))
      (syn_wbr (syn_cop (.cv b) (.cv g)) (syn_ccross) (.cv c)) a (syn_cop (.cv b) (.cv g))
      dv_cache_0011 dv_cache_0012 p0020 p0021
  have p0023 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (.cv b)))
        (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (syn_wex a (syn_wbr (.cv a) (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))
          (syn_cop (.cv c) (syn_cop (.cv g) (.cv b)))))
      (syn_wex a (syn_wa (.classEq (.cv a) (syn_cop (.cv b) (.cv g)))
          (syn_wbr (.cv a) (syn_ccross) (.cv c))))
      (syn_wbr (syn_cop (.cv b) (.cv g)) (syn_ccross) (.cv c)) p0008 p0019 p0022
  have p0024 := @g_brcross (.cv b) (.cv g) (.cv c) p0012 p0013
  have p0025 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))))
        (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))))
      (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (.cv b)))
        (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (syn_wbr (syn_cop (.cv b) (.cv g)) (syn_ccross) (.cv c))
      (.classEq (.cv c) (syn_cxp (.cv b) (.cv g))) p0007 p0023 p0024
  have p0026 :=
    @g_otelins2 (.cv c) (.cv g) (syn_cop (.cv b) (.cv a)) (syn_cins2 (syn_ccnv (syn_cen)))
      p0013
  have p0027 := @g_otelins2 (.cv c) (.cv b) (.cv a) (syn_ccnv (syn_cen)) p0012
  have p0028 := (Nominal.biimpRefl (syn_wbr (.cv c) (syn_ccnv (syn_cen)) (.cv a)))
  have p0029 := @g_brcnv (.cv c) (.cv a) (syn_cen)
  have p0030 :=
    @g_bitr3i (.classMem (syn_cop (.cv c) (.cv a)) (syn_ccnv (syn_cen)))
      (syn_wbr (.cv c) (syn_ccnv (syn_cen)) (.cv a)) (syn_wbr (.cv a) (syn_cen) (.cv c))
      p0028 p0029
  have p0031 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))))
        (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))
      (.classMem (syn_cop (.cv c) (syn_cop (.cv b) (.cv a))) (syn_cins2 (syn_ccnv (syn_cen))))
      (.classMem (syn_cop (.cv c) (.cv a)) (syn_ccnv (syn_cen)))
      (syn_wbr (.cv a) (syn_cen) (.cv c)) p0026 p0027 p0030
  have p0032 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))))
        (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))))
      (.classEq (.cv c) (syn_cxp (.cv b) (.cv g)))
      (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))))
        (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))
      (syn_wbr (.cv a) (syn_cen) (.cv c)) p0025 p0031
  have p0033 :=
    @g_bitri
      (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cin
          (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
          (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))))
      (syn_wa (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))))
          (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))))))
        (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))))
          (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))))
      (syn_wa (.classEq (.cv c) (syn_cxp (.cv b) (.cv g))) (syn_wbr (.cv a) (syn_cen) (.cv c)))
      p0005 p0032
  have p0034 :=
    @g_exbii
      (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a)))) (syn_cin
          (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
          (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))))
      (syn_wa (.classEq (.cv c) (syn_cxp (.cv b) (.cv g))) (syn_wbr (.cv a) (syn_cen) (.cv c)))
      c p0033
  have p0035 := @g_xpex (.cv b) (.cv g) p0012 p0013
  have p0036 := @g_breq2 (.cv c) (syn_cxp (.cv b) (.cv g)) (.cv a) (syn_cen)
  have p0037 :=
    @g_ceqsexv (syn_wbr (.cv a) (syn_cen) (.cv c))
      (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))) c (syn_cxp (.cv b) (.cv g))
      dv_cache_0013 dv_cache_0014 p0035 p0036
  have p0038 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))) (syn_crn (syn_cin
            (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
            (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))))
      (syn_wex c (.classMem (syn_cop (.cv c) (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))))
          (syn_cin
            (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
            (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))))
      (syn_wex c (syn_wa (.classEq (.cv c) (syn_cxp (.cv b) (.cv g)))
          (syn_wbr (.cv a) (syn_cen) (.cv c))))
      (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))) p0004 p0034 p0037
  have p0039 :=
    @g_bitri
      (syn_wbr (.cv g) (syn_crn (syn_cin
            (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
            (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_cop (.cv b) (.cv a)))
      (.classMem (syn_cop (.cv g) (syn_cop (.cv b) (.cv a))) (syn_crn (syn_cin
            (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
            (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))))
      (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))) p0003 p0038
  have p0040 :=
    @g_rexbii
      (syn_wbr (.cv g) (syn_crn (syn_cin
            (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
            (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_cop (.cv b) (.cv a)))
      (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))) g N p0039
  have p0041 :=
    @g_n_3bitri
      (syn_wbr (.cv b) (syn_cima (syn_crn (syn_cin (syn_cins4
                (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
              (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (.cv a))
      (.classMem (syn_cop (.cv b) (.cv a)) (syn_cima (syn_crn (syn_cin (syn_cins4
                (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
              (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N))
      (syn_wrex g N (syn_wbr (.cv g) (syn_crn (syn_cin (syn_cins4
                (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
              (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_cop (.cv b) (.cv a))))
      (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))) p0001 p0002
      p0040
  have p0042 :=
    @g_rexbii
      (syn_wbr (.cv b) (syn_cima (syn_crn (syn_cin (syn_cins4
                (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
              (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (.cv a))
      (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))) b M p0041
  have p0043 :=
    @g_bitri
      (.classMem (.cv a) (syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4
                  (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
                (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M))
      (syn_wrex b M (syn_wbr (.cv b) (syn_cima (syn_crn (syn_cin (syn_cins4
                  (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
                (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (.cv a)))
      (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))
      p0000 p0042
  have p0044 :=
    @g_eqabi
      (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))
      a
      (syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4
                (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
              (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M)
      dv_cache_0015 p0043
  have p0045 := @g_crossex
  have p0046 := @g_n_2ndex
  have p0047 := @g_n_1stex
  have p0048 := @g_txpex (syn_c2nd) (syn_c1st) p0046 p0047
  have p0049 := @g_txpex (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)) p0045 p0048
  have p0050 := @g_rnex (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st))) p0049
  have p0051 :=
    @g_ins4ex (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))) p0050
  have p0052 := @g_enex
  have p0053 := @g_cnvex (syn_cen) p0052
  have p0054 := @g_ins2ex (syn_ccnv (syn_cen)) p0053
  have p0055 := @g_ins2ex (syn_cins2 (syn_ccnv (syn_cen))) p0054
  have p0056 :=
    @g_inex (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
      (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))) p0051 p0055
  have p0057 :=
    @g_rnex
      (syn_cin (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
        (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))
      p0056
  have p0058 :=
    @g_imaexg
      (syn_crn (syn_cin
          (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
          (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen))))))
      N (syn_cvv) (syn_cncs)
  have p0059 :=
    @g_mpan
      (.classMem (syn_crn (syn_cin
            (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
            (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) (syn_cvv))
      (.classMem N (syn_cncs))
      (.classMem (syn_cima (syn_crn (syn_cin (syn_cins4
                (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
              (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (syn_cvv))
      p0057 p0058
  have p0060 :=
    @g_imaexg
      (syn_cima (syn_crn (syn_cin
            (syn_cins4 (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
            (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N)
      M (syn_cvv) (syn_cncs)
  have p0061 :=
    @g_sylan (.classMem N (syn_cncs))
      (.classMem (syn_cima (syn_crn (syn_cin (syn_cins4
                (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
              (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) (syn_cvv))
      (.classMem M (syn_cncs))
      (.classMem (syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4
                  (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
                (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M) (syn_cvv))
      p0059 p0060
  have p0062 :=
    @g_ancoms (.classMem N (syn_cncs)) (.classMem M (syn_cncs))
      (.classMem (syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4
                  (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
                (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M) (syn_cvv))
      p0061
  have p0063 :=
    @g_syl5eqelr (syn_wa (.classMem M (syn_cncs)) (.classMem N (syn_cncs)))
      (.cab a (syn_wrex b M
          (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))
      (syn_cima (syn_cima (syn_crn (syn_cin (syn_cins4
                (syn_crn (syn_ctxp (syn_ccross) (syn_ctxp (syn_c2nd) (syn_c1st)))))
              (syn_cins2 (syn_cins2 (syn_ccnv (syn_cen)))))) N) M)
      (syn_cvv) p0044 p0062
  have p0064 :=
    @g_rexeq (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))) b
      (.cv m) M dv_cache_0016 dv_cache_0003
  have p0065 :=
    @g_abbidv (.classEq (.cv m) M)
      (syn_wrex b (.cv m)
        (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))
      (syn_wrex b M (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))
      a dv_cache_0017 p0064
  have p0066 :=
    @g_rexeq (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))) g (.cv n) N
      dv_cache_0018 dv_cache_0006
  have p0067 :=
    @g_rexbidv (.classEq (.cv n) N)
      (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))
      (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))) b M
      dv_cache_0019 p0066
  have p0068 :=
    @g_abbidv (.classEq (.cv n) N)
      (syn_wrex b M (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))
      (syn_wrex b M (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))
      a dv_cache_0020 p0067
  have p0069 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_muc g m n a b
      dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
      dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
  have p0070 :=
    @g_ovmpt2g m n M N (syn_cncs) (syn_cncs)
      (.cab a (syn_wrex b (.cv m)
          (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))
      (.cab a (syn_wrex b M
          (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))
      (syn_cmuc)
      (.cab a (syn_wrex b M
          (syn_wrex g (.cv n) (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g))))))
      (syn_cvv) dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
      dv_cache_0030 p0065 p0068 p0069
  have p0071 :=
    @g_mpd3an3 (.classMem M (syn_cncs)) (.classMem N (syn_cncs))
      (.classMem (.cab a (syn_wrex b M
            (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))) (syn_cvv))
      (.classEq (syn_co M (syn_cmuc) N) (.cab a (syn_wrex b M
            (syn_wrex g N (syn_wbr (.cv a) (syn_cen) (syn_cxp (.cv b) (.cv g)))))))
      p0063 p0070
  exact p0071


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part045`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_mucnc (A : Class) (B : Class)
    (hyp_mucnc_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_mucnc_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_co (syn_cnc A) (syn_cmuc) (syn_cnc B)) (syn_cnc (syn_cxp A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have dv_cache_0001 : x ∉ ((syn_cnc A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((syn_cnc A)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_y_not_A,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_x_not_B,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_y_not_B,
          not_false_eq_true])
  have dv_cache_0005 : z ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_z_not_B,
          not_false_eq_true])
  have dv_cache_0006 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0007 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0009 : x ∉ ((syn_cxp A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((syn_cen)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 : z ∉ ((syn_cnc A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_z_not_A,
          not_false_eq_true])
  have dv_cache_0012 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0013 : z ∉ (A).fv :=
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
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0014 : y ∉ (B).fv :=
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
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0015 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0016 :
    y ∉
      ((syn_wa (syn_wa (syn_wbr A (syn_cen) A) (syn_wbr B (syn_cen) B))
          (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 :
    z ∉
      ((syn_wa (syn_wa (syn_wbr A (syn_cen) A) (syn_wbr B (syn_cen) B))
          (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 : y ∉ ((syn_wbr (syn_cxp A B) (syn_cen) (.cv x))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((syn_wbr (syn_cxp A B) (syn_cen) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_not_B, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_ncelncsi A hyp_mucnc_1
  have p0001 := @g_ncelncsi B hyp_mucnc_2
  have p0002 :=
    @g_ovmuc z (syn_cnc A) (syn_cnc B) x y dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0003 :=
    @g_mp2an (.classMem (syn_cnc A) (syn_cncs)) (.classMem (syn_cnc B) (syn_cncs))
      (.classEq (syn_co (syn_cnc A) (syn_cmuc) (syn_cnc B)) (.cab x (syn_wrex y (syn_cnc A)
            (syn_wrex z (syn_cnc B) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z)))))))
      p0000 p0001 p0002
  have p0004 := (Nominal.classEqRefl (syn_cnc (syn_cxp A B)))
  have p0005 := @g_dfec2 x (syn_cxp A B) (syn_cen) dv_cache_0009 dv_cache_0010
  have p0006 := @g_elnc (.cv y) A
  have p0007 := @g_elnc (.cv z) B
  have p0008 :=
    @g_anbi12i (.classMem (.cv y) (syn_cnc A)) (syn_wbr (.cv y) (syn_cen) A)
      (.classMem (.cv z) (syn_cnc B)) (syn_wbr (.cv z) (syn_cen) B) p0006 p0007
  have p0009 := @g_ensym (.cv x) (syn_cxp (.cv y) (.cv z))
  have p0010 :=
    @g_anbi12i (syn_wa (.classMem (.cv y) (syn_cnc A)) (.classMem (.cv z) (syn_cnc B)))
      (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B))
      (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z)))
      (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x)) p0008 p0009
  have p0011 :=
    @g_n_2exbii
      (syn_wa (syn_wa (.classMem (.cv y) (syn_cnc A)) (.classMem (.cv z) (syn_cnc B)))
        (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z))))
      (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B))
        (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x)))
      y z p0010
  have p0012 :=
    @g_r2ex (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z))) y z (syn_cnc A)
      (syn_cnc B) dv_cache_0011 dv_cache_0008
  have p0013 := @g_enrflx A hyp_mucnc_1
  have p0014 := @g_enrflx B hyp_mucnc_2
  have p0015 := @g_breq1 (.cv y) A A (syn_cen)
  have p0016 := @g_breq1 (.cv z) B B (syn_cen)
  have p0017 :=
    @g_bi2anan9 (.classEq (.cv y) A) (syn_wbr (.cv y) (syn_cen) A) (syn_wbr A (syn_cen) A)
      (.classEq (.cv z) B) (syn_wbr (.cv z) (syn_cen) B) (syn_wbr B (syn_cen) B) p0015
      p0016
  have p0018 := @g_xpeq12 (.cv y) A (.cv z) B
  have p0019 :=
    @g_breq1d (syn_wa (.classEq (.cv y) A) (.classEq (.cv z) B)) (syn_cxp (.cv y) (.cv z))
      (syn_cxp A B) (.cv x) (syn_cen) p0018
  have p0020 :=
    @g_anbi12d (syn_wa (.classEq (.cv y) A) (.classEq (.cv z) B))
      (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B))
      (syn_wa (syn_wbr A (syn_cen) A) (syn_wbr B (syn_cen) B))
      (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x))
      (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) p0017 p0019
  have p0021 :=
    @g_spc2ev
      (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B))
        (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x)))
      (syn_wa (syn_wa (syn_wbr A (syn_cen) A) (syn_wbr B (syn_cen) B))
        (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)))
      y z A B dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0008 hyp_mucnc_1 hyp_mucnc_2 p0020
  have p0022 :=
    @g_mpanl12 (syn_wbr A (syn_cen) A) (syn_wbr B (syn_cen) B)
      (syn_wbr (syn_cxp A B) (syn_cen) (.cv x))
      (syn_wex y (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B))
            (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x)))))
      p0013 p0014 p0021
  have p0023 := @g_xpen (.cv y) A (.cv z) B
  have p0024 := @g_ensym (syn_cxp (.cv y) (.cv z)) (syn_cxp A B)
  have p0025 :=
    @g_sylib (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B))
      (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (syn_cxp A B))
      (syn_wbr (syn_cxp A B) (syn_cen) (syn_cxp (.cv y) (.cv z))) p0023 p0024
  have p0026 := @g_entr (syn_cxp A B) (syn_cxp (.cv y) (.cv z)) (.cv x)
  have p0027 :=
    @g_sylan (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B))
      (syn_wbr (syn_cxp A B) (syn_cen) (syn_cxp (.cv y) (.cv z)))
      (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x))
      (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) p0025 p0026
  have p0028 :=
    @g_exlimivv
      (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B))
        (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x)))
      (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) y z dv_cache_0018 dv_cache_0019 p0027
  have p0029 :=
    @g_impbii (syn_wbr (syn_cxp A B) (syn_cen) (.cv x))
      (syn_wex y (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B))
            (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x)))))
      p0022 p0028
  have p0030 :=
    @g_n_3bitr4ri
      (syn_wex y (syn_wex z
          (syn_wa (syn_wa (.classMem (.cv y) (syn_cnc A)) (.classMem (.cv z) (syn_cnc B)))
            (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z))))))
      (syn_wex y (syn_wex z
          (syn_wa (syn_wa (syn_wbr (.cv y) (syn_cen) A) (syn_wbr (.cv z) (syn_cen) B))
            (syn_wbr (syn_cxp (.cv y) (.cv z)) (syn_cen) (.cv x)))))
      (syn_wrex y (syn_cnc A)
        (syn_wrex z (syn_cnc B) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z)))))
      (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)) p0011 p0012 p0029
  have p0031 :=
    @g_abbii (syn_wbr (syn_cxp A B) (syn_cen) (.cv x))
      (syn_wrex y (syn_cnc A)
        (syn_wrex z (syn_cnc B) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z)))))
      x p0030
  have p0032 :=
    @g_n_3eqtrri (syn_cnc (syn_cxp A B)) (syn_cec (syn_cxp A B) (syn_cen))
      (.cab x (syn_wbr (syn_cxp A B) (syn_cen) (.cv x)))
      (.cab x (syn_wrex y (syn_cnc A)
          (syn_wrex z (syn_cnc B) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z))))))
      p0004 p0005 p0031
  have p0033 :=
    @g_eqtri (syn_co (syn_cnc A) (syn_cmuc) (syn_cnc B))
      (.cab x (syn_wrex y (syn_cnc A)
          (syn_wrex z (syn_cnc B) (syn_wbr (.cv x) (syn_cen) (syn_cxp (.cv y) (.cv z))))))
      (syn_cnc (syn_cxp A B)) p0003 p0032
  exact p0033

@[expose]
noncomputable def g_muccl (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
        (.classMem (syn_co A (syn_cmuc) B) (syn_cncs))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (syn_co A (syn_cmuc) B) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Wff.classMem (syn_co A (syn_cmuc) B) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_elncs x A dv_cache_0001
  have p0001 := @g_elncs y B dv_cache_0002
  have p0002 :=
    @g_anbi12i (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x))))
      (.classMem B (syn_cncs)) (syn_wex y (.classEq B (syn_cnc (.cv y)))) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wa (syn_wex x (.classEq A (syn_cnc (.cv x))))
        (syn_wex y (.classEq B (syn_cnc (.cv y)))))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))))
      p0002 p0003
  have p0005 := @g_oveq12 A (syn_cnc (.cv x)) B (syn_cnc (.cv y)) (syn_cmuc)
  have p0006 := @g_vex x
  have p0007 := @g_vex y
  have p0008 := @g_mucnc (.cv x) (.cv y) p0006 p0007
  have p0009 := @g_xpex (.cv x) (.cv y) p0006 p0007
  have p0010 := @g_ncelncsi (syn_cxp (.cv x) (.cv y)) p0009
  have p0011 :=
    @g_eqeltri (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y)))
      (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_cncs) p0008 p0010
  have p0012 :=
    @g_syl6eqel (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))
      (syn_co A (syn_cmuc) B) (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y)))
      (syn_cncs) p0005 p0011
  have p0013 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))
      (.classMem (syn_co A (syn_cmuc) B) (syn_cncs)) x y dv_cache_0005 dv_cache_0006 p0012
  have p0014 :=
    @g_sylbi (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))))
      (.classMem (syn_co A (syn_cmuc) B) (syn_cncs)) p0004 p0013
  exact p0014

@[expose]
noncomputable def g_muccom (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
        (.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0005 :
    x ∉ ((Wff.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    y ∉ ((Wff.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_co,
          NFChoice.Compiler.WPPCompactSyntaxFVExplicit.fv_syn_cmuc, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_elncs x A dv_cache_0001
  have p0001 := @g_elncs y B dv_cache_0002
  have p0002 :=
    @g_anbi12i (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x))))
      (.classMem B (syn_cncs)) (syn_wex y (.classEq B (syn_cnc (.cv y)))) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wa (syn_wex x (.classEq A (syn_cnc (.cv x))))
        (syn_wex y (.classEq B (syn_cnc (.cv y)))))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))))
      p0002 p0003
  have p0005 := @g_vex x
  have p0006 := @g_vex y
  have p0007 := @g_xpcomen (.cv x) (.cv y) p0005 p0006
  have p0008 := @g_xpex (.cv x) (.cv y) p0005 p0006
  have p0009 := @g_eqnc (syn_cxp (.cv x) (.cv y)) (syn_cxp (.cv y) (.cv x)) p0008
  have p0010 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_cnc (syn_cxp (.cv y) (.cv x))))
      (syn_wbr (syn_cxp (.cv x) (.cv y)) (syn_cen) (syn_cxp (.cv y) (.cv x))) p0007 p0009
  have p0011 := @g_mucnc (.cv x) (.cv y) p0005 p0006
  have p0012 := @g_mucnc (.cv y) (.cv x) p0006 p0005
  have p0013 :=
    @g_n_3eqtr4i (syn_cnc (syn_cxp (.cv x) (.cv y))) (syn_cnc (syn_cxp (.cv y) (.cv x)))
      (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y)))
      (syn_co (syn_cnc (.cv y)) (syn_cmuc) (syn_cnc (.cv x))) p0010 p0011 p0012
  have p0014 := @g_oveq12 A (syn_cnc (.cv x)) B (syn_cnc (.cv y)) (syn_cmuc)
  have p0015 := @g_oveq12 B (syn_cnc (.cv y)) A (syn_cnc (.cv x)) (syn_cmuc)
  have p0016 :=
    @g_ancoms (.classEq B (syn_cnc (.cv y))) (.classEq A (syn_cnc (.cv x)))
      (.classEq (syn_co B (syn_cmuc) A) (syn_co (syn_cnc (.cv y)) (syn_cmuc) (syn_cnc (.cv x))))
      p0015
  have p0017 :=
    @g_n_3eqtr4a (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))
      (syn_co (syn_cnc (.cv x)) (syn_cmuc) (syn_cnc (.cv y)))
      (syn_co (syn_cnc (.cv y)) (syn_cmuc) (syn_cnc (.cv x))) (syn_co A (syn_cmuc) B)
      (syn_co B (syn_cmuc) A) p0013 p0014 p0016
  have p0018 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))
      (.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A)) x y dv_cache_0005
      dv_cache_0006 p0017
  have p0019 :=
    @g_sylbi (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))))
      (.classEq (syn_co A (syn_cmuc) B) (syn_co B (syn_cmuc) A)) p0004 p0018
  exact p0019

@[expose]
noncomputable def g_ncdisjun (A : Class) (B : Class)
    (hyp_ncdisjun_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_ncdisjun_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (.imp (.classEq (syn_cin A B) (syn_c0))
        (.classEq (syn_cnc (syn_cun A B)) (syn_cplc (syn_cnc A) (syn_cnc B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let r : Var := freshVar proofSupport 1
  let p : Var := freshVar proofSupport 2
  let q : Var := freshVar proofSupport 3
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_r : r ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_r_not_A : r ∉ A.fv := by
    intro h
    exact fresh_r (Finset.mem_union_left _ (h))
  have fresh_r_not_B : r ∉ B.fv := by
    intro h
    exact fresh_r (Finset.mem_union_right _ (h))
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_p_not_A : p ∉ A.fv := by
    intro h
    exact fresh_p (Finset.mem_union_left _ (h))
  have fresh_p_not_B : p ∉ B.fv := by
    intro h
    exact fresh_p (Finset.mem_union_right _ (h))
  have fresh_q : q ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_q_not_A : q ∉ A.fv := by
    intro h
    exact fresh_q (Finset.mem_union_left _ (h))
  have fresh_q_not_B : q ∉ B.fv := by
    intro h
    exact fresh_q (Finset.mem_union_right _ (h))
  have fresh_x_ne_r : x ≠ r :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_r_ne_x : r ≠ x := Ne.symm fresh_x_ne_r
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_x_ne_q : x ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have dv_cache_0001 : r ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_r_ne_x, not_false_eq_true])
  have dv_cache_0002 : r ∉ ((syn_cun A B)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_r_not_A, fresh_r_not_B, or_false, not_false_eq_true])
  have dv_cache_0003 :
    r ∉ ((Wff.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          Finset.mem_singleton, fresh_r_ne_x, fresh_r_not_A, fresh_r_not_B, or_false,
          not_false_eq_true])
  have dv_cache_0004 : r ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : r ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_r_not_A, fresh_r_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : p ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_x, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_x, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((syn_cnc A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_p_not_A,
          not_false_eq_true])
  have dv_cache_0008 : q ∉ ((syn_cnc A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_q_not_A,
          not_false_eq_true])
  have dv_cache_0009 : p ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_p_not_B,
          not_false_eq_true])
  have dv_cache_0010 : q ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_q_not_B,
          not_false_eq_true])
  have dv_cache_0011 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0012 : p ∉ ((syn_wbr (.cv x) (syn_cen) (syn_cun A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_x, fresh_p_not_A, fresh_p_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : q ∉ ((syn_wbr (.cv x) (syn_cen) (syn_cun A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_x, fresh_q_not_A, fresh_q_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : p ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_p_not_A, fresh_p_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 : q ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_q_not_A, fresh_q_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_cnc (syn_cun A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0017 : x ∉ ((syn_cplc (syn_cnc A) (syn_cnc B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((Wff.classEq (syn_cin A B) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_elnc (.cv x) (syn_cun A B)
  have p0001 := @g_bren (.cv x) (syn_cun A B) r dv_cache_0001 dv_cache_0002
  have p0002 := @g_f1ocnv (.cv x) (syn_cun A B) (.cv r)
  have p0003 := @g_imaundi (syn_ccnv (.cv r)) A B
  have p0004 := @g_imadmrn (syn_ccnv (.cv r))
  have p0005 :=
    @g_a1i
      (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_cdm (syn_ccnv (.cv r))))
        (syn_crn (syn_ccnv (.cv r))))
      (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) p0004
  have p0006 := @g_f1odm (syn_cun A B) (.cv x) (syn_ccnv (.cv r))
  have p0007 :=
    @g_imaeq2d (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_cdm (syn_ccnv (.cv r))) (syn_cun A B) (syn_ccnv (.cv r)) p0006
  have p0008 := @g_f1ofo (syn_cun A B) (.cv x) (syn_ccnv (.cv r))
  have p0009 := @g_forn (syn_cun A B) (.cv x) (syn_ccnv (.cv r))
  have p0010 :=
    @g_syl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wfo (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (.classEq (syn_crn (syn_ccnv (.cv r))) (.cv x)) p0008 p0009
  have p0011 :=
    @g_n_3eqtr3d (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_cima (syn_ccnv (.cv r)) (syn_cdm (syn_ccnv (.cv r))))
      (syn_crn (syn_ccnv (.cv r))) (syn_cima (syn_ccnv (.cv r)) (syn_cun A B)) (.cv x)
      p0005 p0007 p0010
  have p0012 :=
    @g_syl5eqr (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_cun (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B))
      (syn_cima (syn_ccnv (.cv r)) (syn_cun A B)) (.cv x) p0003 p0011
  have p0013 :=
    @g_adantl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (.classEq (syn_cun (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B))
        (.cv x))
      (.classEq (syn_cin A B) (syn_c0)) p0012
  have p0014 := @g_f1of1 (syn_cun A B) (.cv x) (syn_ccnv (.cv r))
  have p0015 := @g_ssun1 A B
  have p0016 := @g_f1ores (syn_cun A B) (.cv x) A (syn_ccnv (.cv r))
  have p0017 :=
    @g_sylancl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wf1 (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wss A (syn_cun A B))
      (syn_wf1o (syn_cres (syn_ccnv (.cv r)) A) A (syn_cima (syn_ccnv (.cv r)) A)) p0014
      p0015 p0016
  have p0018 :=
    @g_f1ocnv A (syn_cima (syn_ccnv (.cv r)) A) (syn_cres (syn_ccnv (.cv r)) A)
  have p0019 := @g_vex r
  have p0020 := @g_cnvex (.cv r) p0019
  have p0021 := @g_resex (syn_ccnv (.cv r)) A p0020 hyp_ncdisjun_1
  have p0022 := @g_cnvex (syn_cres (syn_ccnv (.cv r)) A) p0021
  have p0023 :=
    @g_f1oen (syn_cima (syn_ccnv (.cv r)) A) A (syn_ccnv (syn_cres (syn_ccnv (.cv r)) A))
      p0022
  have p0024 :=
    @g_n_3syl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wf1o (syn_cres (syn_ccnv (.cv r)) A) A (syn_cima (syn_ccnv (.cv r)) A))
      (syn_wf1o (syn_ccnv (syn_cres (syn_ccnv (.cv r)) A)) (syn_cima (syn_ccnv (.cv r)) A) A)
      (syn_wbr (syn_cima (syn_ccnv (.cv r)) A) (syn_cen) A) p0017 p0018 p0023
  have p0025 := @g_elnc (syn_cima (syn_ccnv (.cv r)) A) A
  have p0026 :=
    @g_sylibr (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wbr (syn_cima (syn_ccnv (.cv r)) A) (syn_cen) A)
      (.classMem (syn_cima (syn_ccnv (.cv r)) A) (syn_cnc A)) p0024 p0025
  have p0027 :=
    @g_adantl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (.classMem (syn_cima (syn_ccnv (.cv r)) A) (syn_cnc A))
      (.classEq (syn_cin A B) (syn_c0)) p0026
  have p0028 := @g_ssun2 B A
  have p0029 := @g_f1ores (syn_cun A B) (.cv x) B (syn_ccnv (.cv r))
  have p0030 :=
    @g_sylancl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wf1 (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) (syn_wss B (syn_cun A B))
      (syn_wf1o (syn_cres (syn_ccnv (.cv r)) B) B (syn_cima (syn_ccnv (.cv r)) B)) p0014
      p0028 p0029
  have p0031 :=
    @g_f1ocnv B (syn_cima (syn_ccnv (.cv r)) B) (syn_cres (syn_ccnv (.cv r)) B)
  have p0032 := @g_resex (syn_ccnv (.cv r)) B p0020 hyp_ncdisjun_2
  have p0033 := @g_cnvex (syn_cres (syn_ccnv (.cv r)) B) p0032
  have p0034 :=
    @g_f1oen (syn_cima (syn_ccnv (.cv r)) B) B (syn_ccnv (syn_cres (syn_ccnv (.cv r)) B))
      p0033
  have p0035 :=
    @g_n_3syl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wf1o (syn_cres (syn_ccnv (.cv r)) B) B (syn_cima (syn_ccnv (.cv r)) B))
      (syn_wf1o (syn_ccnv (syn_cres (syn_ccnv (.cv r)) B)) (syn_cima (syn_ccnv (.cv r)) B) B)
      (syn_wbr (syn_cima (syn_ccnv (.cv r)) B) (syn_cen) B) p0030 p0031 p0034
  have p0036 :=
    @g_adantl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wbr (syn_cima (syn_ccnv (.cv r)) B) (syn_cen) B)
      (.classEq (syn_cin A B) (syn_c0)) p0035
  have p0037 := @g_elnc (syn_cima (syn_ccnv (.cv r)) B) B
  have p0038 :=
    @g_sylibr
      (syn_wa (.classEq (syn_cin A B) (syn_c0))
        (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)))
      (syn_wbr (syn_cima (syn_ccnv (.cv r)) B) (syn_cen) B)
      (.classMem (syn_cima (syn_ccnv (.cv r)) B) (syn_cnc B)) p0036 p0037
  have p0039 := (Nominal.biimpRefl (syn_wf1 (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)))
  have p0040 :=
    @g_simprbi (syn_wf1 (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wf (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wfun (syn_ccnv (syn_ccnv (.cv r)))) p0039
  have p0041 := @g_imain A B (syn_ccnv (.cv r))
  have p0042 :=
    @g_n_3syl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wf1 (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (syn_wfun (syn_ccnv (syn_ccnv (.cv r))))
      (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_cin A B))
        (syn_cin (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B)))
      p0014 p0040 p0041
  have p0043 :=
    @g_adantl (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_cin A B))
        (syn_cin (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B)))
      (.classEq (syn_cin A B) (syn_c0)) p0042
  have p0044 := @g_imaeq2 (syn_cin A B) (syn_c0) (syn_ccnv (.cv r))
  have p0045 := @g_ima0 (syn_ccnv (.cv r))
  have p0046 :=
    @g_syl6eq (.classEq (syn_cin A B) (syn_c0))
      (syn_cima (syn_ccnv (.cv r)) (syn_cin A B)) (syn_cima (syn_ccnv (.cv r)) (syn_c0))
      (syn_c0) p0044 p0045
  have p0047 :=
    @g_adantr (.classEq (syn_cin A B) (syn_c0))
      (.classEq (syn_cima (syn_ccnv (.cv r)) (syn_cin A B)) (syn_c0))
      (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)) p0046
  have p0048 :=
    @g_eqtr3d
      (syn_wa (.classEq (syn_cin A B) (syn_c0))
        (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)))
      (syn_cima (syn_ccnv (.cv r)) (syn_cin A B))
      (syn_cin (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B)) (syn_c0)
      p0043 p0047
  have p0049 :=
    @g_eladdci (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B) (syn_cnc A)
      (syn_cnc B)
  have p0050 :=
    @g_syl3anc
      (syn_wa (.classEq (syn_cin A B) (syn_c0))
        (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)))
      (.classMem (syn_cima (syn_ccnv (.cv r)) A) (syn_cnc A))
      (.classMem (syn_cima (syn_ccnv (.cv r)) B) (syn_cnc B))
      (.classEq (syn_cin (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B))
        (syn_c0))
      (.classMem (syn_cun (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B))
        (syn_cplc (syn_cnc A) (syn_cnc B)))
      p0027 p0038 p0048 p0049
  have p0051 :=
    @g_eqeltrrd
      (syn_wa (.classEq (syn_cin A B) (syn_c0))
        (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x)))
      (syn_cun (syn_cima (syn_ccnv (.cv r)) A) (syn_cima (syn_ccnv (.cv r)) B)) (.cv x)
      (syn_cplc (syn_cnc A) (syn_cnc B)) p0013 p0050
  have p0052 :=
    @g_ex (.classEq (syn_cin A B) (syn_c0))
      (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) p0051
  have p0053 :=
    @g_syl5 (syn_wf1o (.cv r) (.cv x) (syn_cun A B))
      (syn_wf1o (syn_ccnv (.cv r)) (syn_cun A B) (.cv x))
      (.classEq (syn_cin A B) (syn_c0))
      (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) p0002 p0052
  have p0054 :=
    @g_exlimdv (.classEq (syn_cin A B) (syn_c0)) (syn_wf1o (.cv r) (.cv x) (syn_cun A B))
      (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) r dv_cache_0003 dv_cache_0004
      p0053
  have p0055 :=
    @g_syl5bi (syn_wbr (.cv x) (syn_cen) (syn_cun A B))
      (syn_wex r (syn_wf1o (.cv r) (.cv x) (syn_cun A B)))
      (.classEq (syn_cin A B) (syn_c0))
      (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) p0001 p0054
  have p0056 :=
    @g_eladdc (.cv x) (syn_cnc A) (syn_cnc B) p q dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0057 :=
    @g_simplrl (.classEq (syn_cin A B) (syn_c0)) (.classMem (.cv p) (syn_cnc A))
      (.classMem (.cv q) (syn_cnc B)) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
  have p0058 := @g_elnc (.cv p) A
  have p0059 :=
    @g_sylib
      (syn_wa (syn_wa (.classEq (syn_cin A B) (syn_c0))
          (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B))))
        (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0)))
      (.classMem (.cv p) (syn_cnc A)) (syn_wbr (.cv p) (syn_cen) A) p0057 p0058
  have p0060 :=
    @g_simplrr (.classEq (syn_cin A B) (syn_c0)) (.classMem (.cv p) (syn_cnc A))
      (.classMem (.cv q) (syn_cnc B)) (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
  have p0061 := @g_elnc (.cv q) B
  have p0062 :=
    @g_sylib
      (syn_wa (syn_wa (.classEq (syn_cin A B) (syn_c0))
          (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B))))
        (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0)))
      (.classMem (.cv q) (syn_cnc B)) (syn_wbr (.cv q) (syn_cen) B) p0060 p0061
  have p0063 :=
    @g_simpr
      (syn_wa (.classEq (syn_cin A B) (syn_c0))
        (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B))))
      (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
  have p0064 :=
    @g_simpll (.classEq (syn_cin A B) (syn_c0))
      (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B)))
      (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
  have p0065 := @g_unen (.cv p) A (.cv q) B
  have p0066 :=
    @g_syl22anc
      (syn_wa (syn_wa (.classEq (syn_cin A B) (syn_c0))
          (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B))))
        (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0)))
      (syn_wbr (.cv p) (syn_cen) A) (syn_wbr (.cv q) (syn_cen) B)
      (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0)) (.classEq (syn_cin A B) (syn_c0))
      (syn_wbr (syn_cun (.cv p) (.cv q)) (syn_cen) (syn_cun A B)) p0059 p0062 p0063 p0064
      p0065
  have p0067 := @g_breq1 (.cv x) (syn_cun (.cv p) (.cv q)) (syn_cun A B) (syn_cen)
  have p0068 :=
    @g_syl5ibrcom
      (syn_wa (syn_wa (.classEq (syn_cin A B) (syn_c0))
          (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B))))
        (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0)))
      (syn_wbr (.cv x) (syn_cen) (syn_cun A B))
      (.classEq (.cv x) (syn_cun (.cv p) (.cv q)))
      (syn_wbr (syn_cun (.cv p) (.cv q)) (syn_cen) (syn_cun A B)) p0066 p0067
  have p0069 :=
    @g_expimpd
      (syn_wa (.classEq (syn_cin A B) (syn_c0))
        (syn_wa (.classMem (.cv p) (syn_cnc A)) (.classMem (.cv q) (syn_cnc B))))
      (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
      (.classEq (.cv x) (syn_cun (.cv p) (.cv q)))
      (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) p0068
  have p0070 :=
    @g_rexlimdvva (.classEq (syn_cin A B) (syn_c0))
      (syn_wa (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
        (.classEq (.cv x) (syn_cun (.cv p) (.cv q))))
      (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) p q (syn_cnc A) (syn_cnc B) dv_cache_0008
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0011 p0069
  have p0071 :=
    @g_syl5bi (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B)))
      (syn_wrex p (syn_cnc A) (syn_wrex q (syn_cnc B)
          (syn_wa (.classEq (syn_cin (.cv p) (.cv q)) (syn_c0))
            (.classEq (.cv x) (syn_cun (.cv p) (.cv q))))))
      (.classEq (syn_cin A B) (syn_c0)) (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) p0056
      p0070
  have p0072 :=
    @g_impbid (.classEq (syn_cin A B) (syn_c0)) (syn_wbr (.cv x) (syn_cen) (syn_cun A B))
      (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) p0055 p0071
  have p0073 :=
    @g_syl5bb (.classMem (.cv x) (syn_cnc (syn_cun A B)))
      (syn_wbr (.cv x) (syn_cen) (syn_cun A B)) (.classEq (syn_cin A B) (syn_c0))
      (.classMem (.cv x) (syn_cplc (syn_cnc A) (syn_cnc B))) p0000 p0072
  have p0074 :=
    @g_eqrdv (.classEq (syn_cin A B) (syn_c0)) x (syn_cnc (syn_cun A B))
      (syn_cplc (syn_cnc A) (syn_cnc B)) dv_cache_0016 dv_cache_0017 dv_cache_0018 p0073
  exact p0074


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part046`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_df0c2 : Nominal.NPrf (.classEq (syn_c0c) (syn_cnc (syn_c0))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((syn_c0)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cen)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_c0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_dfec2 x (syn_c0) (syn_cen) dv_cache_0001 dv_cache_0002
  have p0001 := (Nominal.classEqRefl (syn_cnc (syn_c0)))
  have p0002 := @g_en0 (.cv x)
  have p0003 := @g_ensym (syn_c0) (.cv x)
  have p0004 := @g_el0c (.cv x)
  have p0005 :=
    @g_n_3bitr4ri (syn_wbr (.cv x) (syn_cen) (syn_c0)) (.classEq (.cv x) (syn_c0))
      (syn_wbr (syn_c0) (syn_cen) (.cv x)) (.classMem (.cv x) (syn_c0c)) p0002 p0003 p0004
  have p0006 :=
    @g_eqabi (syn_wbr (syn_c0) (syn_cen) (.cv x)) x (syn_c0c) dv_cache_0003 p0005
  have p0007 :=
    @g_n_3eqtr4ri (syn_cec (syn_c0) (syn_cen))
      (.cab x (syn_wbr (syn_c0) (syn_cen) (.cv x))) (syn_cnc (syn_c0)) (syn_c0c) p0000
      p0001 p0006
  exact p0007

@[expose]
noncomputable def g_n_0cnc : Nominal.NPrf (.classMem (syn_c0c) (syn_cncs)) :=
  by
  have p0000 := @g_df0c2
  have p0001 := @g_n_0ex
  have p0002 := @g_ncelncsi (syn_c0) p0001
  have p0003 := @g_eqeltri (syn_c0c) (syn_cnc (syn_c0)) (syn_cncs) p0000 p0002
  exact p0003

@[expose]
noncomputable def g_n_1cnc : Nominal.NPrf (.classMem (syn_c1c) (syn_cncs)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let f : Var := freshVar proofSupport 3
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_f : x ≠ f :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_f_ne_x : f ≠ x := Ne.symm fresh_x_ne_f
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_f : y ≠ f :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_f_ne_y : f ≠ y := Ne.symm fresh_y_ne_f
  have fresh_z_ne_f : z ≠ f :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_f_ne_z : f ≠ z := Ne.symm fresh_z_ne_f
  have dv_cache_0001 : z ∉ ((syn_csn (.cv y))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_y,
          not_false_eq_true])
  have dv_cache_0002 : z ∉ ((syn_cen)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cen, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 : f ∉ ((syn_csn (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_f_ne_y,
          not_false_eq_true])
  have dv_cache_0006 : f ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_f_ne_z, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_cfv (.cv f) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_f, or_false, not_false_eq_true])
  have dv_cache_0008 :
    x ∉ ((Wff.classEq (.cv z) (syn_csn (syn_cfv (.cv f) (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, fresh_x_ne_y, fresh_x_ne_f, or_false,
          not_false_eq_true])
  have dv_cache_0009 : f ∉ ((syn_wex x (.classEq (.cv z) (syn_csn (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : f ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_f_ne_z, fresh_f_ne_x, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0010 : z ∉ ((syn_c1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 : x ∉ ((syn_csn (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_y,
          not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.classEq (syn_c1c) (syn_cnc (syn_csn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 : x ∉ ((syn_c1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_dfec2 z (syn_csn (.cv y)) (syn_cen) dv_cache_0001 dv_cache_0002
  have p0001 := (Nominal.classEqRefl (syn_cnc (syn_csn (.cv y))))
  have p0002 := @g_el1c x (.cv z) dv_cache_0003
  have p0003 := @g_vex y
  have p0004 := @g_vex x
  have p0005 := @g_en2sn (.cv y) (.cv x) (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      (syn_wbr (syn_csn (.cv y)) (syn_cen) (syn_csn (.cv x))) p0003 p0004 p0005
  have p0007 := @g_breq2 (.cv z) (syn_csn (.cv x)) (syn_csn (.cv y)) (syn_cen)
  have p0008 :=
    @g_mpbiri (.classEq (.cv z) (syn_csn (.cv x)))
      (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z))
      (syn_wbr (syn_csn (.cv y)) (syn_cen) (syn_csn (.cv x))) p0006 p0007
  have p0009 :=
    @g_exlimiv (.classEq (.cv z) (syn_csn (.cv x)))
      (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z)) x dv_cache_0004 p0008
  have p0010 := @g_bren (syn_csn (.cv y)) (.cv z) f dv_cache_0005 dv_cache_0006
  have p0011 := @g_f1of (syn_csn (.cv y)) (.cv z) (.cv f)
  have p0012 := @g_f1ofo (syn_csn (.cv y)) (.cv z) (.cv f)
  have p0013 := @g_forn (syn_csn (.cv y)) (.cv z) (.cv f)
  have p0014 :=
    @g_syl (syn_wf1o (.cv f) (syn_csn (.cv y)) (.cv z))
      (syn_wfo (.cv f) (syn_csn (.cv y)) (.cv z)) (.classEq (syn_crn (.cv f)) (.cv z))
      p0012 p0013
  have p0015 := @g_fsn2 (.cv y) (.cv z) (.cv f) p0003
  have p0016 := @g_rneq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y))))
  have p0017 := @g_rnsnop (.cv y) (syn_cfv (.cv f) (.cv y)) p0003
  have p0018 :=
    @g_syl6eq (.classEq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y)))))
      (syn_crn (.cv f)) (syn_crn (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y)))))
      (syn_csn (syn_cfv (.cv f) (.cv y))) p0016 p0017
  have p0019 :=
    @g_eqeq1d (.classEq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y)))))
      (syn_crn (.cv f)) (syn_csn (syn_cfv (.cv f) (.cv y))) (.cv z) p0018
  have p0020 := @g_fvex (.cv y) (.cv f)
  have p0021 := @g_sneq (.cv x) (syn_cfv (.cv f) (.cv y))
  have p0022 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cfv (.cv f) (.cv y))) (syn_csn (.cv x))
      (syn_csn (syn_cfv (.cv f) (.cv y))) (.cv z) p0021
  have p0023 :=
    @g_spcev (.classEq (.cv z) (syn_csn (.cv x)))
      (.classEq (.cv z) (syn_csn (syn_cfv (.cv f) (.cv y)))) x (syn_cfv (.cv f) (.cv y))
      dv_cache_0007 dv_cache_0008 p0020 p0022
  have p0024 :=
    @g_eqcoms (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) (.cv z)
      (syn_csn (syn_cfv (.cv f) (.cv y))) p0023
  have p0025 :=
    @g_syl6bi (.classEq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y)))))
      (.classEq (syn_crn (.cv f)) (.cv z))
      (.classEq (syn_csn (syn_cfv (.cv f) (.cv y))) (.cv z))
      (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) p0019 p0024
  have p0026 :=
    @g_adantl (.classEq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y)))))
      (.imp (.classEq (syn_crn (.cv f)) (.cv z))
        (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))))
      (.classMem (syn_cfv (.cv f) (.cv y)) (.cv z)) p0025
  have p0027 :=
    @g_sylbi (syn_wf (.cv f) (syn_csn (.cv y)) (.cv z))
      (syn_wa (.classMem (syn_cfv (.cv f) (.cv y)) (.cv z))
        (.classEq (.cv f) (syn_csn (syn_cop (.cv y) (syn_cfv (.cv f) (.cv y))))))
      (.imp (.classEq (syn_crn (.cv f)) (.cv z))
        (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))))
      p0015 p0026
  have p0028 :=
    @g_sylc (syn_wf1o (.cv f) (syn_csn (.cv y)) (.cv z))
      (syn_wf (.cv f) (syn_csn (.cv y)) (.cv z)) (.classEq (syn_crn (.cv f)) (.cv z))
      (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) p0011 p0014 p0027
  have p0029 :=
    @g_exlimiv (syn_wf1o (.cv f) (syn_csn (.cv y)) (.cv z))
      (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) f dv_cache_0009 p0028
  have p0030 :=
    @g_sylbi (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z))
      (syn_wex f (syn_wf1o (.cv f) (syn_csn (.cv y)) (.cv z)))
      (syn_wex x (.classEq (.cv z) (syn_csn (.cv x)))) p0010 p0029
  have p0031 :=
    @g_impbii (syn_wex x (.classEq (.cv z) (syn_csn (.cv x))))
      (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z)) p0009 p0030
  have p0032 :=
    @g_bitri (.classMem (.cv z) (syn_c1c))
      (syn_wex x (.classEq (.cv z) (syn_csn (.cv x))))
      (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z)) p0002 p0031
  have p0033 :=
    @g_eqabi (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z)) z (syn_c1c) dv_cache_0010 p0032
  have p0034 :=
    @g_n_3eqtr4ri (syn_cec (syn_csn (.cv y)) (syn_cen))
      (.cab z (syn_wbr (syn_csn (.cv y)) (syn_cen) (.cv z))) (syn_cnc (syn_csn (.cv y)))
      (syn_c1c) p0000 p0001 p0033
  have p0035 := @g_snex (.cv y)
  have p0036 := @g_nceq (.cv x) (syn_csn (.cv y))
  have p0037 :=
    @g_eqeq2d (.classEq (.cv x) (syn_csn (.cv y))) (syn_cnc (.cv x))
      (syn_cnc (syn_csn (.cv y))) (syn_c1c) p0036
  have p0038 :=
    @g_spcev (.classEq (syn_c1c) (syn_cnc (.cv x)))
      (.classEq (syn_c1c) (syn_cnc (syn_csn (.cv y)))) x (syn_csn (.cv y)) dv_cache_0011
      dv_cache_0012 p0035 p0037
  have p0039 := Nominal.mp p0034 p0038
  have p0040 := @g_elncs x (syn_c1c) dv_cache_0013
  have p0041 :=
    @g_mpbir (.classMem (syn_c1c) (syn_cncs))
      (syn_wex x (.classEq (syn_c1c) (syn_cnc (.cv x)))) p0039 p0040
  exact p0041

@[expose]
noncomputable def g_df1c3 (A : Class)
    (hyp_df1c3_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classEq (syn_c1c) (syn_cnc (syn_csn A))) :=
  by
  have p0000 := @g_snel1c A hyp_df1c3_1
  have p0001 := @g_n_1cnc
  have p0002 := @g_ncseqnc (syn_c1c) (syn_csn A)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_mpbir (.classEq (syn_c1c) (syn_cnc (syn_csn A))) (.classMem (syn_csn A) (syn_c1c))
      p0000 p0003
  exact p0004

@[expose]
noncomputable def g_ncaddccl (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
        (.classMem (syn_cplc A B) (syn_cncs))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0005 :
    z ∉
      ((syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
          (syn_cxp (.cv y) (syn_csn (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0006 :
    z ∉
      ((Wff.classEq (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
            (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cnc
            (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
              (syn_cxp (.cv y) (syn_csn (syn_c0))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0007 :
    z ∉
      ((syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxp,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Wff.classMem (syn_cplc A B) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Wff.classMem (syn_cplc A B) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_elncs x A dv_cache_0001
  have p0001 := @g_elncs y B dv_cache_0002
  have p0002 :=
    @g_eeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0003 := @g_vex x
  have p0004 := @g_n_0ex
  have p0005 := @g_complex (syn_c0) p0004
  have p0006 := @g_xpsnen (.cv x) (syn_ccompl (syn_c0)) p0003 p0005
  have p0007 := @g_snex (syn_ccompl (syn_c0))
  have p0008 := @g_xpex (.cv x) (syn_csn (syn_ccompl (syn_c0))) p0003 p0007
  have p0009 := @g_eqnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (.cv x) p0008
  have p0010 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (.cv x)))
      (syn_wbr (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cen) (.cv x)) p0006
      p0009
  have p0011 :=
    @g_eqcomi (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
      (syn_cnc (.cv x)) p0010
  have p0012 :=
    @g_eqtr A (syn_cnc (.cv x))
      (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
  have p0013 :=
    @g_mpan2 (.classEq A (syn_cnc (.cv x)))
      (.classEq (syn_cnc (.cv x)) (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
      (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) p0011 p0012
  have p0014 := @g_vex y
  have p0016 := @g_xpsnen (.cv y) (syn_c0) p0014 p0004
  have p0017 := @g_snex (syn_c0)
  have p0018 := @g_xpex (.cv y) (syn_csn (syn_c0)) p0014 p0017
  have p0019 := @g_eqnc (syn_cxp (.cv y) (syn_csn (syn_c0))) (.cv y) p0018
  have p0020 :=
    @g_mpbir (.classEq (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cnc (.cv y)))
      (syn_wbr (syn_cxp (.cv y) (syn_csn (syn_c0))) (syn_cen) (.cv y)) p0016 p0019
  have p0021 :=
    @g_eqcomi (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cnc (.cv y)) p0020
  have p0022 := @g_eqtr B (syn_cnc (.cv y)) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0023 :=
    @g_mpan2 (.classEq B (syn_cnc (.cv y)))
      (.classEq (syn_cnc (.cv y)) (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) p0021 p0022
  have p0024 :=
    @g_addceq12 A B (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
      (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0025 := @g_necompl (syn_c0)
  have p0026 := @g_xpnedisj (.cv x) (.cv y) (syn_ccompl (syn_c0)) (syn_c0) p0005 p0025
  have p0027 :=
    @g_ncdisjun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
      (syn_cxp (.cv y) (syn_csn (syn_c0))) p0008 p0018
  have p0028 := Nominal.mp p0026 p0027
  have p0029 :=
    @g_eqcomi
      (syn_cnc (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
          (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      p0028
  have p0030 :=
    @g_unex (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
      (syn_cxp (.cv y) (syn_csn (syn_c0))) p0008 p0018
  have p0031 :=
    @g_nceq (.cv z)
      (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
        (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0032 :=
    @g_eqeq2d
      (.classEq (.cv z) (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
          (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (syn_cnc (.cv z))
      (syn_cnc (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
          (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      p0031
  have p0033 :=
    @g_spcev
      (.classEq (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cnc (.cv z)))
      (.classEq (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cnc
          (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
            (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      z
      (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
        (syn_cxp (.cv y) (syn_csn (syn_c0))))
      dv_cache_0005 dv_cache_0006 p0030 p0032
  have p0034 := Nominal.mp p0029 p0033
  have p0035 :=
    @g_elncs z
      (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      dv_cache_0007
  have p0036 :=
    @g_mpbir
      (.classMem (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cncs))
      (syn_wex z (.classEq (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
            (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cnc (.cv z))))
      p0034 p0035
  have p0037 :=
    @g_syl6eqel
      (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
        (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (syn_cplc A B)
      (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (syn_cncs) p0024 p0036
  have p0038 :=
    @g_syl2an (.classEq A (syn_cnc (.cv x)))
      (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
      (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (.classMem (syn_cplc A B) (syn_cncs)) (.classEq B (syn_cnc (.cv y))) p0013 p0023
      p0037
  have p0039 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))
      (.classMem (syn_cplc A B) (syn_cncs)) x y dv_cache_0008 dv_cache_0009 p0038
  have p0040 :=
    @g_sylbir
      (syn_wa (syn_wex x (.classEq A (syn_cnc (.cv x))))
        (syn_wex y (.classEq B (syn_cnc (.cv y)))))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))))
      (.classMem (syn_cplc A B) (syn_cncs)) p0002 p0039
  have p0041 :=
    @g_syl2anb (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x))))
      (syn_wex y (.classEq B (syn_cnc (.cv y)))) (.classMem (syn_cplc A B) (syn_cncs))
      (.classMem B (syn_cncs)) p0000 p0001 p0040
  exact p0041

@[expose]
noncomputable def g_peano2nc (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cncs)) (.classMem (syn_cplc A (syn_c1c)) (syn_cncs))) :=
  by
  have p0000 := @g_n_1cnc
  have p0001 := @g_ncaddccl A (syn_c1c)
  have p0002 :=
    @g_mpan2 (.classMem A (syn_cncs)) (.classMem (syn_c1c) (syn_cncs))
      (.classMem (syn_cplc A (syn_c1c)) (syn_cncs)) p0000 p0001
  exact p0002

@[expose]
noncomputable def g_nnnc (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (.classMem A (syn_cncs))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_x_ne_n : x ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_x : n ≠ x := Ne.symm fresh_x_ne_n
  have dv_cache_0001 : x ∉ ((syn_cncs)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (.cv n) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : n ∉ ((Wff.classMem (.cv x) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Wff.classMem (syn_c0c) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classMem A (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Wff.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : x ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ n from (by exact fresh_x_ne_n))
  have p0000 := @g_abid2 x (syn_cncs) dv_cache_0001
  have p0001 := @g_ncsex
  have p0002 :=
    @g_eqeltri (.cab x (.classMem (.cv x) (syn_cncs))) (syn_cncs) (syn_cvv) p0000 p0001
  have p0003 := @g_eleq1 (.cv x) (syn_c0c) (syn_cncs)
  have p0004 := @g_eleq1 (.cv x) (.cv n) (syn_cncs)
  have p0005 := @g_eleq1 (.cv x) (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)
  have p0006 := @g_eleq1 (.cv x) A (syn_cncs)
  have p0007 := @g_n_0cnc
  have p0008 := @g_peano2nc (.cv n)
  have p0009 :=
    @g_a1i
      (.imp (.classMem (.cv n) (syn_cncs)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)))
      (.classMem (.cv n) (syn_cnnc)) p0008
  have p0010_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x n)
        (syn_wb (.classMem (.cv x) (syn_cncs)) (.classMem (.cv n) (syn_cncs)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cncs syn_cqs syn_wrex syn_wex syn_wa syn_cec syn_cima syn_csn
          syn_cvv syn_cen syn_copab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0010 :=
    @g_finds (.classMem (.cv x) (syn_cncs)) (.classMem (syn_c0c) (syn_cncs))
      (.classMem (.cv n) (syn_cncs)) (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs))
      (.classMem A (syn_cncs)) x n A dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0002 p0003
      p0010_e02_recanon p0005 p0006 p0007 p0009
  exact p0010

@[expose]
noncomputable def g_ncdisjeq (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
        (syn_wo (.classEq (syn_cin A B) (syn_c0)) (.classEq A B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0005 :
    x ∉ ((syn_wo (.classEq (syn_cin A B) (syn_c0)) (.classEq A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0006 :
    y ∉ ((syn_wo (.classEq (syn_cin A B) (syn_c0)) (.classEq A B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_elncs x A dv_cache_0001
  have p0001 := @g_elncs y B dv_cache_0002
  have p0002 :=
    @g_anbi12i (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x))))
      (.classMem B (syn_cncs)) (syn_wex y (.classEq B (syn_cnc (.cv y)))) p0000 p0001
  have p0003 :=
    @g_eeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @g_bitr4i (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wa (syn_wex x (.classEq A (syn_cnc (.cv x))))
        (syn_wex y (.classEq B (syn_cnc (.cv y)))))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))))
      p0002 p0003
  have p0005 := @g_ener
  have p0006 := @g_erdisj (.cv x) (.cv y) (syn_cen)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := (Nominal.classEqRefl (syn_cnc (.cv x)))
  have p0009 := @g_eqtr A (syn_cnc (.cv x)) (syn_cec (.cv x) (syn_cen))
  have p0010 :=
    @g_mpan2 (.classEq A (syn_cnc (.cv x)))
      (.classEq (syn_cnc (.cv x)) (syn_cec (.cv x) (syn_cen)))
      (.classEq A (syn_cec (.cv x) (syn_cen))) p0008 p0009
  have p0011 := (Nominal.classEqRefl (syn_cnc (.cv y)))
  have p0012 := @g_eqtr B (syn_cnc (.cv y)) (syn_cec (.cv y) (syn_cen))
  have p0013 :=
    @g_mpan2 (.classEq B (syn_cnc (.cv y)))
      (.classEq (syn_cnc (.cv y)) (syn_cec (.cv y) (syn_cen)))
      (.classEq B (syn_cec (.cv y) (syn_cen))) p0011 p0012
  have p0014 := @g_eqeq12 A (syn_cec (.cv x) (syn_cen)) B (syn_cec (.cv y) (syn_cen))
  have p0015 := @g_ineq12 A (syn_cec (.cv x) (syn_cen)) B (syn_cec (.cv y) (syn_cen))
  have p0016 :=
    @g_eqeq1d
      (syn_wa (.classEq A (syn_cec (.cv x) (syn_cen))) (.classEq B (syn_cec (.cv y) (syn_cen))))
      (syn_cin A B) (syn_cin (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen)))
      (syn_c0) p0015
  have p0017 :=
    @g_orbi12d
      (syn_wa (.classEq A (syn_cec (.cv x) (syn_cen))) (.classEq B (syn_cec (.cv y) (syn_cen))))
      (.classEq A B) (.classEq (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen)))
      (.classEq (syn_cin A B) (syn_c0))
      (.classEq (syn_cin (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen))) (syn_c0))
      p0014 p0016
  have p0018 :=
    @g_syl2an (.classEq A (syn_cnc (.cv x))) (.classEq A (syn_cec (.cv x) (syn_cen)))
      (.classEq B (syn_cec (.cv y) (syn_cen)))
      (syn_wb (syn_wo (.classEq A B) (.classEq (syn_cin A B) (syn_c0)))
        (syn_wo (.classEq (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen)))
          (.classEq (syn_cin (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen)))
            (syn_c0))))
      (.classEq B (syn_cnc (.cv y))) p0010 p0013 p0017
  have p0019 :=
    @g_mpbiri (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))
      (syn_wo (.classEq A B) (.classEq (syn_cin A B) (syn_c0)))
      (syn_wo (.classEq (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen)))
        (.classEq (syn_cin (syn_cec (.cv x) (syn_cen)) (syn_cec (.cv y) (syn_cen))) (syn_c0)))
      p0007 p0018
  have p0020 :=
    @g_orcomd (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))
      (.classEq A B) (.classEq (syn_cin A B) (syn_c0)) p0019
  have p0021 :=
    @g_exlimivv (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))
      (syn_wo (.classEq (syn_cin A B) (syn_c0)) (.classEq A B)) x y dv_cache_0005
      dv_cache_0006 p0020
  have p0022 :=
    @g_sylbi (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))))
      (syn_wo (.classEq (syn_cin A B) (syn_c0)) (.classEq A B)) p0004 p0021
  exact p0022

@[expose]
noncomputable def g_nceleq (A : Class) (B : Class) (X : Class) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
          (syn_wa (.classMem X A) (.classMem X B))) (.classEq A B)) :=
  by
  have p0000 := @g_elin X A B
  have p0001 := @g_n0i (syn_cin A B) X
  have p0002 :=
    @g_sylbir (syn_wa (.classMem X A) (.classMem X B)) (.classMem X (syn_cin A B))
      (.neg (.classEq (syn_cin A B) (syn_c0))) p0000 p0001
  have p0003 := @g_ncdisjeq A B
  have p0004 :=
    @g_ord (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (.classEq (syn_cin A B) (syn_c0)) (.classEq A B) p0003
  have p0005 :=
    @g_syl5 (syn_wa (.classMem X A) (.classMem X B))
      (.neg (.classEq (syn_cin A B) (syn_c0)))
      (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) (.classEq A B) p0002
      p0004
  have p0006 :=
    @g_imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wa (.classMem X A) (.classMem X B)) (.classEq A B) p0005
  exact p0006

@[expose]
noncomputable def g_ncpw1 (A : Class) (B : Class)
    (hyp_ncpw1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classEq (syn_cnc A) (syn_cnc B))
        (.classEq (syn_cnc (syn_cpw1 A)) (syn_cnc (syn_cpw1 B)))) :=
  by
  have p0000 := @g_enpw1 A B
  have p0001 := @g_eqnc A B hyp_ncpw1_1
  have p0002 := @g_pw1ex A hyp_ncpw1_1
  have p0003 := @g_eqnc (syn_cpw1 A) (syn_cpw1 B) p0002
  have p0004 :=
    @g_n_3bitr4i (syn_wbr A (syn_cen) B) (syn_wbr (syn_cpw1 A) (syn_cen) (syn_cpw1 B))
      (.classEq (syn_cnc A) (syn_cnc B))
      (.classEq (syn_cnc (syn_cpw1 A)) (syn_cnc (syn_cpw1 B))) p0000 p0001 p0003
  exact p0004

@[expose]
noncomputable def g_ncpwpw1 (A : Class)
    (hyp_ncpwpw1_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf
      (.classEq (syn_cnc (syn_cpw (syn_cpw1 A))) (syn_cnc (syn_cpw1 (syn_cpw A)))) :=
  by
  have p0000 := @g_enpw1pw A hyp_ncpwpw1_1
  have p0001 := @g_ensym (syn_cpw1 (syn_cpw A)) (syn_cpw (syn_cpw1 A))
  have p0002 :=
    @g_mpbi (syn_wbr (syn_cpw1 (syn_cpw A)) (syn_cen) (syn_cpw (syn_cpw1 A)))
      (syn_wbr (syn_cpw (syn_cpw1 A)) (syn_cen) (syn_cpw1 (syn_cpw A))) p0000 p0001
  have p0003 := @g_pw1ex A hyp_ncpwpw1_1
  have p0004 := @g_pwex (syn_cpw1 A) p0003
  have p0005 := @g_eqnc (syn_cpw (syn_cpw1 A)) (syn_cpw1 (syn_cpw A)) p0004
  have p0006 :=
    @g_mpbir (.classEq (syn_cnc (syn_cpw (syn_cpw1 A))) (syn_cnc (syn_cpw1 (syn_cpw A))))
      (syn_wbr (syn_cpw (syn_cpw1 A)) (syn_cen) (syn_cpw1 (syn_cpw A))) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_ncpw1c :
    Nominal.NPrf (.classEq (syn_cnc (syn_cpw (syn_c1c))) (syn_cnc (syn_c1c))) :=
  by
  have p0000 := @g_vvex
  have p0001 := @g_ncpwpw1 (syn_cvv) p0000
  have p0002 := @g_df1c2
  have p0003 := @g_pweqi (syn_c1c) (syn_cpw1 (syn_cvv)) p0002
  have p0004 := @g_nceqi (syn_cpw (syn_c1c)) (syn_cpw (syn_cpw1 (syn_cvv))) p0003
  have p0006 := @g_pwv
  have p0007 := @g_pw1eq (syn_cpw (syn_cvv)) (syn_cvv)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @g_eqtr4i (syn_c1c) (syn_cpw1 (syn_cvv)) (syn_cpw1 (syn_cpw (syn_cvv))) p0002 p0008
  have p0010 := @g_nceqi (syn_c1c) (syn_cpw1 (syn_cpw (syn_cvv))) p0009
  have p0011 :=
    @g_n_3eqtr4i (syn_cnc (syn_cpw (syn_cpw1 (syn_cvv))))
      (syn_cnc (syn_cpw1 (syn_cpw (syn_cvv)))) (syn_cnc (syn_cpw (syn_c1c)))
      (syn_cnc (syn_c1c)) p0001 p0004 p0010
  exact p0011

@[expose]
noncomputable def g_n_1p1e2c :
    Nominal.NPrf (.classEq (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c)) :=
  by
  have p0000 := @g_n_0ex
  have p0001 := @g_n0i (syn_cvv) (syn_c0)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_vvex
  have p0004 := @g_elsnc (syn_cvv) (syn_c0) p0003
  have p0005 :=
    @g_mtbir (.classMem (syn_cvv) (syn_csn (syn_c0))) (.classEq (syn_cvv) (syn_c0)) p0002
      p0004
  have p0006 := @g_disjsn (syn_csn (syn_c0)) (syn_cvv)
  have p0007 :=
    @g_mpbir (.classEq (syn_cin (syn_csn (syn_c0)) (syn_csn (syn_cvv))) (syn_c0))
      (.neg (.classMem (syn_cvv) (syn_csn (syn_c0)))) p0005 p0006
  have p0008 := @g_snex (syn_c0)
  have p0009 := @g_snex (syn_cvv)
  have p0010 := @g_ncdisjun (syn_csn (syn_c0)) (syn_csn (syn_cvv)) p0008 p0009
  have p0011 := Nominal.mp p0007 p0010
  have p0012 := (Nominal.classEqRefl (syn_c2c))
  have p0013 := (Nominal.classEqRefl (syn_cpr (syn_c0) (syn_cvv)))
  have p0014 :=
    @g_nceqi (syn_cpr (syn_c0) (syn_cvv)) (syn_cun (syn_csn (syn_c0)) (syn_csn (syn_cvv)))
      p0013
  have p0015 :=
    @g_eqtri (syn_c2c) (syn_cnc (syn_cpr (syn_c0) (syn_cvv)))
      (syn_cnc (syn_cun (syn_csn (syn_c0)) (syn_csn (syn_cvv)))) p0012 p0014
  have p0017 := @g_df1c3 (syn_c0) p0000
  have p0019 := @g_df1c3 (syn_cvv) p0003
  have p0020 :=
    @g_addceq12i (syn_c1c) (syn_cnc (syn_csn (syn_c0))) (syn_c1c)
      (syn_cnc (syn_csn (syn_cvv))) p0017 p0019
  have p0021 :=
    @g_n_3eqtr4ri (syn_cnc (syn_cun (syn_csn (syn_c0)) (syn_csn (syn_cvv))))
      (syn_cplc (syn_cnc (syn_csn (syn_c0))) (syn_cnc (syn_csn (syn_cvv)))) (syn_c2c)
      (syn_cplc (syn_c1c) (syn_c1c)) p0011 p0015 p0020
  exact p0021

@[expose]
noncomputable def g_tcex (A : Class) : Nominal.NPrf (.classMem (syn_ctc A) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc y A x
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @g_iotaex
      (syn_wa (.classMem (.cv x) (syn_cncs))
        (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))
      x
  have p0002 :=
    @g_eqeltri (syn_ctc A)
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cncs))
          (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))))
      (syn_cvv) p0000 p0001
  exact p0002


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part047`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_tceq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_ctc A) (syn_ctc B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classEq A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have p0000 :=
    @g_rexeq (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) y A B dv_cache_0001
      dv_cache_0002
  have p0001 :=
    @g_anbi2d (.classEq A B)
      (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))
      (syn_wrex y B (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))
      (.classMem (.cv x) (syn_cncs)) p0000
  have p0002 :=
    @g_iotabidv (.classEq A B)
      (syn_wa (.classMem (.cv x) (syn_cncs))
        (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))
      (syn_wa (.classMem (.cv x) (syn_cncs))
        (syn_wrex y B (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))
      x dv_cache_0003 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc y A x
      dv_cache_0004 dv_cache_0001 dv_cache_0005
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc y B x
      dv_cache_0006 dv_cache_0002 dv_cache_0005
  have p0005 :=
    @g_n_3eqtr4g (.classEq A B)
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cncs))
          (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))))
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cncs))
          (syn_wrex y B (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))))
      (syn_ctc A) (syn_ctc B) p0002 p0003 p0004
  exact p0005

@[expose]
noncomputable def g_ncspw1eu (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cncs)) (syn_wreu x (syn_cncs)
          (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_y, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((syn_cnc (syn_cpw1 (.cv y)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, dv_x_y,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 :
    x ∉ ((Wff.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_x_y, or_false, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Wff.classMem A (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, dv_A_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0008 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact (show x ≠ y from (by exact dv_x_y))
  have dv_cache_0009 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0010 : w ∉ ((Wff.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, or_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((Wff.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_w, or_false, not_false_eq_true])
  have dv_cache_0012 : y ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0013 : y ∉ ((Wff.objEq x z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, (Ne.symm dv_x_y), fresh_y_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0014 : w ∉ ((Wff.objEq x z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0015 :
    y ∉
      ((syn_wa (.classMem A (syn_cncs))
          (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, (Ne.symm dv_x_y), fresh_y_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    w ∉
      ((syn_wa (.classMem A (syn_cncs))
          (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_x, fresh_w_ne_z,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((Wff.classMem A (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, dv_A_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((Wff.classMem A (syn_cncs))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union,
          fresh_z_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0021 : w ∉ ((Wff.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y, or_false, not_false_eq_true])
  have dv_cache_0022 :
    z ∉ ((syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x,
          fresh_z_ne_y, or_false, and_false, not_false_eq_true])
  have dv_cache_0023 :
    x ∉ ((syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_w,
          or_false, and_false, not_false_eq_true])
  have p0000 := @g_nulnnc
  have p0001 := @g_eleq1 A (syn_c0) (syn_cncs)
  have p0002 :=
    @g_mtbiri (.classEq A (syn_c0)) (.classMem A (syn_cncs))
      (.classMem (syn_c0) (syn_cncs)) p0000 p0001
  have p0003 := @g_necon2ai (.classMem A (syn_cncs)) A (syn_c0) p0002
  have p0004 := @g_n0 y A dv_cache_0001
  have p0005 :=
    @g_sylib (.classMem A (syn_cncs)) (syn_wne A (syn_c0))
      (syn_wex y (.classMem (.cv y) A)) p0003 p0004
  have p0006 := @g_vex y
  have p0007 := @g_pw1ex (.cv y) p0006
  have p0008 := @g_ncelncsi (syn_cpw1 (.cv y)) p0007
  have p0009 := @g_eqid (syn_cnc (syn_cpw1 (.cv y)))
  have p0010 := @g_eqeq1 (.cv x) (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv y)))
  have p0011 :=
    @g_rspcev (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))
      (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv y)))) x
      (syn_cnc (syn_cpw1 (.cv y))) (syn_cncs) dv_cache_0002 dv_cache_0003 dv_cache_0004
      p0010
  have p0012 :=
    @g_mp2an (.classMem (syn_cnc (syn_cpw1 (.cv y))) (syn_cncs))
      (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv y))))
      (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) p0008 p0009
      p0011
  have p0013 :=
    @g_jctr (.classMem (.cv y) A)
      (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) p0012
  have p0014 :=
    @g_a1i
      (.imp (.classMem (.cv y) A) (syn_wa (.classMem (.cv y) A)
          (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))))
      (.classMem A (syn_cncs)) p0013
  have p0015 :=
    @g_eximdv (.classMem A (syn_cncs)) (.classMem (.cv y) A)
      (syn_wa (.classMem (.cv y) A)
        (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))
      y dv_cache_0005 p0014
  have p0016 :=
    @g_mpd (.classMem A (syn_cncs)) (syn_wex y (.classMem (.cv y) A))
      (syn_wex y (syn_wa (.classMem (.cv y) A)
          (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))))
      p0005 p0015
  have p0017 :=
    @g_rexcom (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))) x y (syn_cncs) A
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0018 :=
    (Nominal.biimpRefl (syn_wrex y A
        (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))))
  have p0019 :=
    @g_bitri
      (syn_wrex x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))
      (syn_wrex y A (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))
      (syn_wex y (syn_wa (.classMem (.cv y) A)
          (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))))
      p0017 p0018
  have p0020 :=
    @g_sylibr (.classMem A (syn_cncs))
      (syn_wex y (syn_wa (.classMem (.cv y) A)
          (syn_wrex x (syn_cncs) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))))
      (syn_wrex x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))
      p0016 p0019
  have p0021 :=
    @g_reeanv (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))
      (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))) y w A A dv_cache_0009 dv_cache_0001
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0022 := @g_ncseqnc A (.cv y)
  have p0023 :=
    @g_biimpar (.classMem A (syn_cncs)) (.classEq A (syn_cnc (.cv y)))
      (.classMem (.cv y) A) p0022
  have p0024 :=
    @g_adantrr (.classMem A (syn_cncs)) (.classMem (.cv y) A)
      (.classEq A (syn_cnc (.cv y))) (.classMem (.cv w) A) p0023
  have p0025 := @g_ncseqnc A (.cv w)
  have p0026 :=
    @g_biimpar (.classMem A (syn_cncs)) (.classEq A (syn_cnc (.cv w)))
      (.classMem (.cv w) A) p0025
  have p0027 :=
    @g_adantrl (.classMem A (syn_cncs)) (.classMem (.cv w) A)
      (.classEq A (syn_cnc (.cv w))) (.classMem (.cv y) A) p0026
  have p0028 :=
    @g_eqtr3d
      (syn_wa (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv y) A) (.classMem (.cv w) A)))
      A (syn_cnc (.cv y)) (syn_cnc (.cv w)) p0024 p0027
  have p0029 := @g_ncpw1 (.cv y) (.cv w) p0006
  have p0030 :=
    @g_sylib
      (syn_wa (.classMem A (syn_cncs)) (syn_wa (.classMem (.cv y) A) (.classMem (.cv w) A)))
      (.classEq (syn_cnc (.cv y)) (syn_cnc (.cv w)))
      (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w)))) p0028 p0029
  have p0031 :=
    @g_n_3adant2 (.classMem A (syn_cncs))
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv w) A))
      (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w))))
      (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs))) p0030
  have p0032 := @g_eqeq2 (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w))) (.cv x)
  have p0033 :=
    @g_anbi1d (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w))))
      (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))
      (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv w))))
      (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))) p0032
  have p0034 := @g_eqtr3 (.cv x) (.cv z) (syn_cnc (syn_cpw1 (.cv w)))
  have p0035_e01_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv w))))
          (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cnc syn_cec syn_cima syn_wrex syn_wex syn_wbr syn_cop syn_cun
          syn_cnin syn_wnan syn_ccompl syn_csn syn_cen syn_copab syn_cpw1 syn_cin syn_cpw
          syn_wss syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0034
  have p0035 :=
    @g_syl6bi (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w))))
      (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))
        (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))
      (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv w))))
        (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))
      (.objEq x z) p0033 p0035_e01_recanon
  have p0036 :=
    @g_syl
      (syn_w3a (.classMem A (syn_cncs))
        (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs)))
        (syn_wa (.classMem (.cv y) A) (.classMem (.cv w) A)))
      (.classEq (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w))))
      (.imp (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))
          (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) (.objEq x z))
      p0031 p0035
  have p0037 :=
    @g_n_3expa (.classMem A (syn_cncs))
      (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs)))
      (syn_wa (.classMem (.cv y) A) (.classMem (.cv w) A))
      (.imp (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))
          (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) (.objEq x z))
      p0036
  have p0038 :=
    @g_rexlimdvva
      (syn_wa (.classMem A (syn_cncs))
        (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs))))
      (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))
        (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))
      (.objEq x z) y w A A dv_cache_0009 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0012 p0037
  have p0039 :=
    @g_syl5bir
      (syn_wa (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))
        (syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))))
      (syn_wrex y A (syn_wrex w A (syn_wa (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))
            (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))))
      (syn_wa (.classMem A (syn_cncs))
        (syn_wa (.classMem (.cv x) (syn_cncs)) (.classMem (.cv z) (syn_cncs))))
      (.objEq x z) p0021 p0038
  have p0040 :=
    @g_ralrimivva (.classMem A (syn_cncs))
      (.imp (syn_wa (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))
          (syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))) (.objEq x z))
      x z (syn_cncs) (syn_cncs) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      p0039
  have p0041 := @g_eqeq1 (.cv x) (.cv z) (syn_cnc (syn_cpw1 (.cv y)))
  have p0042_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (syn_wb (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))
          (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cnc syn_cec syn_cima syn_wrex syn_wex syn_wa syn_wbr syn_cop
          syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cen syn_copab syn_cpw1 syn_cin
          syn_cpw syn_wss syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0041
  have p0042 :=
    @g_rexbidv (.objEq x z) (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))
      (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv y)))) y A dv_cache_0013 p0042_e00_recanon
  have p0043 := @g_pw1eq (.cv y) (.cv w)
  have p0044_e00_recanon :
    Nominal.NPrf (.imp (.objEq y w) (.classEq (syn_cpw1 (.cv y)) (syn_cpw1 (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss
          syn_c1c syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0043
  have p0044 :=
    @g_nceqd (.objEq y w) (syn_cpw1 (.cv y)) (syn_cpw1 (.cv w)) p0044_e00_recanon
  have p0045 :=
    @g_eqeq2d (.objEq y w) (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 (.cv w)))
      (.cv z) p0044
  have p0046 :=
    @g_cbvrexv (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv y))))
      (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))) y w A dv_cache_0001 dv_cache_0009
      dv_cache_0021 dv_cache_0011 p0045
  have p0047 :=
    @g_syl6bb (.objEq x z) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))
      (syn_wrex y A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv y)))))
      (syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) p0042 p0046
  have p0048 :=
    @g_reu4 (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))
      (syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w))))) x z (syn_cncs)
      dv_cache_0003 dv_cache_0017 dv_cache_0022 dv_cache_0023 dv_cache_0020 p0047
  have p0049 :=
    @g_sylanbrc (.classMem A (syn_cncs))
      (syn_wrex x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))
      (syn_wral x (syn_cncs) (syn_wral z (syn_cncs) (.imp
            (syn_wa (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))
              (syn_wrex w A (.classEq (.cv z) (syn_cnc (syn_cpw1 (.cv w)))))) (.objEq x z))))
      (syn_wreu x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))
      p0020 p0040 p0048
  exact p0049

@[expose]
noncomputable def g_tccl (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cncs)) (.classMem (syn_ctc A) (syn_cncs))) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0004 : x ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc y A x
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_ncspw1eu x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @g_reiotacl (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))) x
      (syn_cncs) dv_cache_0004
  have p0003 :=
    @g_syl (.classMem A (syn_cncs))
      (syn_wreu x (syn_cncs) (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))
      (.classMem (syn_cio x (syn_wa (.classMem (.cv x) (syn_cncs))
            (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y))))))) (syn_cncs))
      p0001 p0002
  have p0004 :=
    @g_syl5eqel (.classMem A (syn_cncs)) (syn_ctc A)
      (syn_cio x (syn_wa (.classMem (.cv x) (syn_cncs))
          (syn_wrex y A (.classEq (.cv x) (syn_cnc (syn_cpw1 (.cv y)))))))
      (syn_cncs) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_eqtc (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cncs)) (syn_wb (.classEq (syn_ctc A) B)
          (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ ((Wff.classMem B (syn_cncs))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs, Finset.mem_union, dv_B_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_A_x, not_false_eq_true])
  have dv_cache_0004 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0005 : x ∉ ((Wff.classEq (.cv y) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, dv_B_x, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cncs)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncs,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0008 :
    y ∉ ((syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_not_B, fresh_y_ne_x, or_false,
          and_false, not_false_eq_true])
  have p0000 := @g_simpr (.classMem A (syn_cncs)) (.classEq (syn_ctc A) B)
  have p0001 := @g_tccl A
  have p0002 :=
    @g_adantr (.classMem A (syn_cncs)) (.classMem (syn_ctc A) (syn_cncs))
      (.classEq (syn_ctc A) B) p0001
  have p0003 :=
    @g_eqeltrrd (syn_wa (.classMem A (syn_cncs)) (.classEq (syn_ctc A) B)) (syn_ctc A) B
      (syn_cncs) p0000 p0002
  have p0004 :=
    @g_ex (.classMem A (syn_cncs)) (.classEq (syn_ctc A) B) (.classMem B (syn_cncs)) p0003
  have p0005 := @g_vex x
  have p0006 := @g_pw1ex (.cv x) p0005
  have p0007 := @g_ncelncsi (syn_cpw1 (.cv x)) p0006
  have p0008 := @g_eleq1 B (syn_cnc (syn_cpw1 (.cv x))) (syn_cncs)
  have p0009 :=
    @g_mpbiri (.classEq B (syn_cnc (syn_cpw1 (.cv x)))) (.classMem B (syn_cncs))
      (.classMem (syn_cnc (syn_cpw1 (.cv x))) (syn_cncs)) p0007 p0008
  have p0010 :=
    @g_rexlimivw (.classEq B (syn_cnc (syn_cpw1 (.cv x)))) (.classMem B (syn_cncs)) x A
      dv_cache_0001 p0009
  have p0011 :=
    @g_a1i
      (.imp (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))) (.classMem B (syn_cncs)))
      (.classMem A (syn_cncs)) p0010
  have p0012 := @g_ncspw1eu y x A dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0013 := @g_eqeq1 (.cv y) B (syn_cnc (syn_cpw1 (.cv x)))
  have p0014 :=
    @g_rexbidv (.classEq (.cv y) B) (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x))))
      (.classEq B (syn_cnc (syn_cpw1 (.cv x)))) x A dv_cache_0005 p0013
  have p0015 :=
    @g_reiota2 (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x)))))
      (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))) y (syn_cncs) B
      dv_cache_0006 dv_cache_0007 dv_cache_0008 p0014
  have p0016 :=
    @g_sylan2 (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
      (syn_wreu y (syn_cncs) (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x))))))
      (syn_wb (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))) (.classEq (syn_cio y
            (syn_wa (.classMem (.cv y) (syn_cncs))
              (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x))))))) B))
      p0012 p0015
  have p0017 :=
    @g_ancoms (.classMem B (syn_cncs)) (.classMem A (syn_cncs))
      (syn_wb (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))) (.classEq (syn_cio y
            (syn_wa (.classMem (.cv y) (syn_cncs))
              (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x))))))) B))
      p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_tc x A y
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0019 :=
    @g_eqeq1i (syn_ctc A)
      (syn_cio y (syn_wa (.classMem (.cv y) (syn_cncs))
          (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x)))))))
      B p0018
  have p0020 :=
    @g_syl6rbbr (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x)))))
      (.classEq (syn_cio y (syn_wa (.classMem (.cv y) (syn_cncs))
            (syn_wrex x A (.classEq (.cv y) (syn_cnc (syn_cpw1 (.cv x))))))) B)
      (.classEq (syn_ctc A) B) p0017 p0019
  have p0021 :=
    @g_ex (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
      (syn_wb (.classEq (syn_ctc A) B) (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x))))))
      p0020
  have p0022 :=
    @g_pm5_21ndd (.classMem A (syn_cncs)) (.classMem B (syn_cncs))
      (.classEq (syn_ctc A) B) (syn_wrex x A (.classEq B (syn_cnc (syn_cpw1 (.cv x)))))
      p0004 p0011 p0021
  exact p0022

@[expose]
noncomputable def g_pw1eltc (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B A))
        (.classMem (syn_cpw1 B) (syn_ctc A))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let y : Var := freshVar proofSupport 0
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have dv_cache_0001 : y ∉ (B).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 :
    y ∉ ((Wff.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0004 : y ∉ ((syn_cnc (syn_cpw1 B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_y_not_B,
          not_false_eq_true])
  have p0000 := @g_pw1exg B A
  have p0001 := @g_ncidg (syn_cpw1 B) (syn_cvv)
  have p0002 :=
    @g_syl (.classMem B A) (.classMem (syn_cpw1 B) (syn_cvv))
      (.classMem (syn_cpw1 B) (syn_cnc (syn_cpw1 B))) p0000 p0001
  have p0003 :=
    @g_adantl (.classMem B A) (.classMem (syn_cpw1 B) (syn_cnc (syn_cpw1 B)))
      (.classMem A (syn_cncs)) p0002
  have p0004 := @g_eqid (syn_cnc (syn_cpw1 B))
  have p0005 := @g_pw1eq (.cv y) B
  have p0006 := @g_nceqd (.classEq (.cv y) B) (syn_cpw1 (.cv y)) (syn_cpw1 B) p0005
  have p0007 :=
    @g_eqeq2d (.classEq (.cv y) B) (syn_cnc (syn_cpw1 (.cv y))) (syn_cnc (syn_cpw1 B))
      (syn_cnc (syn_cpw1 B)) p0006
  have p0008 :=
    @g_rspcev (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 (.cv y))))
      (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 B))) y B A dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0007
  have p0009 :=
    @g_mpan2 (.classMem B A) (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 B)))
      (syn_wrex y A (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 (.cv y))))) p0004
      p0008
  have p0010 :=
    @g_adantl (.classMem B A)
      (syn_wrex y A (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 (.cv y)))))
      (.classMem A (syn_cncs)) p0009
  have p0011 := @g_eqtc y A (syn_cnc (syn_cpw1 B)) dv_cache_0002 dv_cache_0004
  have p0012 :=
    @g_adantr (.classMem A (syn_cncs))
      (syn_wb (.classEq (syn_ctc A) (syn_cnc (syn_cpw1 B)))
        (syn_wrex y A (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 (.cv y))))))
      (.classMem B A) p0011
  have p0013 :=
    @g_mpbird (syn_wa (.classMem A (syn_cncs)) (.classMem B A))
      (.classEq (syn_ctc A) (syn_cnc (syn_cpw1 B)))
      (syn_wrex y A (.classEq (syn_cnc (syn_cpw1 B)) (syn_cnc (syn_cpw1 (.cv y))))) p0010
      p0012
  have p0014 :=
    @g_eleqtrrd (syn_wa (.classMem A (syn_cncs)) (.classMem B A)) (syn_cpw1 B)
      (syn_cnc (syn_cpw1 B)) (syn_ctc A) p0003 p0013
  exact p0014

@[expose]
noncomputable def g_tc0c : Nominal.NPrf (.classEq (syn_ctc (syn_c0c)) (syn_c0c)) :=
  by
  have p0000 := @g_n_0cnc
  have p0001 := @g_tccl (syn_c0c)
  have p0002 := Nominal.mp p0000 p0001
  have p0004 := @g_pw10
  have p0006 := @g_nulel0c
  have p0007 := @g_pw1eltc (syn_c0c) (syn_c0)
  have p0008 :=
    @g_mp2an (.classMem (syn_c0c) (syn_cncs)) (.classMem (syn_c0) (syn_c0c))
      (.classMem (syn_cpw1 (syn_c0)) (syn_ctc (syn_c0c))) p0000 p0006 p0007
  have p0009 := @g_eqeltrri (syn_cpw1 (syn_c0)) (syn_c0) (syn_ctc (syn_c0c)) p0004 p0008
  have p0011 := @g_nceleq (syn_ctc (syn_c0c)) (syn_c0c) (syn_c0)
  have p0012 :=
    @g_mp4an (.classMem (syn_ctc (syn_c0c)) (syn_cncs)) (.classMem (syn_c0c) (syn_cncs))
      (.classMem (syn_c0) (syn_ctc (syn_c0c))) (.classMem (syn_c0) (syn_c0c))
      (.classEq (syn_ctc (syn_c0c)) (syn_c0c)) p0002 p0000 p0009 p0006 p0011
  exact p0012


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part048`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_tcdi (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
        (.classEq (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B)))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Wff.classEq A (syn_cnc (.cv x)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_not_A, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Wff.classEq B (syn_cnc (.cv y)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 :
    x ∉ ((Wff.classEq (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          fresh_x_not_A, fresh_x_not_B, or_false, not_false_eq_true])
  have dv_cache_0006 :
    y ∉ ((Wff.classEq (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have p0000 :=
    @g_eeanv (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))) x y
      dv_cache_0001 dv_cache_0002
  have p0001 := @g_vex x
  have p0002 := @g_n_0ex
  have p0003 := @g_complex (syn_c0) p0002
  have p0004 := @g_xpsnen (.cv x) (syn_ccompl (syn_c0)) p0001 p0003
  have p0005 := @g_snex (syn_ccompl (syn_c0))
  have p0006 := @g_xpex (.cv x) (syn_csn (syn_ccompl (syn_c0))) p0001 p0005
  have p0007 := @g_eqnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (.cv x) p0006
  have p0008 :=
    @g_mpbir
      (.classEq (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cnc (.cv x)))
      (syn_wbr (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) (syn_cen) (.cv x)) p0004
      p0007
  have p0009 :=
    @g_eqeq2i (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
      (syn_cnc (.cv x)) A p0008
  have p0010 := @g_vex y
  have p0012 := @g_xpsnen (.cv y) (syn_c0) p0010 p0002
  have p0013 := @g_snex (syn_c0)
  have p0014 := @g_xpex (.cv y) (syn_csn (syn_c0)) p0010 p0013
  have p0015 := @g_eqnc (syn_cxp (.cv y) (syn_csn (syn_c0))) (.cv y) p0014
  have p0016 :=
    @g_mpbir (.classEq (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cnc (.cv y)))
      (syn_wbr (syn_cxp (.cv y) (syn_csn (syn_c0))) (syn_cen) (.cv y)) p0012 p0015
  have p0017 :=
    @g_eqeq2i (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cnc (.cv y)) B p0016
  have p0018 :=
    @g_anbi12i (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
      (.classEq A (syn_cnc (.cv x)))
      (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (.classEq B (syn_cnc (.cv y))) p0009 p0017
  have p0019 :=
    @g_n_2exbii
      (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
        (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y)))) x y p0018
  have p0020 := @g_elncs x A dv_cache_0003
  have p0021 := @g_elncs y B dv_cache_0004
  have p0022 :=
    @g_anbi12i (.classMem A (syn_cncs)) (syn_wex x (.classEq A (syn_cnc (.cv x))))
      (.classMem B (syn_cncs)) (syn_wex y (.classEq B (syn_cnc (.cv y)))) p0020 p0021
  have p0023 :=
    @g_n_3bitr4ri
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cnc (.cv x))) (.classEq B (syn_cnc (.cv y))))))
      (syn_wa (syn_wex x (.classEq A (syn_cnc (.cv x))))
        (syn_wex y (.classEq B (syn_cnc (.cv y)))))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
            (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))))
      (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs))) p0000 p0019 p0022
  have p0024 := @g_ncelncsi (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) p0006
  have p0025 := @g_ncelncsi (syn_cxp (.cv y) (syn_csn (syn_c0))) p0014
  have p0026 :=
    @g_ncaddccl (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
      (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0027 :=
    @g_mp2an
      (.classMem (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cncs))
      (.classMem (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cncs))
      (.classMem (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cncs))
      p0024 p0025 p0026
  have p0028 :=
    @g_tccl
      (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
  have p0029 := Nominal.mp p0027 p0028
  have p0030 := @g_tccl (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
  have p0031 := Nominal.mp p0024 p0030
  have p0032 := @g_tccl (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0033 := Nominal.mp p0025 p0032
  have p0034 :=
    @g_ncaddccl (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
      (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
  have p0035 :=
    @g_mp2an
      (.classMem (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
        (syn_cncs))
      (.classMem (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cncs))
      (.classMem (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
          (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cncs))
      p0031 p0033 p0034
  have p0036 := @g_ncid (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))) p0006
  have p0037 := @g_ncid (syn_cxp (.cv y) (syn_csn (syn_c0))) p0014
  have p0038 := @g_necompl (syn_c0)
  have p0039 := @g_xpnedisj (.cv x) (.cv y) (syn_ccompl (syn_c0)) (syn_c0) p0003 p0038
  have p0040 :=
    @g_eladdci (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
      (syn_cxp (.cv y) (syn_csn (syn_c0)))
      (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
      (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0041 :=
    @g_mp3an
      (.classMem (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
        (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
      (.classMem (syn_cxp (.cv y) (syn_csn (syn_c0)))
        (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (.classEq (syn_cin (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
          (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_c0))
      (.classMem (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
          (syn_cxp (.cv y) (syn_csn (syn_c0))))
        (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      p0036 p0037 p0039 p0040
  have p0042 :=
    @g_pw1eltc
      (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
        (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0043 :=
    @g_mp2an
      (.classMem (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_cncs))
      (.classMem (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
          (syn_cxp (.cv y) (syn_csn (syn_c0))))
        (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (.classMem (syn_cpw1 (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
            (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_ctc
          (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
            (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))))
      p0027 p0041 p0042
  have p0044 :=
    @g_pw1un (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
      (syn_cxp (.cv y) (syn_csn (syn_c0)))
  have p0045 :=
    @g_pw1eltc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
      (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
  have p0046 :=
    @g_mp2an
      (.classMem (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))) (syn_cncs))
      (.classMem (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
        (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
      (.classMem (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))))
      p0024 p0036 p0045
  have p0047 :=
    @g_pw1eltc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
      (syn_cxp (.cv y) (syn_csn (syn_c0)))
  have p0048 :=
    @g_mp2an (.classMem (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))) (syn_cncs))
      (.classMem (syn_cxp (.cv y) (syn_csn (syn_c0)))
        (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (.classMem (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0))))
        (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      p0025 p0037 p0047
  have p0049 :=
    @g_pw1eq
      (syn_cin (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
        (syn_cxp (.cv y) (syn_csn (syn_c0))))
      (syn_c0)
  have p0050 := Nominal.mp p0039 p0049
  have p0051 :=
    @g_pw1in (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
      (syn_cxp (.cv y) (syn_csn (syn_c0)))
  have p0052 := @g_pw10
  have p0053 :=
    @g_n_3eqtr3i
      (syn_cpw1 (syn_cin (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
          (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (syn_cpw1 (syn_c0))
      (syn_cin (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (syn_c0) p0050 p0051 p0052
  have p0054 :=
    @g_eladdci (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
      (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0))))
      (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
      (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
  have p0055 :=
    @g_mp3an
      (.classMem (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))))
      (.classMem (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0))))
        (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (.classEq (syn_cin (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_c0))
      (.classMem (syn_cun (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0)))))
        (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
          (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))))
      p0046 p0048 p0053 p0054
  have p0056 :=
    @g_eqeltri
      (syn_cpw1 (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
          (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (syn_cun (syn_cpw1 (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_cpw1 (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
        (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      p0044 p0055
  have p0057 :=
    @g_nceleq
      (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
        (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (syn_cpw1 (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
          (syn_cxp (.cv y) (syn_csn (syn_c0)))))
  have p0058 :=
    @g_mp4an
      (.classMem (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
            (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cncs))
      (.classMem (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
          (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))) (syn_cncs))
      (.classMem (syn_cpw1 (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
            (syn_cxp (.cv y) (syn_csn (syn_c0))))) (syn_ctc
          (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
            (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))))
      (.classMem (syn_cpw1 (syn_cun (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))
            (syn_cxp (.cv y) (syn_csn (syn_c0)))))
        (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
          (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))))
      (.classEq (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
            (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
        (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
          (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))))
      p0029 p0035 p0043 p0056 p0057
  have p0059 :=
    @g_addceq12 A B (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
      (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0060 :=
    @g_tceq (syn_cplc A B)
      (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
        (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
  have p0061 :=
    @g_syl
      (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
        (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (.classEq (syn_cplc A B)
        (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (.classEq (syn_ctc (syn_cplc A B)) (syn_ctc
          (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
            (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))))
      p0059 p0060
  have p0062 := @g_tceq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
  have p0063 :=
    @g_adantr (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
      (.classEq (syn_ctc A)
        (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))))
      (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) p0062
  have p0064 := @g_tceq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))
  have p0065 :=
    @g_adantl (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0)))))
      (.classEq (syn_ctc B) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))) p0064
  have p0066 :=
    @g_addceq12d
      (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
        (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (syn_ctc A) (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
      (syn_ctc B) (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))) p0063 p0065
  have p0067 :=
    @g_n_3eqtr4a
      (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
        (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (syn_ctc (syn_cplc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0)))))
          (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (syn_cplc (syn_ctc (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
        (syn_ctc (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B)) p0058 p0061 p0066
  have p0068 :=
    @g_exlimivv
      (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
        (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))
      (.classEq (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B))) x y
      dv_cache_0005 dv_cache_0006 p0067
  have p0069 :=
    @g_sylbi (syn_wa (.classMem A (syn_cncs)) (.classMem B (syn_cncs)))
      (syn_wex x (syn_wex y
          (syn_wa (.classEq A (syn_cnc (syn_cxp (.cv x) (syn_csn (syn_ccompl (syn_c0))))))
            (.classEq B (syn_cnc (syn_cxp (.cv y) (syn_csn (syn_c0))))))))
      (.classEq (syn_ctc (syn_cplc A B)) (syn_cplc (syn_ctc A) (syn_ctc B))) p0023 p0068
  exact p0069

@[expose]
noncomputable def g_tc1c : Nominal.NPrf (.classEq (syn_ctc (syn_c1c)) (syn_c1c)) :=
  by
  have p0000 := @g_n_1cnc
  have p0001 := @g_tccl (syn_c1c)
  have p0002 := Nominal.mp p0000 p0001
  have p0004 := @g_n_0ex
  have p0005 := @g_pw1sn (syn_c0) p0004
  have p0008 := @g_snel1c (syn_c0) p0004
  have p0009 := @g_pw1eltc (syn_c1c) (syn_csn (syn_c0))
  have p0010 :=
    @g_mp2an (.classMem (syn_c1c) (syn_cncs)) (.classMem (syn_csn (syn_c0)) (syn_c1c))
      (.classMem (syn_cpw1 (syn_csn (syn_c0))) (syn_ctc (syn_c1c))) p0000 p0008 p0009
  have p0011 :=
    @g_eqeltrri (syn_cpw1 (syn_csn (syn_c0))) (syn_csn (syn_csn (syn_c0)))
      (syn_ctc (syn_c1c)) p0005 p0010
  have p0012 := @g_snex (syn_c0)
  have p0013 := @g_snel1c (syn_csn (syn_c0)) p0012
  have p0014 := @g_nceleq (syn_ctc (syn_c1c)) (syn_c1c) (syn_csn (syn_csn (syn_c0)))
  have p0015 :=
    @g_mp4an (.classMem (syn_ctc (syn_c1c)) (syn_cncs)) (.classMem (syn_c1c) (syn_cncs))
      (.classMem (syn_csn (syn_csn (syn_c0))) (syn_ctc (syn_c1c)))
      (.classMem (syn_csn (syn_csn (syn_c0))) (syn_c1c))
      (.classEq (syn_ctc (syn_c1c)) (syn_c1c)) p0002 p0000 p0011 p0013 p0014
  exact p0015

@[expose]
noncomputable def g_n_2nnc : Nominal.NPrf (.classMem (syn_c2c) (syn_cnnc)) :=
  by
  have p0000 := @g_n_1p1e2c
  have p0001 := @g_n_1cnnc
  have p0002 := @g_peano2 (syn_c1c)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @g_eqeltrri (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c) (syn_cnnc) p0000 p0003
  exact p0004

@[expose]
noncomputable def g_pw1fin (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cfin)) (.classMem (syn_cpw1 A) (syn_cfin))) :=
  by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (h)
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : m ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_m_not_A, not_false_eq_true])
  have dv_cache_0002 :
    n ∉
      ((syn_wrex m (syn_cnnc) (syn_wa (.classMem (syn_cpw1 A) (.cv m))
            (.classMem (syn_cpw1 A) (.cv m))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_n_not_A, fresh_n_ne_m, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_A, not_false_eq_true])
  have dv_cache_0004 : m ∉ ((syn_cpw1 A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, fresh_m_not_A,
          not_false_eq_true])
  have p0000 := @g_ncfinraise A A m (.cv n) dv_cache_0001 dv_cache_0001
  have p0001 :=
    @g_n_3anidm23 (.classMem (.cv n) (syn_cnnc)) (.classMem A (.cv n))
      (syn_wrex m (syn_cnnc)
        (syn_wa (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m))))
      p0000
  have p0002 :=
    @g_rexlimiva (.classMem A (.cv n))
      (syn_wrex m (syn_cnnc)
        (syn_wa (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m))))
      n (syn_cnnc) dv_cache_0002 p0001
  have p0003 := @g_simpl (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m))
  have p0004 :=
    @g_reximi (syn_wa (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m)))
      (.classMem (syn_cpw1 A) (.cv m)) m (syn_cnnc) p0003
  have p0005 :=
    @g_syl (syn_wrex n (syn_cnnc) (.classMem A (.cv n)))
      (syn_wrex m (syn_cnnc)
        (syn_wa (.classMem (syn_cpw1 A) (.cv m)) (.classMem (syn_cpw1 A) (.cv m))))
      (syn_wrex m (syn_cnnc) (.classMem (syn_cpw1 A) (.cv m))) p0002 p0004
  have p0006 := @g_elfin n A dv_cache_0003
  have p0007 := @g_elfin m (syn_cpw1 A) dv_cache_0004
  have p0008 :=
    @g_n_3imtr4i (syn_wrex n (syn_cnnc) (.classMem A (.cv n)))
      (syn_wrex m (syn_cnnc) (.classMem (syn_cpw1 A) (.cv m))) (.classMem A (syn_cfin))
      (.classMem (syn_cpw1 A) (syn_cfin)) p0005 p0006 p0007
  exact p0008

@[expose]
noncomputable def g_nntccl (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cnnc)) (.classMem (syn_ctc A) (syn_cnnc))) :=
  by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  let m : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have fresh_m : m ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_m_not_A : m ∉ A.fv := by
    intro h
    exact fresh_m (h)
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (h)
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_n_ne_a : n ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_a_ne_n : a ≠ n := Ne.symm fresh_n_ne_a
  have dv_cache_0001 : n ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_A, not_false_eq_true])
  have dv_cache_0002 : a ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((Wff.classMem (.cv n) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_n, fresh_a_not_A, or_false, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_n, not_false_eq_true])
  have dv_cache_0006 : m ∉ ((syn_cpw1 (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_m_ne_n,
          not_false_eq_true])
  have dv_cache_0007 : m ∉ ((Wff.classMem (syn_ctc A) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_m_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : m ∉ ((syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_not_A, fresh_m_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((Wff.classMem (syn_ctc A) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_n_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : n ∉ ((Wff.classMem A (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_n_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_nulnnn
  have p0001 := @g_eleq1 A (syn_c0) (syn_cnnc)
  have p0002 :=
    @g_mtbiri (.classEq A (syn_c0)) (.classMem A (syn_cnnc))
      (.classMem (syn_c0) (syn_cnnc)) p0000 p0001
  have p0003 := @g_necon2ai (.classMem A (syn_cnnc)) A (syn_c0) p0002
  have p0004 := @g_n0 n A dv_cache_0001
  have p0005 :=
    @g_sylib (.classMem A (syn_cnnc)) (syn_wne A (syn_c0))
      (syn_wex n (.classMem (.cv n) A)) p0003 p0004
  have p0006 := @g_eleq2 (.cv a) A (.cv n)
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) A) (syn_wb (.objMem n a) (.classMem (.cv n) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
      p0006
  have p0007 :=
    @g_rspcev (.objMem n a) (.classMem (.cv n) A) a A (syn_cnnc) dv_cache_0002
      dv_cache_0003 dv_cache_0004 p0007_e00_recanon
  have p0008 := @g_elfin a (.cv n) dv_cache_0005
  have p0009_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv n) (syn_cfin)) (syn_wrex a (syn_cnnc) (.objMem n a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cfin syn_cuni syn_wex syn_wa syn_cnnc syn_cint syn_wrex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0008
  have p0009 :=
    @g_sylibr (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A))
      (syn_wrex a (syn_cnnc) (.objMem n a)) (.classMem (.cv n) (syn_cfin)) p0007
      p0009_e01_recanon
  have p0010 := @g_pw1fin (.cv n)
  have p0011 :=
    @g_syl (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A))
      (.classMem (.cv n) (syn_cfin)) (.classMem (syn_cpw1 (.cv n)) (syn_cfin)) p0009 p0010
  have p0012 := @g_elfin m (syn_cpw1 (.cv n)) dv_cache_0006
  have p0013 :=
    @g_sylib (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A))
      (.classMem (syn_cpw1 (.cv n)) (syn_cfin))
      (syn_wrex m (syn_cnnc) (.classMem (syn_cpw1 (.cv n)) (.cv m))) p0011 p0012
  have p0014 := @g_nnnc A
  have p0015 := @g_tccl A
  have p0016 :=
    @g_syl (.classMem A (syn_cnnc)) (.classMem A (syn_cncs))
      (.classMem (syn_ctc A) (syn_cncs)) p0014 p0015
  have p0017 :=
    @g_ad2antrr (.classMem A (syn_cnnc)) (.classMem (syn_ctc A) (syn_cncs))
      (.classMem (.cv m) (syn_cnnc))
      (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))) p0016
  have p0018 := @g_nnnc (.cv m)
  have p0019 :=
    @g_ad2antlr (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv m) (syn_cncs))
      (.classMem A (syn_cnnc))
      (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))) p0018
  have p0020 :=
    @g_ad2antrr (.classMem A (syn_cnnc)) (.classMem A (syn_cncs))
      (.classMem (.cv m) (syn_cnnc))
      (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))) p0014
  have p0021 :=
    @g_simprl (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)))
      (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))
  have p0022 := @g_pw1eltc A (.cv n)
  have p0023 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)))
        (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))))
      (.classMem A (syn_cncs)) (.classMem (.cv n) A)
      (.classMem (syn_cpw1 (.cv n)) (syn_ctc A)) p0020 p0021 p0022
  have p0024 :=
    @g_simprr (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)))
      (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))
  have p0025 := @g_nceleq (syn_ctc A) (.cv m) (syn_cpw1 (.cv n))
  have p0026 :=
    @g_syl22anc
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)))
        (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))))
      (.classMem (syn_ctc A) (syn_cncs)) (.classMem (.cv m) (syn_cncs))
      (.classMem (syn_cpw1 (.cv n)) (syn_ctc A)) (.classMem (syn_cpw1 (.cv n)) (.cv m))
      (.classEq (syn_ctc A) (.cv m)) p0017 p0019 p0023 p0024 p0025
  have p0027 :=
    @g_simplr (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc))
      (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m)))
  have p0028 :=
    @g_eqeltrd
      (syn_wa (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)))
        (syn_wa (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))))
      (syn_ctc A) (.cv m) (syn_cnnc) p0026 p0027
  have p0029 :=
    @g_expr (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)))
      (.classMem (.cv n) A) (.classMem (syn_cpw1 (.cv n)) (.cv m))
      (.classMem (syn_ctc A) (syn_cnnc)) p0028
  have p0030 :=
    @g_an32s (.classMem A (syn_cnnc)) (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv n) A)
      (.imp (.classMem (syn_cpw1 (.cv n)) (.cv m)) (.classMem (syn_ctc A) (syn_cnnc)))
      p0029
  have p0031 :=
    @g_rexlimdva (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A))
      (.classMem (syn_cpw1 (.cv n)) (.cv m)) (.classMem (syn_ctc A) (syn_cnnc)) m
      (syn_cnnc) dv_cache_0007 dv_cache_0008 p0030
  have p0032 :=
    @g_mpd (syn_wa (.classMem A (syn_cnnc)) (.classMem (.cv n) A))
      (syn_wrex m (syn_cnnc) (.classMem (syn_cpw1 (.cv n)) (.cv m)))
      (.classMem (syn_ctc A) (syn_cnnc)) p0013 p0031
  have p0033 :=
    @g_ex (.classMem A (syn_cnnc)) (.classMem (.cv n) A)
      (.classMem (syn_ctc A) (syn_cnnc)) p0032
  have p0034 :=
    @g_exlimdv (.classMem A (syn_cnnc)) (.classMem (.cv n) A)
      (.classMem (syn_ctc A) (syn_cnnc)) n dv_cache_0009 dv_cache_0010 p0033
  have p0035 :=
    @g_mpd (.classMem A (syn_cnnc)) (syn_wex n (.classMem (.cv n) A))
      (.classMem (syn_ctc A) (syn_cnnc)) p0005 p0034
  exact p0035

@[expose]
noncomputable def g_nclec (A : Class) (B : Class)
    (hyp_nclec_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_nclec_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf (.imp (syn_wss A B) (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_cnc A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_x_not_B,
          not_false_eq_true])
  have dv_cache_0006 : y ∉ ((syn_cnc B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_y_not_B,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((syn_wss A (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_wss A B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0009 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_ncid A hyp_nclec_1
  have p0001 := @g_ncid B hyp_nclec_2
  have p0002 := @g_sseq1 (.cv x) A (.cv y)
  have p0003 := @g_sseq2 (.cv y) B A
  have p0004 :=
    @g_rspc2ev (syn_wss (.cv x) (.cv y)) (syn_wss A B) (syn_wss A (.cv y)) x y A B
      (syn_cnc A) (syn_cnc B) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0002 p0003
  have p0005 :=
    @g_mp3an12 (.classMem A (syn_cnc A)) (.classMem B (syn_cnc B)) (syn_wss A B)
      (syn_wrex x (syn_cnc A) (syn_wrex y (syn_cnc B) (syn_wss (.cv x) (.cv y)))) p0000
      p0001 p0004
  have p0006 := @g_ncex A
  have p0007 := @g_ncex B
  have p0008 :=
    @g_brlec x y (syn_cnc A) (syn_cnc B) dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0009 p0006 p0007
  have p0009 :=
    @g_sylibr (syn_wss A B)
      (syn_wrex x (syn_cnc A) (syn_wrex y (syn_cnc B) (syn_wss (.cv x) (.cv y))))
      (syn_wbr (syn_cnc A) (syn_clec) (syn_cnc B)) p0005 p0008
  exact p0009

@[expose]
noncomputable def g_lecidg (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A V) (syn_wne A (syn_c0))) (syn_wbr A (syn_clec) A)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ V.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0002 : y ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((syn_wss (.cv x) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wss,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @g_ssid (.cv x)
  have p0001 := @g_sseq2 (.cv y) (.cv x) (.cv x)
  have p0002 :=
    @g_rspcev (syn_wss (.cv x) (.cv y)) (syn_wss (.cv x) (.cv x)) y (.cv x) A
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @g_mpan2 (.classMem (.cv x) A) (syn_wss (.cv x) (.cv x))
      (syn_wrex y A (syn_wss (.cv x) (.cv y))) p0000 p0002
  have p0004 :=
    @g_ancli (.classMem (.cv x) A) (syn_wrex y A (syn_wss (.cv x) (.cv y))) p0003
  have p0005 :=
    @g_eximi (.classMem (.cv x) A)
      (syn_wa (.classMem (.cv x) A) (syn_wrex y A (syn_wss (.cv x) (.cv y)))) x p0004
  have p0006 := @g_n0 x A dv_cache_0004
  have p0007 :=
    (Nominal.biimpRefl (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y)))))
  have p0008 :=
    @g_n_3imtr4i (syn_wex x (.classMem (.cv x) A))
      (syn_wex x (syn_wa (.classMem (.cv x) A) (syn_wrex y A (syn_wss (.cv x) (.cv y)))))
      (syn_wne A (syn_c0)) (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y)))) p0005
      p0006 p0007
  have p0009 :=
    @g_adantl (syn_wne A (syn_c0)) (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y))))
      (.classMem A V) p0008
  have p0010 :=
    @g_brlecg x y A A V V dv_cache_0004 dv_cache_0004 dv_cache_0002 dv_cache_0005
  have p0011 :=
    @g_anidms (.classMem A V)
      (syn_wb (syn_wbr A (syn_clec) A) (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y)))))
      p0010
  have p0012 :=
    @g_adantr (.classMem A V)
      (syn_wb (syn_wbr A (syn_clec) A) (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y)))))
      (syn_wne A (syn_c0)) p0011
  have p0013 :=
    @g_mpbird (syn_wa (.classMem A V) (syn_wne A (syn_c0))) (syn_wbr A (syn_clec) A)
      (syn_wrex x A (syn_wrex y A (syn_wss (.cv x) (.cv y)))) p0009 p0012
  exact p0013

@[expose]
noncomputable def g_nclecid (A : Class) :
    Nominal.NPrf (.imp (.classMem A (syn_cncs)) (syn_wbr A (syn_clec) A)) :=
  by
  have p0000 := @g_nulnnc
  have p0001 := @g_eleq1 A (syn_c0) (syn_cncs)
  have p0002 :=
    @g_mtbiri (.classEq A (syn_c0)) (.classMem A (syn_cncs))
      (.classMem (syn_c0) (syn_cncs)) p0000 p0001
  have p0003 := @g_necon2ai (.classMem A (syn_cncs)) A (syn_c0) p0002
  have p0004 := @g_lecidg A (syn_cncs)
  have p0005 :=
    @g_mpdan (.classMem A (syn_cncs)) (syn_wne A (syn_c0)) (syn_wbr A (syn_clec) A) p0003
      p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end
