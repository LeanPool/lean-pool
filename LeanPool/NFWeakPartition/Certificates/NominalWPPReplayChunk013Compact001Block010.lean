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

/-- Checked nominal proof certificate identified upstream as `g_ovmuc`. -/
@[expose]
noncomputable def gOvmuc (g : Var) (M : Class) (N : Class) (a : Var) (b : Var)
    (dv_M_a : a ∉ M.fv) (dv_M_b : b ∉ M.fv) (dv_N_a : a ∉ N.fv) (dv_N_b : b ∉ N.fv)
    (dv_N_g : g ∉ N.fv) (dv_a_b : a ≠ b) (dv_a_g : a ≠ g) (dv_b_g : b ≠ g) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
        (.classEq (synCo M (synCmuc) N) (.cab a (synWrex b M
              (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))))) :=
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
      ((synCima (synCrn (synCin (synCins4
                (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
              (synCins2 (synCins2 (synCcnv (synCen)))))) N)).fv :=
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
  have dv_cache_0004 : g ∉ ((synCop (.cv b) (.cv a))).fv :=
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
      ((synCrn (synCin
            (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
            (synCins2 (synCins2 (synCcnv (synCen))))))).fv :=
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
  have dv_cache_0007 : c ∉ ((synCop (.cv g) (synCop (.cv b) (.cv a)))).fv :=
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
      ((synCin (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
          (synCins2 (synCins2 (synCcnv (synCen)))))).fv :=
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
  have dv_cache_0009 : a ∉ ((synCop (.cv c) (synCop (.cv g) (.cv b)))).fv :=
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
    a ∉ ((synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))).fv :=
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
  have dv_cache_0011 : a ∉ ((synCop (.cv b) (.cv g))).fv :=
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
    a ∉ ((synWbr (synCop (.cv b) (.cv g)) (synCcross) (.cv c))).fv :=
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
  have dv_cache_0013 : c ∉ ((synCxp (.cv b) (.cv g))).fv :=
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
  have dv_cache_0014 : c ∉ ((synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))).fv :=
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
      ((synCima (synCima (synCrn (synCin (synCins4
                  (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
                (synCins2 (synCins2 (synCcnv (synCen)))))) N) M)).fv :=
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
  have dv_cache_0035 : m ∉ ((synCncs)).fv :=
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
  have dv_cache_0036 : n ∉ ((synCncs)).fv :=
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
      ((Class.cab a (synWrex b M (synWrex g (.cv n)
              (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))))))).fv :=
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
      ((Class.cab a (synWrex b M
            (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))))))).fv :=
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
      ((Class.cab a (synWrex b M
            (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))))))).fv :=
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
    @gElima b (.cv a)
      (synCima (synCrn (synCin
            (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
            (synCins2 (synCins2 (synCcnv (synCen)))))) N)
      M dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    (Nominal.biimpRefl (synWbr (.cv b) (synCima (synCrn (synCin (synCins4
                (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
              (synCins2 (synCins2 (synCcnv (synCen)))))) N) (.cv a)))
  have p0002 :=
    @gElima g (synCop (.cv b) (.cv a))
      (synCrn (synCin
          (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
          (synCins2 (synCins2 (synCcnv (synCen))))))
      N dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0003 :=
    (Nominal.biimpRefl (synWbr (.cv g) (synCrn (synCin
            (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
            (synCins2 (synCins2 (synCcnv (synCen)))))) (synCop (.cv b) (.cv a))))
  have p0004 :=
    @gElrn2 c (synCop (.cv g) (synCop (.cv b) (.cv a)))
      (synCin (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
        (synCins2 (synCins2 (synCcnv (synCen)))))
      dv_cache_0007 dv_cache_0008
  have p0005 :=
    @gElin (synCop (.cv c) (synCop (.cv g) (synCop (.cv b) (.cv a))))
      (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
      (synCins2 (synCins2 (synCcnv (synCen))))
  have p0006 := @gVex a
  have p0007 :=
    @gOqelins4 (.cv c) (.cv g) (.cv b) (.cv a)
      (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))) p0006
  have p0008 :=
    @gElrn a (synCop (.cv c) (synCop (.cv g) (.cv b)))
      (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st))) dv_cache_0009 dv_cache_0010
  have p0009 :=
    @gTrtxp (.cv a) (.cv c) (synCop (.cv g) (.cv b)) (synCcross)
      (synCtxp (synC2nd) (synC1st))
  have p0010 := @gTrtxp (.cv a) (.cv g) (.cv b) (synC2nd) (synC1st)
  have p0011 :=
    @gAncom (synWbr (.cv a) (synC2nd) (.cv g)) (synWbr (.cv a) (synC1st) (.cv b))
  have p0012 := @gVex b
  have p0013 := @gVex g
  have p0014 := @gOp1st2nd (.cv b) (.cv g) (.cv a) p0012 p0013
  have p0015 :=
    @gN3bitri
      (synWbr (.cv a) (synCtxp (synC2nd) (synC1st)) (synCop (.cv g) (.cv b)))
      (synWa (synWbr (.cv a) (synC2nd) (.cv g)) (synWbr (.cv a) (synC1st) (.cv b)))
      (synWa (synWbr (.cv a) (synC1st) (.cv b)) (synWbr (.cv a) (synC2nd) (.cv g)))
      (.classEq (.cv a) (synCop (.cv b) (.cv g))) p0010 p0011 p0014
  have p0016 :=
    @gAnbi2i (synWbr (.cv a) (synCtxp (synC2nd) (synC1st)) (synCop (.cv g) (.cv b)))
      (.classEq (.cv a) (synCop (.cv b) (.cv g))) (synWbr (.cv a) (synCcross) (.cv c))
      p0015
  have p0017 :=
    @gAncom (synWbr (.cv a) (synCcross) (.cv c))
      (.classEq (.cv a) (synCop (.cv b) (.cv g)))
  have p0018 :=
    @gN3bitri
      (synWbr (.cv a) (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))
        (synCop (.cv c) (synCop (.cv g) (.cv b))))
      (synWa (synWbr (.cv a) (synCcross) (.cv c))
        (synWbr (.cv a) (synCtxp (synC2nd) (synC1st)) (synCop (.cv g) (.cv b))))
      (synWa (synWbr (.cv a) (synCcross) (.cv c))
        (.classEq (.cv a) (synCop (.cv b) (.cv g))))
      (synWa (.classEq (.cv a) (synCop (.cv b) (.cv g)))
        (synWbr (.cv a) (synCcross) (.cv c)))
      p0009 p0016 p0017
  have p0019 :=
    @gExbii
      (synWbr (.cv a) (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))
        (synCop (.cv c) (synCop (.cv g) (.cv b))))
      (synWa (.classEq (.cv a) (synCop (.cv b) (.cv g)))
        (synWbr (.cv a) (synCcross) (.cv c)))
      a p0018
  have p0020 := @gOpex (.cv b) (.cv g) p0012 p0013
  have p0021 := @gBreq1 (.cv a) (synCop (.cv b) (.cv g)) (.cv c) (synCcross)
  have p0022 :=
    @gCeqsexv (synWbr (.cv a) (synCcross) (.cv c))
      (synWbr (synCop (.cv b) (.cv g)) (synCcross) (.cv c)) a (synCop (.cv b) (.cv g))
      dv_cache_0011 dv_cache_0012 p0020 p0021
  have p0023 :=
    @gN3bitri
      (.classMem (synCop (.cv c) (synCop (.cv g) (.cv b)))
        (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
      (synWex a (synWbr (.cv a) (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))
          (synCop (.cv c) (synCop (.cv g) (.cv b)))))
      (synWex a (synWa (.classEq (.cv a) (synCop (.cv b) (.cv g)))
          (synWbr (.cv a) (synCcross) (.cv c))))
      (synWbr (synCop (.cv b) (.cv g)) (synCcross) (.cv c)) p0008 p0019 p0022
  have p0024 := @gBrcross (.cv b) (.cv g) (.cv c) p0012 p0013
  have p0025 :=
    @gN3bitri
      (.classMem (synCop (.cv c) (synCop (.cv g) (synCop (.cv b) (.cv a))))
        (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st))))))
      (.classMem (synCop (.cv c) (synCop (.cv g) (.cv b)))
        (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
      (synWbr (synCop (.cv b) (.cv g)) (synCcross) (.cv c))
      (.classEq (.cv c) (synCxp (.cv b) (.cv g))) p0007 p0023 p0024
  have p0026 :=
    @gOtelins2 (.cv c) (.cv g) (synCop (.cv b) (.cv a)) (synCins2 (synCcnv (synCen)))
      p0013
  have p0027 := @gOtelins2 (.cv c) (.cv b) (.cv a) (synCcnv (synCen)) p0012
  have p0028 := (Nominal.biimpRefl (synWbr (.cv c) (synCcnv (synCen)) (.cv a)))
  have p0029 := @gBrcnv (.cv c) (.cv a) (synCen)
  have p0030 :=
    @gBitr3i (.classMem (synCop (.cv c) (.cv a)) (synCcnv (synCen)))
      (synWbr (.cv c) (synCcnv (synCen)) (.cv a)) (synWbr (.cv a) (synCen) (.cv c))
      p0028 p0029
  have p0031 :=
    @gN3bitri
      (.classMem (synCop (.cv c) (synCop (.cv g) (synCop (.cv b) (.cv a))))
        (synCins2 (synCins2 (synCcnv (synCen)))))
      (.classMem (synCop (.cv c) (synCop (.cv b) (.cv a))) (synCins2 (synCcnv (synCen))))
      (.classMem (synCop (.cv c) (.cv a)) (synCcnv (synCen)))
      (synWbr (.cv a) (synCen) (.cv c)) p0026 p0027 p0030
  have p0032 :=
    @gAnbi12i
      (.classMem (synCop (.cv c) (synCop (.cv g) (synCop (.cv b) (.cv a))))
        (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st))))))
      (.classEq (.cv c) (synCxp (.cv b) (.cv g)))
      (.classMem (synCop (.cv c) (synCop (.cv g) (synCop (.cv b) (.cv a))))
        (synCins2 (synCins2 (synCcnv (synCen)))))
      (synWbr (.cv a) (synCen) (.cv c)) p0025 p0031
  have p0033 :=
    @gBitri
      (.classMem (synCop (.cv c) (synCop (.cv g) (synCop (.cv b) (.cv a)))) (synCin
          (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
          (synCins2 (synCins2 (synCcnv (synCen))))))
      (synWa (.classMem (synCop (.cv c) (synCop (.cv g) (synCop (.cv b) (.cv a))))
          (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st))))))
        (.classMem (synCop (.cv c) (synCop (.cv g) (synCop (.cv b) (.cv a))))
          (synCins2 (synCins2 (synCcnv (synCen))))))
      (synWa (.classEq (.cv c) (synCxp (.cv b) (.cv g))) (synWbr (.cv a) (synCen) (.cv c)))
      p0005 p0032
  have p0034 :=
    @gExbii
      (.classMem (synCop (.cv c) (synCop (.cv g) (synCop (.cv b) (.cv a)))) (synCin
          (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
          (synCins2 (synCins2 (synCcnv (synCen))))))
      (synWa (.classEq (.cv c) (synCxp (.cv b) (.cv g))) (synWbr (.cv a) (synCen) (.cv c)))
      c p0033
  have p0035 := @gXpex (.cv b) (.cv g) p0012 p0013
  have p0036 := @gBreq2 (.cv c) (synCxp (.cv b) (.cv g)) (.cv a) (synCen)
  have p0037 :=
    @gCeqsexv (synWbr (.cv a) (synCen) (.cv c))
      (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))) c (synCxp (.cv b) (.cv g))
      dv_cache_0013 dv_cache_0014 p0035 p0036
  have p0038 :=
    @gN3bitri
      (.classMem (synCop (.cv g) (synCop (.cv b) (.cv a))) (synCrn (synCin
            (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
            (synCins2 (synCins2 (synCcnv (synCen)))))))
      (synWex c (.classMem (synCop (.cv c) (synCop (.cv g) (synCop (.cv b) (.cv a))))
          (synCin
            (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
            (synCins2 (synCins2 (synCcnv (synCen)))))))
      (synWex c (synWa (.classEq (.cv c) (synCxp (.cv b) (.cv g)))
          (synWbr (.cv a) (synCen) (.cv c))))
      (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))) p0004 p0034 p0037
  have p0039 :=
    @gBitri
      (synWbr (.cv g) (synCrn (synCin
            (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
            (synCins2 (synCins2 (synCcnv (synCen)))))) (synCop (.cv b) (.cv a)))
      (.classMem (synCop (.cv g) (synCop (.cv b) (.cv a))) (synCrn (synCin
            (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
            (synCins2 (synCins2 (synCcnv (synCen)))))))
      (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))) p0003 p0038
  have p0040 :=
    @gRexbii
      (synWbr (.cv g) (synCrn (synCin
            (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
            (synCins2 (synCins2 (synCcnv (synCen)))))) (synCop (.cv b) (.cv a)))
      (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))) g N p0039
  have p0041 :=
    @gN3bitri
      (synWbr (.cv b) (synCima (synCrn (synCin (synCins4
                (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
              (synCins2 (synCins2 (synCcnv (synCen)))))) N) (.cv a))
      (.classMem (synCop (.cv b) (.cv a)) (synCima (synCrn (synCin (synCins4
                (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
              (synCins2 (synCins2 (synCcnv (synCen)))))) N))
      (synWrex g N (synWbr (.cv g) (synCrn (synCin (synCins4
                (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
              (synCins2 (synCins2 (synCcnv (synCen)))))) (synCop (.cv b) (.cv a))))
      (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))) p0001 p0002
      p0040
  have p0042 :=
    @gRexbii
      (synWbr (.cv b) (synCima (synCrn (synCin (synCins4
                (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
              (synCins2 (synCins2 (synCcnv (synCen)))))) N) (.cv a))
      (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))) b M p0041
  have p0043 :=
    @gBitri
      (.classMem (.cv a) (synCima (synCima (synCrn (synCin (synCins4
                  (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
                (synCins2 (synCins2 (synCcnv (synCen)))))) N) M))
      (synWrex b M (synWbr (.cv b) (synCima (synCrn (synCin (synCins4
                  (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
                (synCins2 (synCins2 (synCcnv (synCen)))))) N) (.cv a)))
      (synWrex b M (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))
      p0000 p0042
  have p0044 :=
    @gEqabi
      (synWrex b M (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))
      a
      (synCima (synCima (synCrn (synCin (synCins4
                (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
              (synCins2 (synCins2 (synCcnv (synCen)))))) N) M)
      dv_cache_0015 p0043
  have p0045 := @gCrossex
  have p0046 := @gN2ndex
  have p0047 := @gN1stex
  have p0048 := @gTxpex (synC2nd) (synC1st) p0046 p0047
  have p0049 := @gTxpex (synCcross) (synCtxp (synC2nd) (synC1st)) p0045 p0048
  have p0050 := @gRnex (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st))) p0049
  have p0051 :=
    @gIns4ex (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))) p0050
  have p0052 := @gEnex
  have p0053 := @gCnvex (synCen) p0052
  have p0054 := @gIns2ex (synCcnv (synCen)) p0053
  have p0055 := @gIns2ex (synCins2 (synCcnv (synCen))) p0054
  have p0056 :=
    @gInex (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
      (synCins2 (synCins2 (synCcnv (synCen)))) p0051 p0055
  have p0057 :=
    @gRnex
      (synCin (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
        (synCins2 (synCins2 (synCcnv (synCen)))))
      p0056
  have p0058 :=
    @gImaexg
      (synCrn (synCin
          (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
          (synCins2 (synCins2 (synCcnv (synCen))))))
      N (synCvv) (synCncs)
  have p0059 :=
    @gMpan
      (.classMem (synCrn (synCin
            (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
            (synCins2 (synCins2 (synCcnv (synCen)))))) (synCvv))
      (.classMem N (synCncs))
      (.classMem (synCima (synCrn (synCin (synCins4
                (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
              (synCins2 (synCins2 (synCcnv (synCen)))))) N) (synCvv))
      p0057 p0058
  have p0060 :=
    @gImaexg
      (synCima (synCrn (synCin
            (synCins4 (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
            (synCins2 (synCins2 (synCcnv (synCen)))))) N)
      M (synCvv) (synCncs)
  have p0061 :=
    @gSylan (.classMem N (synCncs))
      (.classMem (synCima (synCrn (synCin (synCins4
                (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
              (synCins2 (synCins2 (synCcnv (synCen)))))) N) (synCvv))
      (.classMem M (synCncs))
      (.classMem (synCima (synCima (synCrn (synCin (synCins4
                  (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
                (synCins2 (synCins2 (synCcnv (synCen)))))) N) M) (synCvv))
      p0059 p0060
  have p0062 :=
    @gAncoms (.classMem N (synCncs)) (.classMem M (synCncs))
      (.classMem (synCima (synCima (synCrn (synCin (synCins4
                  (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
                (synCins2 (synCins2 (synCcnv (synCen)))))) N) M) (synCvv))
      p0061
  have p0063 :=
    @gSyl5eqelr (synWa (.classMem M (synCncs)) (.classMem N (synCncs)))
      (.cab a (synWrex b M
          (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))))))
      (synCima (synCima (synCrn (synCin (synCins4
                (synCrn (synCtxp (synCcross) (synCtxp (synC2nd) (synC1st)))))
              (synCins2 (synCins2 (synCcnv (synCen)))))) N) M)
      (synCvv) p0044 p0062
  have p0064 :=
    @gRexeq (synWrex g (.cv n) (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))) b
      (.cv m) M dv_cache_0016 dv_cache_0003
  have p0065 :=
    @gAbbidv (.classEq (.cv m) M)
      (synWrex b (.cv m)
        (synWrex g (.cv n) (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))
      (synWrex b M (synWrex g (.cv n) (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))
      a dv_cache_0017 p0064
  have p0066 :=
    @gRexeq (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))) g (.cv n) N
      dv_cache_0018 dv_cache_0006
  have p0067 :=
    @gRexbidv (.classEq (.cv n) N)
      (synWrex g (.cv n) (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))))
      (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))) b M
      dv_cache_0019 p0066
  have p0068 :=
    @gAbbidv (.classEq (.cv n) N)
      (synWrex b M (synWrex g (.cv n) (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))
      (synWrex b M (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))
      a dv_cache_0020 p0067
  have p0069 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfMuc g m n a b
      dv_cache_0021 dv_cache_0022 dv_cache_0023 dv_cache_0024 dv_cache_0025 dv_cache_0026
      dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030
  have p0070 :=
    @gOvmpt2g m n M N (synCncs) (synCncs)
      (.cab a (synWrex b (.cv m)
          (synWrex g (.cv n) (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))))))
      (.cab a (synWrex b M
          (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))))))
      (synCmuc)
      (.cab a (synWrex b M
          (synWrex g (.cv n) (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g))))))
      (synCvv) dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0035 dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039
      dv_cache_0030 p0065 p0068 p0069
  have p0071 :=
    @gMpd3an3 (.classMem M (synCncs)) (.classMem N (synCncs))
      (.classMem (.cab a (synWrex b M
            (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))) (synCvv))
      (.classEq (synCo M (synCmuc) N) (.cab a (synWrex b M
            (synWrex g N (synWbr (.cv a) (synCen) (synCxp (.cv b) (.cv g)))))))
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

/-- Checked nominal proof certificate identified upstream as `g_mucnc`. -/
@[expose]
noncomputable def gMucnc (A : Class) (B : Class)
    (hyp_mucnc_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_mucnc_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.classEq (synCo (synCnc A) (synCmuc) (synCnc B)) (synCnc (synCxp A B))) :=
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
  have dv_cache_0001 : x ∉ ((synCnc A)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnc, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCnc A)).fv :=
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
  have dv_cache_0003 : x ∉ ((synCnc B)).fv :=
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
  have dv_cache_0004 : y ∉ ((synCnc B)).fv :=
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
  have dv_cache_0005 : z ∉ ((synCnc B)).fv :=
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
  have dv_cache_0009 : x ∉ ((synCxp A B)).fv :=
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
  have dv_cache_0010 : x ∉ ((synCen)).fv :=
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
  have dv_cache_0011 : z ∉ ((synCnc A)).fv :=
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
      ((synWa (synWa (synWbr A (synCen) A) (synWbr B (synCen) B))
          (synWbr (synCxp A B) (synCen) (.cv x)))).fv :=
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
      ((synWa (synWa (synWbr A (synCen) A) (synWbr B (synCen) B))
          (synWbr (synCxp A B) (synCen) (.cv x)))).fv :=
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
  have dv_cache_0018 : y ∉ ((synWbr (synCxp A B) (synCen) (.cv x))).fv :=
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
  have dv_cache_0019 : z ∉ ((synWbr (synCxp A B) (synCen) (.cv x))).fv :=
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
  have p0000 := @gNcelncsi A hyp_mucnc_1
  have p0001 := @gNcelncsi B hyp_mucnc_2
  have p0002 :=
    @gOvmuc z (synCnc A) (synCnc B) x y dv_cache_0001 dv_cache_0002 dv_cache_0003
      dv_cache_0004 dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0003 :=
    @gMp2an (.classMem (synCnc A) (synCncs)) (.classMem (synCnc B) (synCncs))
      (.classEq (synCo (synCnc A) (synCmuc) (synCnc B)) (.cab x (synWrex y (synCnc A)
            (synWrex z (synCnc B) (synWbr (.cv x) (synCen) (synCxp (.cv y) (.cv z)))))))
      p0000 p0001 p0002
  have p0004 := (Nominal.classEqRefl (synCnc (synCxp A B)))
  have p0005 := @gDfec2 x (synCxp A B) (synCen) dv_cache_0009 dv_cache_0010
  have p0006 := @gElnc (.cv y) A
  have p0007 := @gElnc (.cv z) B
  have p0008 :=
    @gAnbi12i (.classMem (.cv y) (synCnc A)) (synWbr (.cv y) (synCen) A)
      (.classMem (.cv z) (synCnc B)) (synWbr (.cv z) (synCen) B) p0006 p0007
  have p0009 := @gEnsym (.cv x) (synCxp (.cv y) (.cv z))
  have p0010 :=
    @gAnbi12i (synWa (.classMem (.cv y) (synCnc A)) (.classMem (.cv z) (synCnc B)))
      (synWa (synWbr (.cv y) (synCen) A) (synWbr (.cv z) (synCen) B))
      (synWbr (.cv x) (synCen) (synCxp (.cv y) (.cv z)))
      (synWbr (synCxp (.cv y) (.cv z)) (synCen) (.cv x)) p0008 p0009
  have p0011 :=
    @gN2exbii
      (synWa (synWa (.classMem (.cv y) (synCnc A)) (.classMem (.cv z) (synCnc B)))
        (synWbr (.cv x) (synCen) (synCxp (.cv y) (.cv z))))
      (synWa (synWa (synWbr (.cv y) (synCen) A) (synWbr (.cv z) (synCen) B))
        (synWbr (synCxp (.cv y) (.cv z)) (synCen) (.cv x)))
      y z p0010
  have p0012 :=
    @gR2ex (synWbr (.cv x) (synCen) (synCxp (.cv y) (.cv z))) y z (synCnc A)
      (synCnc B) dv_cache_0011 dv_cache_0008
  have p0013 := @gEnrflx A hyp_mucnc_1
  have p0014 := @gEnrflx B hyp_mucnc_2
  have p0015 := @gBreq1 (.cv y) A A (synCen)
  have p0016 := @gBreq1 (.cv z) B B (synCen)
  have p0017 :=
    @gBi2anan9 (.classEq (.cv y) A) (synWbr (.cv y) (synCen) A) (synWbr A (synCen) A)
      (.classEq (.cv z) B) (synWbr (.cv z) (synCen) B) (synWbr B (synCen) B) p0015
      p0016
  have p0018 := @gXpeq12 (.cv y) A (.cv z) B
  have p0019 :=
    @gBreq1d (synWa (.classEq (.cv y) A) (.classEq (.cv z) B)) (synCxp (.cv y) (.cv z))
      (synCxp A B) (.cv x) (synCen) p0018
  have p0020 :=
    @gAnbi12d (synWa (.classEq (.cv y) A) (.classEq (.cv z) B))
      (synWa (synWbr (.cv y) (synCen) A) (synWbr (.cv z) (synCen) B))
      (synWa (synWbr A (synCen) A) (synWbr B (synCen) B))
      (synWbr (synCxp (.cv y) (.cv z)) (synCen) (.cv x))
      (synWbr (synCxp A B) (synCen) (.cv x)) p0017 p0019
  have p0021 :=
    @gSpc2ev
      (synWa (synWa (synWbr (.cv y) (synCen) A) (synWbr (.cv z) (synCen) B))
        (synWbr (synCxp (.cv y) (.cv z)) (synCen) (.cv x)))
      (synWa (synWa (synWbr A (synCen) A) (synWbr B (synCen) B))
        (synWbr (synCxp A B) (synCen) (.cv x)))
      y z A B dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0008 hyp_mucnc_1 hyp_mucnc_2 p0020
  have p0022 :=
    @gMpanl12 (synWbr A (synCen) A) (synWbr B (synCen) B)
      (synWbr (synCxp A B) (synCen) (.cv x))
      (synWex y (synWex z
          (synWa (synWa (synWbr (.cv y) (synCen) A) (synWbr (.cv z) (synCen) B))
            (synWbr (synCxp (.cv y) (.cv z)) (synCen) (.cv x)))))
      p0013 p0014 p0021
  have p0023 := @gXpen (.cv y) A (.cv z) B
  have p0024 := @gEnsym (synCxp (.cv y) (.cv z)) (synCxp A B)
  have p0025 :=
    @gSylib (synWa (synWbr (.cv y) (synCen) A) (synWbr (.cv z) (synCen) B))
      (synWbr (synCxp (.cv y) (.cv z)) (synCen) (synCxp A B))
      (synWbr (synCxp A B) (synCen) (synCxp (.cv y) (.cv z))) p0023 p0024
  have p0026 := @gEntr (synCxp A B) (synCxp (.cv y) (.cv z)) (.cv x)
  have p0027 :=
    @gSylan (synWa (synWbr (.cv y) (synCen) A) (synWbr (.cv z) (synCen) B))
      (synWbr (synCxp A B) (synCen) (synCxp (.cv y) (.cv z)))
      (synWbr (synCxp (.cv y) (.cv z)) (synCen) (.cv x))
      (synWbr (synCxp A B) (synCen) (.cv x)) p0025 p0026
  have p0028 :=
    @gExlimivv
      (synWa (synWa (synWbr (.cv y) (synCen) A) (synWbr (.cv z) (synCen) B))
        (synWbr (synCxp (.cv y) (.cv z)) (synCen) (.cv x)))
      (synWbr (synCxp A B) (synCen) (.cv x)) y z dv_cache_0018 dv_cache_0019 p0027
  have p0029 :=
    @gImpbii (synWbr (synCxp A B) (synCen) (.cv x))
      (synWex y (synWex z
          (synWa (synWa (synWbr (.cv y) (synCen) A) (synWbr (.cv z) (synCen) B))
            (synWbr (synCxp (.cv y) (.cv z)) (synCen) (.cv x)))))
      p0022 p0028
  have p0030 :=
    @gN3bitr4ri
      (synWex y (synWex z
          (synWa (synWa (.classMem (.cv y) (synCnc A)) (.classMem (.cv z) (synCnc B)))
            (synWbr (.cv x) (synCen) (synCxp (.cv y) (.cv z))))))
      (synWex y (synWex z
          (synWa (synWa (synWbr (.cv y) (synCen) A) (synWbr (.cv z) (synCen) B))
            (synWbr (synCxp (.cv y) (.cv z)) (synCen) (.cv x)))))
      (synWrex y (synCnc A)
        (synWrex z (synCnc B) (synWbr (.cv x) (synCen) (synCxp (.cv y) (.cv z)))))
      (synWbr (synCxp A B) (synCen) (.cv x)) p0011 p0012 p0029
  have p0031 :=
    @gAbbii (synWbr (synCxp A B) (synCen) (.cv x))
      (synWrex y (synCnc A)
        (synWrex z (synCnc B) (synWbr (.cv x) (synCen) (synCxp (.cv y) (.cv z)))))
      x p0030
  have p0032 :=
    @gN3eqtrri (synCnc (synCxp A B)) (synCec (synCxp A B) (synCen))
      (.cab x (synWbr (synCxp A B) (synCen) (.cv x)))
      (.cab x (synWrex y (synCnc A)
          (synWrex z (synCnc B) (synWbr (.cv x) (synCen) (synCxp (.cv y) (.cv z))))))
      p0004 p0005 p0031
  have p0033 :=
    @gEqtri (synCo (synCnc A) (synCmuc) (synCnc B))
      (.cab x (synWrex y (synCnc A)
          (synWrex z (synCnc B) (synWbr (.cv x) (synCen) (synCxp (.cv y) (.cv z))))))
      (synCnc (synCxp A B)) p0003 p0032
  exact p0033

/-- Checked nominal proof certificate identified upstream as `g_muccl`. -/
@[expose]
noncomputable def gMuccl (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
        (.classMem (synCo A (synCmuc) B) (synCncs))) :=
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
  have dv_cache_0003 : y ∉ ((Wff.classEq A (synCnc (.cv x)))).fv :=
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
  have dv_cache_0004 : x ∉ ((Wff.classEq B (synCnc (.cv y)))).fv :=
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
  have dv_cache_0005 : x ∉ ((Wff.classMem (synCo A (synCmuc) B) (synCncs))).fv :=
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
  have dv_cache_0006 : y ∉ ((Wff.classMem (synCo A (synCmuc) B) (synCncs))).fv :=
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
  have p0000 := @gElncs x A dv_cache_0001
  have p0001 := @gElncs y B dv_cache_0002
  have p0002 :=
    @gAnbi12i (.classMem A (synCncs)) (synWex x (.classEq A (synCnc (.cv x))))
      (.classMem B (synCncs)) (synWex y (.classEq B (synCnc (.cv y)))) p0000 p0001
  have p0003 :=
    @gEeanv (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @gBitr4i (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWa (synWex x (.classEq A (synCnc (.cv x))))
        (synWex y (.classEq B (synCnc (.cv y)))))
      (synWex x (synWex y
          (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))))
      p0002 p0003
  have p0005 := @gOveq12 A (synCnc (.cv x)) B (synCnc (.cv y)) (synCmuc)
  have p0006 := @gVex x
  have p0007 := @gVex y
  have p0008 := @gMucnc (.cv x) (.cv y) p0006 p0007
  have p0009 := @gXpex (.cv x) (.cv y) p0006 p0007
  have p0010 := @gNcelncsi (synCxp (.cv x) (.cv y)) p0009
  have p0011 :=
    @gEqeltri (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv y)))
      (synCnc (synCxp (.cv x) (.cv y))) (synCncs) p0008 p0010
  have p0012 :=
    @gSyl6eqel (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))
      (synCo A (synCmuc) B) (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv y)))
      (synCncs) p0005 p0011
  have p0013 :=
    @gExlimivv (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))
      (.classMem (synCo A (synCmuc) B) (synCncs)) x y dv_cache_0005 dv_cache_0006 p0012
  have p0014 :=
    @gSylbi (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWex x (synWex y
          (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))))
      (.classMem (synCo A (synCmuc) B) (synCncs)) p0004 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_muccom`. -/
@[expose]
noncomputable def gMuccom (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
        (.classEq (synCo A (synCmuc) B) (synCo B (synCmuc) A))) :=
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
  have dv_cache_0003 : y ∉ ((Wff.classEq A (synCnc (.cv x)))).fv :=
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
  have dv_cache_0004 : x ∉ ((Wff.classEq B (synCnc (.cv y)))).fv :=
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
    x ∉ ((Wff.classEq (synCo A (synCmuc) B) (synCo B (synCmuc) A))).fv :=
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
    y ∉ ((Wff.classEq (synCo A (synCmuc) B) (synCo B (synCmuc) A))).fv :=
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
  have p0000 := @gElncs x A dv_cache_0001
  have p0001 := @gElncs y B dv_cache_0002
  have p0002 :=
    @gAnbi12i (.classMem A (synCncs)) (synWex x (.classEq A (synCnc (.cv x))))
      (.classMem B (synCncs)) (synWex y (.classEq B (synCnc (.cv y)))) p0000 p0001
  have p0003 :=
    @gEeanv (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @gBitr4i (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWa (synWex x (.classEq A (synCnc (.cv x))))
        (synWex y (.classEq B (synCnc (.cv y)))))
      (synWex x (synWex y
          (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))))
      p0002 p0003
  have p0005 := @gVex x
  have p0006 := @gVex y
  have p0007 := @gXpcomen (.cv x) (.cv y) p0005 p0006
  have p0008 := @gXpex (.cv x) (.cv y) p0005 p0006
  have p0009 := @gEqnc (synCxp (.cv x) (.cv y)) (synCxp (.cv y) (.cv x)) p0008
  have p0010 :=
    @gMpbir
      (.classEq (synCnc (synCxp (.cv x) (.cv y))) (synCnc (synCxp (.cv y) (.cv x))))
      (synWbr (synCxp (.cv x) (.cv y)) (synCen) (synCxp (.cv y) (.cv x))) p0007 p0009
  have p0011 := @gMucnc (.cv x) (.cv y) p0005 p0006
  have p0012 := @gMucnc (.cv y) (.cv x) p0006 p0005
  have p0013 :=
    @gN3eqtr4i (synCnc (synCxp (.cv x) (.cv y))) (synCnc (synCxp (.cv y) (.cv x)))
      (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv y)))
      (synCo (synCnc (.cv y)) (synCmuc) (synCnc (.cv x))) p0010 p0011 p0012
  have p0014 := @gOveq12 A (synCnc (.cv x)) B (synCnc (.cv y)) (synCmuc)
  have p0015 := @gOveq12 B (synCnc (.cv y)) A (synCnc (.cv x)) (synCmuc)
  have p0016 :=
    @gAncoms (.classEq B (synCnc (.cv y))) (.classEq A (synCnc (.cv x)))
      (.classEq (synCo B (synCmuc) A) (synCo (synCnc (.cv y)) (synCmuc) (synCnc (.cv x))))
      p0015
  have p0017 :=
    @gN3eqtr4a (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))
      (synCo (synCnc (.cv x)) (synCmuc) (synCnc (.cv y)))
      (synCo (synCnc (.cv y)) (synCmuc) (synCnc (.cv x))) (synCo A (synCmuc) B)
      (synCo B (synCmuc) A) p0013 p0014 p0016
  have p0018 :=
    @gExlimivv (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))
      (.classEq (synCo A (synCmuc) B) (synCo B (synCmuc) A)) x y dv_cache_0005
      dv_cache_0006 p0017
  have p0019 :=
    @gSylbi (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWex x (synWex y
          (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))))
      (.classEq (synCo A (synCmuc) B) (synCo B (synCmuc) A)) p0004 p0018
  exact p0019

/-- Checked nominal proof certificate identified upstream as `g_ncdisjun`. -/
@[expose]
noncomputable def gNcdisjun (A : Class) (B : Class)
    (hyp_ncdisjun_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_ncdisjun_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf
      (.imp (.classEq (synCin A B) (synC0))
        (.classEq (synCnc (synCun A B)) (synCplc (synCnc A) (synCnc B)))) :=
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
  have dv_cache_0002 : r ∉ ((synCun A B)).fv :=
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
    r ∉ ((Wff.classMem (.cv x) (synCplc (synCnc A) (synCnc B)))).fv :=
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
  have dv_cache_0004 : r ∉ ((Wff.classEq (synCin A B) (synC0))).fv :=
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
  have dv_cache_0007 : p ∉ ((synCnc A)).fv :=
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
  have dv_cache_0008 : q ∉ ((synCnc A)).fv :=
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
  have dv_cache_0009 : p ∉ ((synCnc B)).fv :=
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
  have dv_cache_0010 : q ∉ ((synCnc B)).fv :=
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
  have dv_cache_0012 : p ∉ ((synWbr (.cv x) (synCen) (synCun A B))).fv :=
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
  have dv_cache_0013 : q ∉ ((synWbr (.cv x) (synCen) (synCun A B))).fv :=
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
  have dv_cache_0014 : p ∉ ((Wff.classEq (synCin A B) (synC0))).fv :=
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
  have dv_cache_0015 : q ∉ ((Wff.classEq (synCin A B) (synC0))).fv :=
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
  have dv_cache_0016 : x ∉ ((synCnc (synCun A B))).fv :=
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
  have dv_cache_0017 : x ∉ ((synCplc (synCnc A) (synCnc B))).fv :=
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
  have dv_cache_0018 : x ∉ ((Wff.classEq (synCin A B) (synC0))).fv :=
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
  have p0000 := @gElnc (.cv x) (synCun A B)
  have p0001 := @gBren (.cv x) (synCun A B) r dv_cache_0001 dv_cache_0002
  have p0002 := @gF1ocnv (.cv x) (synCun A B) (.cv r)
  have p0003 := @gImaundi (synCcnv (.cv r)) A B
  have p0004 := @gImadmrn (synCcnv (.cv r))
  have p0005 :=
    @gA1i
      (.classEq (synCima (synCcnv (.cv r)) (synCdm (synCcnv (.cv r))))
        (synCrn (synCcnv (.cv r))))
      (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x)) p0004
  have p0006 := @gF1odm (synCun A B) (.cv x) (synCcnv (.cv r))
  have p0007 :=
    @gImaeq2d (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synCdm (synCcnv (.cv r))) (synCun A B) (synCcnv (.cv r)) p0006
  have p0008 := @gF1ofo (synCun A B) (.cv x) (synCcnv (.cv r))
  have p0009 := @gForn (synCun A B) (.cv x) (synCcnv (.cv r))
  have p0010 :=
    @gSyl (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWfo (synCcnv (.cv r)) (synCun A B) (.cv x))
      (.classEq (synCrn (synCcnv (.cv r))) (.cv x)) p0008 p0009
  have p0011 :=
    @gN3eqtr3d (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synCima (synCcnv (.cv r)) (synCdm (synCcnv (.cv r))))
      (synCrn (synCcnv (.cv r))) (synCima (synCcnv (.cv r)) (synCun A B)) (.cv x)
      p0005 p0007 p0010
  have p0012 :=
    @gSyl5eqr (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synCun (synCima (synCcnv (.cv r)) A) (synCima (synCcnv (.cv r)) B))
      (synCima (synCcnv (.cv r)) (synCun A B)) (.cv x) p0003 p0011
  have p0013 :=
    @gAdantl (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (.classEq (synCun (synCima (synCcnv (.cv r)) A) (synCima (synCcnv (.cv r)) B))
        (.cv x))
      (.classEq (synCin A B) (synC0)) p0012
  have p0014 := @gF1of1 (synCun A B) (.cv x) (synCcnv (.cv r))
  have p0015 := @gSsun1 A B
  have p0016 := @gF1ores (synCun A B) (.cv x) A (synCcnv (.cv r))
  have p0017 :=
    @gSylancl (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWf1 (synCcnv (.cv r)) (synCun A B) (.cv x)) (synWss A (synCun A B))
      (synWf1o (synCres (synCcnv (.cv r)) A) A (synCima (synCcnv (.cv r)) A)) p0014
      p0015 p0016
  have p0018 :=
    @gF1ocnv A (synCima (synCcnv (.cv r)) A) (synCres (synCcnv (.cv r)) A)
  have p0019 := @gVex r
  have p0020 := @gCnvex (.cv r) p0019
  have p0021 := @gResex (synCcnv (.cv r)) A p0020 hyp_ncdisjun_1
  have p0022 := @gCnvex (synCres (synCcnv (.cv r)) A) p0021
  have p0023 :=
    @gF1oen (synCima (synCcnv (.cv r)) A) A (synCcnv (synCres (synCcnv (.cv r)) A))
      p0022
  have p0024 :=
    @gN3syl (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWf1o (synCres (synCcnv (.cv r)) A) A (synCima (synCcnv (.cv r)) A))
      (synWf1o (synCcnv (synCres (synCcnv (.cv r)) A)) (synCima (synCcnv (.cv r)) A) A)
      (synWbr (synCima (synCcnv (.cv r)) A) (synCen) A) p0017 p0018 p0023
  have p0025 := @gElnc (synCima (synCcnv (.cv r)) A) A
  have p0026 :=
    @gSylibr (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWbr (synCima (synCcnv (.cv r)) A) (synCen) A)
      (.classMem (synCima (synCcnv (.cv r)) A) (synCnc A)) p0024 p0025
  have p0027 :=
    @gAdantl (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (.classMem (synCima (synCcnv (.cv r)) A) (synCnc A))
      (.classEq (synCin A B) (synC0)) p0026
  have p0028 := @gSsun2 B A
  have p0029 := @gF1ores (synCun A B) (.cv x) B (synCcnv (.cv r))
  have p0030 :=
    @gSylancl (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWf1 (synCcnv (.cv r)) (synCun A B) (.cv x)) (synWss B (synCun A B))
      (synWf1o (synCres (synCcnv (.cv r)) B) B (synCima (synCcnv (.cv r)) B)) p0014
      p0028 p0029
  have p0031 :=
    @gF1ocnv B (synCima (synCcnv (.cv r)) B) (synCres (synCcnv (.cv r)) B)
  have p0032 := @gResex (synCcnv (.cv r)) B p0020 hyp_ncdisjun_2
  have p0033 := @gCnvex (synCres (synCcnv (.cv r)) B) p0032
  have p0034 :=
    @gF1oen (synCima (synCcnv (.cv r)) B) B (synCcnv (synCres (synCcnv (.cv r)) B))
      p0033
  have p0035 :=
    @gN3syl (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWf1o (synCres (synCcnv (.cv r)) B) B (synCima (synCcnv (.cv r)) B))
      (synWf1o (synCcnv (synCres (synCcnv (.cv r)) B)) (synCima (synCcnv (.cv r)) B) B)
      (synWbr (synCima (synCcnv (.cv r)) B) (synCen) B) p0030 p0031 p0034
  have p0036 :=
    @gAdantl (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWbr (synCima (synCcnv (.cv r)) B) (synCen) B)
      (.classEq (synCin A B) (synC0)) p0035
  have p0037 := @gElnc (synCima (synCcnv (.cv r)) B) B
  have p0038 :=
    @gSylibr
      (synWa (.classEq (synCin A B) (synC0))
        (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x)))
      (synWbr (synCima (synCcnv (.cv r)) B) (synCen) B)
      (.classMem (synCima (synCcnv (.cv r)) B) (synCnc B)) p0036 p0037
  have p0039 := (Nominal.biimpRefl (synWf1 (synCcnv (.cv r)) (synCun A B) (.cv x)))
  have p0040 :=
    @gSimprbi (synWf1 (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWf (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWfun (synCcnv (synCcnv (.cv r)))) p0039
  have p0041 := @gImain A B (synCcnv (.cv r))
  have p0042 :=
    @gN3syl (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWf1 (synCcnv (.cv r)) (synCun A B) (.cv x))
      (synWfun (synCcnv (synCcnv (.cv r))))
      (.classEq (synCima (synCcnv (.cv r)) (synCin A B))
        (synCin (synCima (synCcnv (.cv r)) A) (synCima (synCcnv (.cv r)) B)))
      p0014 p0040 p0041
  have p0043 :=
    @gAdantl (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (.classEq (synCima (synCcnv (.cv r)) (synCin A B))
        (synCin (synCima (synCcnv (.cv r)) A) (synCima (synCcnv (.cv r)) B)))
      (.classEq (synCin A B) (synC0)) p0042
  have p0044 := @gImaeq2 (synCin A B) (synC0) (synCcnv (.cv r))
  have p0045 := @gIma0 (synCcnv (.cv r))
  have p0046 :=
    @gSyl6eq (.classEq (synCin A B) (synC0))
      (synCima (synCcnv (.cv r)) (synCin A B)) (synCima (synCcnv (.cv r)) (synC0))
      (synC0) p0044 p0045
  have p0047 :=
    @gAdantr (.classEq (synCin A B) (synC0))
      (.classEq (synCima (synCcnv (.cv r)) (synCin A B)) (synC0))
      (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x)) p0046
  have p0048 :=
    @gEqtr3d
      (synWa (.classEq (synCin A B) (synC0))
        (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x)))
      (synCima (synCcnv (.cv r)) (synCin A B))
      (synCin (synCima (synCcnv (.cv r)) A) (synCima (synCcnv (.cv r)) B)) (synC0)
      p0043 p0047
  have p0049 :=
    @gEladdci (synCima (synCcnv (.cv r)) A) (synCima (synCcnv (.cv r)) B) (synCnc A)
      (synCnc B)
  have p0050 :=
    @gSyl3anc
      (synWa (.classEq (synCin A B) (synC0))
        (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x)))
      (.classMem (synCima (synCcnv (.cv r)) A) (synCnc A))
      (.classMem (synCima (synCcnv (.cv r)) B) (synCnc B))
      (.classEq (synCin (synCima (synCcnv (.cv r)) A) (synCima (synCcnv (.cv r)) B))
        (synC0))
      (.classMem (synCun (synCima (synCcnv (.cv r)) A) (synCima (synCcnv (.cv r)) B))
        (synCplc (synCnc A) (synCnc B)))
      p0027 p0038 p0048 p0049
  have p0051 :=
    @gEqeltrrd
      (synWa (.classEq (synCin A B) (synC0))
        (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x)))
      (synCun (synCima (synCcnv (.cv r)) A) (synCima (synCcnv (.cv r)) B)) (.cv x)
      (synCplc (synCnc A) (synCnc B)) p0013 p0050
  have p0052 :=
    @gEx (.classEq (synCin A B) (synC0))
      (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (.classMem (.cv x) (synCplc (synCnc A) (synCnc B))) p0051
  have p0053 :=
    @gSyl5 (synWf1o (.cv r) (.cv x) (synCun A B))
      (synWf1o (synCcnv (.cv r)) (synCun A B) (.cv x))
      (.classEq (synCin A B) (synC0))
      (.classMem (.cv x) (synCplc (synCnc A) (synCnc B))) p0002 p0052
  have p0054 :=
    @gExlimdv (.classEq (synCin A B) (synC0)) (synWf1o (.cv r) (.cv x) (synCun A B))
      (.classMem (.cv x) (synCplc (synCnc A) (synCnc B))) r dv_cache_0003 dv_cache_0004
      p0053
  have p0055 :=
    @gSyl5bi (synWbr (.cv x) (synCen) (synCun A B))
      (synWex r (synWf1o (.cv r) (.cv x) (synCun A B)))
      (.classEq (synCin A B) (synC0))
      (.classMem (.cv x) (synCplc (synCnc A) (synCnc B))) p0001 p0054
  have p0056 :=
    @gEladdc (.cv x) (synCnc A) (synCnc B) p q dv_cache_0005 dv_cache_0006
      dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0057 :=
    @gSimplrl (.classEq (synCin A B) (synC0)) (.classMem (.cv p) (synCnc A))
      (.classMem (.cv q) (synCnc B)) (.classEq (synCin (.cv p) (.cv q)) (synC0))
  have p0058 := @gElnc (.cv p) A
  have p0059 :=
    @gSylib
      (synWa (synWa (.classEq (synCin A B) (synC0))
          (synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B))))
        (.classEq (synCin (.cv p) (.cv q)) (synC0)))
      (.classMem (.cv p) (synCnc A)) (synWbr (.cv p) (synCen) A) p0057 p0058
  have p0060 :=
    @gSimplrr (.classEq (synCin A B) (synC0)) (.classMem (.cv p) (synCnc A))
      (.classMem (.cv q) (synCnc B)) (.classEq (synCin (.cv p) (.cv q)) (synC0))
  have p0061 := @gElnc (.cv q) B
  have p0062 :=
    @gSylib
      (synWa (synWa (.classEq (synCin A B) (synC0))
          (synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B))))
        (.classEq (synCin (.cv p) (.cv q)) (synC0)))
      (.classMem (.cv q) (synCnc B)) (synWbr (.cv q) (synCen) B) p0060 p0061
  have p0063 :=
    @gSimpr
      (synWa (.classEq (synCin A B) (synC0))
        (synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B))))
      (.classEq (synCin (.cv p) (.cv q)) (synC0))
  have p0064 :=
    @gSimpll (.classEq (synCin A B) (synC0))
      (synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B)))
      (.classEq (synCin (.cv p) (.cv q)) (synC0))
  have p0065 := @gUnen (.cv p) A (.cv q) B
  have p0066 :=
    @gSyl22anc
      (synWa (synWa (.classEq (synCin A B) (synC0))
          (synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B))))
        (.classEq (synCin (.cv p) (.cv q)) (synC0)))
      (synWbr (.cv p) (synCen) A) (synWbr (.cv q) (synCen) B)
      (.classEq (synCin (.cv p) (.cv q)) (synC0)) (.classEq (synCin A B) (synC0))
      (synWbr (synCun (.cv p) (.cv q)) (synCen) (synCun A B)) p0059 p0062 p0063 p0064
      p0065
  have p0067 := @gBreq1 (.cv x) (synCun (.cv p) (.cv q)) (synCun A B) (synCen)
  have p0068 :=
    @gSyl5ibrcom
      (synWa (synWa (.classEq (synCin A B) (synC0))
          (synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B))))
        (.classEq (synCin (.cv p) (.cv q)) (synC0)))
      (synWbr (.cv x) (synCen) (synCun A B))
      (.classEq (.cv x) (synCun (.cv p) (.cv q)))
      (synWbr (synCun (.cv p) (.cv q)) (synCen) (synCun A B)) p0066 p0067
  have p0069 :=
    @gExpimpd
      (synWa (.classEq (synCin A B) (synC0))
        (synWa (.classMem (.cv p) (synCnc A)) (.classMem (.cv q) (synCnc B))))
      (.classEq (synCin (.cv p) (.cv q)) (synC0))
      (.classEq (.cv x) (synCun (.cv p) (.cv q)))
      (synWbr (.cv x) (synCen) (synCun A B)) p0068
  have p0070 :=
    @gRexlimdvva (.classEq (synCin A B) (synC0))
      (synWa (.classEq (synCin (.cv p) (.cv q)) (synC0))
        (.classEq (.cv x) (synCun (.cv p) (.cv q))))
      (synWbr (.cv x) (synCen) (synCun A B)) p q (synCnc A) (synCnc B) dv_cache_0008
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0011 p0069
  have p0071 :=
    @gSyl5bi (.classMem (.cv x) (synCplc (synCnc A) (synCnc B)))
      (synWrex p (synCnc A) (synWrex q (synCnc B)
          (synWa (.classEq (synCin (.cv p) (.cv q)) (synC0))
            (.classEq (.cv x) (synCun (.cv p) (.cv q))))))
      (.classEq (synCin A B) (synC0)) (synWbr (.cv x) (synCen) (synCun A B)) p0056
      p0070
  have p0072 :=
    @gImpbid (.classEq (synCin A B) (synC0)) (synWbr (.cv x) (synCen) (synCun A B))
      (.classMem (.cv x) (synCplc (synCnc A) (synCnc B))) p0055 p0071
  have p0073 :=
    @gSyl5bb (.classMem (.cv x) (synCnc (synCun A B)))
      (synWbr (.cv x) (synCen) (synCun A B)) (.classEq (synCin A B) (synC0))
      (.classMem (.cv x) (synCplc (synCnc A) (synCnc B))) p0000 p0072
  have p0074 :=
    @gEqrdv (.classEq (synCin A B) (synC0)) x (synCnc (synCun A B))
      (synCplc (synCnc A) (synCnc B)) dv_cache_0016 dv_cache_0017 dv_cache_0018 p0073
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

/-- Checked nominal proof certificate identified upstream as `g_df0c2`. -/
@[expose]
noncomputable def gDf0c2 : Nominal.NPrf (.classEq (synC0c) (synCnc (synC0))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  have dv_cache_0001 : x ∉ ((synC0)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((synCen)).fv :=
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
  have dv_cache_0003 : x ∉ ((synC0c)).fv :=
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
  have p0000 := @gDfec2 x (synC0) (synCen) dv_cache_0001 dv_cache_0002
  have p0001 := (Nominal.classEqRefl (synCnc (synC0)))
  have p0002 := @gEn0 (.cv x)
  have p0003 := @gEnsym (synC0) (.cv x)
  have p0004 := @gEl0c (.cv x)
  have p0005 :=
    @gN3bitr4ri (synWbr (.cv x) (synCen) (synC0)) (.classEq (.cv x) (synC0))
      (synWbr (synC0) (synCen) (.cv x)) (.classMem (.cv x) (synC0c)) p0002 p0003 p0004
  have p0006 :=
    @gEqabi (synWbr (synC0) (synCen) (.cv x)) x (synC0c) dv_cache_0003 p0005
  have p0007 :=
    @gN3eqtr4ri (synCec (synC0) (synCen))
      (.cab x (synWbr (synC0) (synCen) (.cv x))) (synCnc (synC0)) (synC0c) p0000
      p0001 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_n_0cnc`. -/
@[expose]
noncomputable def gN0cnc : Nominal.NPrf (.classMem (synC0c) (synCncs)) :=
  by
  have p0000 := @gDf0c2
  have p0001 := @gN0ex
  have p0002 := @gNcelncsi (synC0) p0001
  have p0003 := @gEqeltri (synC0c) (synCnc (synC0)) (synCncs) p0000 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_n_1cnc`. -/
@[expose]
noncomputable def gN1cnc : Nominal.NPrf (.classMem (synC1c) (synCncs)) :=
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
  have dv_cache_0001 : z ∉ ((synCsn (.cv y))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_y,
          not_false_eq_true])
  have dv_cache_0002 : z ∉ ((synCen)).fv :=
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
  have dv_cache_0004 : x ∉ ((synWbr (synCsn (.cv y)) (synCen) (.cv z))).fv :=
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
  have dv_cache_0005 : f ∉ ((synCsn (.cv y))).fv :=
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
  have dv_cache_0007 : x ∉ ((synCfv (.cv f) (.cv y))).fv :=
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
    x ∉ ((Wff.classEq (.cv z) (synCsn (synCfv (.cv f) (.cv y))))).fv :=
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
  have dv_cache_0009 : f ∉ ((synWex x (.classEq (.cv z) (synCsn (.cv x))))).fv :=
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
  have dv_cache_0010 : z ∉ ((synC1c)).fv :=
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
  have dv_cache_0011 : x ∉ ((synCsn (.cv y))).fv :=
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
  have dv_cache_0012 : x ∉ ((Wff.classEq (synC1c) (synCnc (synCsn (.cv y))))).fv :=
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
  have dv_cache_0013 : x ∉ ((synC1c)).fv :=
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
  have p0000 := @gDfec2 z (synCsn (.cv y)) (synCen) dv_cache_0001 dv_cache_0002
  have p0001 := (Nominal.classEqRefl (synCnc (synCsn (.cv y))))
  have p0002 := @gEl1c x (.cv z) dv_cache_0003
  have p0003 := @gVex y
  have p0004 := @gVex x
  have p0005 := @gEn2sn (.cv y) (.cv x) (synCvv) (synCvv)
  have p0006 :=
    @gMp2an (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCvv))
      (synWbr (synCsn (.cv y)) (synCen) (synCsn (.cv x))) p0003 p0004 p0005
  have p0007 := @gBreq2 (.cv z) (synCsn (.cv x)) (synCsn (.cv y)) (synCen)
  have p0008 :=
    @gMpbiri (.classEq (.cv z) (synCsn (.cv x)))
      (synWbr (synCsn (.cv y)) (synCen) (.cv z))
      (synWbr (synCsn (.cv y)) (synCen) (synCsn (.cv x))) p0006 p0007
  have p0009 :=
    @gExlimiv (.classEq (.cv z) (synCsn (.cv x)))
      (synWbr (synCsn (.cv y)) (synCen) (.cv z)) x dv_cache_0004 p0008
  have p0010 := @gBren (synCsn (.cv y)) (.cv z) f dv_cache_0005 dv_cache_0006
  have p0011 := @gF1of (synCsn (.cv y)) (.cv z) (.cv f)
  have p0012 := @gF1ofo (synCsn (.cv y)) (.cv z) (.cv f)
  have p0013 := @gForn (synCsn (.cv y)) (.cv z) (.cv f)
  have p0014 :=
    @gSyl (synWf1o (.cv f) (synCsn (.cv y)) (.cv z))
      (synWfo (.cv f) (synCsn (.cv y)) (.cv z)) (.classEq (synCrn (.cv f)) (.cv z))
      p0012 p0013
  have p0015 := @gFsn2 (.cv y) (.cv z) (.cv f) p0003
  have p0016 := @gRneq (.cv f) (synCsn (synCop (.cv y) (synCfv (.cv f) (.cv y))))
  have p0017 := @gRnsnop (.cv y) (synCfv (.cv f) (.cv y)) p0003
  have p0018 :=
    @gSyl6eq (.classEq (.cv f) (synCsn (synCop (.cv y) (synCfv (.cv f) (.cv y)))))
      (synCrn (.cv f)) (synCrn (synCsn (synCop (.cv y) (synCfv (.cv f) (.cv y)))))
      (synCsn (synCfv (.cv f) (.cv y))) p0016 p0017
  have p0019 :=
    @gEqeq1d (.classEq (.cv f) (synCsn (synCop (.cv y) (synCfv (.cv f) (.cv y)))))
      (synCrn (.cv f)) (synCsn (synCfv (.cv f) (.cv y))) (.cv z) p0018
  have p0020 := @gFvex (.cv y) (.cv f)
  have p0021 := @gSneq (.cv x) (synCfv (.cv f) (.cv y))
  have p0022 :=
    @gEqeq2d (.classEq (.cv x) (synCfv (.cv f) (.cv y))) (synCsn (.cv x))
      (synCsn (synCfv (.cv f) (.cv y))) (.cv z) p0021
  have p0023 :=
    @gSpcev (.classEq (.cv z) (synCsn (.cv x)))
      (.classEq (.cv z) (synCsn (synCfv (.cv f) (.cv y)))) x (synCfv (.cv f) (.cv y))
      dv_cache_0007 dv_cache_0008 p0020 p0022
  have p0024 :=
    @gEqcoms (synWex x (.classEq (.cv z) (synCsn (.cv x)))) (.cv z)
      (synCsn (synCfv (.cv f) (.cv y))) p0023
  have p0025 :=
    @gSyl6bi (.classEq (.cv f) (synCsn (synCop (.cv y) (synCfv (.cv f) (.cv y)))))
      (.classEq (synCrn (.cv f)) (.cv z))
      (.classEq (synCsn (synCfv (.cv f) (.cv y))) (.cv z))
      (synWex x (.classEq (.cv z) (synCsn (.cv x)))) p0019 p0024
  have p0026 :=
    @gAdantl (.classEq (.cv f) (synCsn (synCop (.cv y) (synCfv (.cv f) (.cv y)))))
      (.imp (.classEq (synCrn (.cv f)) (.cv z))
        (synWex x (.classEq (.cv z) (synCsn (.cv x)))))
      (.classMem (synCfv (.cv f) (.cv y)) (.cv z)) p0025
  have p0027 :=
    @gSylbi (synWf (.cv f) (synCsn (.cv y)) (.cv z))
      (synWa (.classMem (synCfv (.cv f) (.cv y)) (.cv z))
        (.classEq (.cv f) (synCsn (synCop (.cv y) (synCfv (.cv f) (.cv y))))))
      (.imp (.classEq (synCrn (.cv f)) (.cv z))
        (synWex x (.classEq (.cv z) (synCsn (.cv x)))))
      p0015 p0026
  have p0028 :=
    @gSylc (synWf1o (.cv f) (synCsn (.cv y)) (.cv z))
      (synWf (.cv f) (synCsn (.cv y)) (.cv z)) (.classEq (synCrn (.cv f)) (.cv z))
      (synWex x (.classEq (.cv z) (synCsn (.cv x)))) p0011 p0014 p0027
  have p0029 :=
    @gExlimiv (synWf1o (.cv f) (synCsn (.cv y)) (.cv z))
      (synWex x (.classEq (.cv z) (synCsn (.cv x)))) f dv_cache_0009 p0028
  have p0030 :=
    @gSylbi (synWbr (synCsn (.cv y)) (synCen) (.cv z))
      (synWex f (synWf1o (.cv f) (synCsn (.cv y)) (.cv z)))
      (synWex x (.classEq (.cv z) (synCsn (.cv x)))) p0010 p0029
  have p0031 :=
    @gImpbii (synWex x (.classEq (.cv z) (synCsn (.cv x))))
      (synWbr (synCsn (.cv y)) (synCen) (.cv z)) p0009 p0030
  have p0032 :=
    @gBitri (.classMem (.cv z) (synC1c))
      (synWex x (.classEq (.cv z) (synCsn (.cv x))))
      (synWbr (synCsn (.cv y)) (synCen) (.cv z)) p0002 p0031
  have p0033 :=
    @gEqabi (synWbr (synCsn (.cv y)) (synCen) (.cv z)) z (synC1c) dv_cache_0010 p0032
  have p0034 :=
    @gN3eqtr4ri (synCec (synCsn (.cv y)) (synCen))
      (.cab z (synWbr (synCsn (.cv y)) (synCen) (.cv z))) (synCnc (synCsn (.cv y)))
      (synC1c) p0000 p0001 p0033
  have p0035 := @gSnex (.cv y)
  have p0036 := @gNceq (.cv x) (synCsn (.cv y))
  have p0037 :=
    @gEqeq2d (.classEq (.cv x) (synCsn (.cv y))) (synCnc (.cv x))
      (synCnc (synCsn (.cv y))) (synC1c) p0036
  have p0038 :=
    @gSpcev (.classEq (synC1c) (synCnc (.cv x)))
      (.classEq (synC1c) (synCnc (synCsn (.cv y)))) x (synCsn (.cv y)) dv_cache_0011
      dv_cache_0012 p0035 p0037
  have p0039 := Nominal.mp p0034 p0038
  have p0040 := @gElncs x (synC1c) dv_cache_0013
  have p0041 :=
    @gMpbir (.classMem (synC1c) (synCncs))
      (synWex x (.classEq (synC1c) (synCnc (.cv x)))) p0039 p0040
  exact p0041

/-- Checked nominal proof certificate identified upstream as `g_df1c3`. -/
@[expose]
noncomputable def gDf1c3 (A : Class)
    (hyp_df1c3_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classEq (synC1c) (synCnc (synCsn A))) :=
  by
  have p0000 := @gSnel1c A hyp_df1c3_1
  have p0001 := @gN1cnc
  have p0002 := @gNcseqnc (synC1c) (synCsn A)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gMpbir (.classEq (synC1c) (synCnc (synCsn A))) (.classMem (synCsn A) (synC1c))
      p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ncaddccl`. -/
@[expose]
noncomputable def gNcaddccl (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
        (.classMem (synCplc A B) (synCncs))) :=
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
  have dv_cache_0003 : y ∉ ((Wff.classEq A (synCnc (.cv x)))).fv :=
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
  have dv_cache_0004 : x ∉ ((Wff.classEq B (synCnc (.cv y)))).fv :=
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
      ((synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
          (synCxp (.cv y) (synCsn (synC0))))).fv :=
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
      ((Wff.classEq (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
            (synCnc (synCxp (.cv y) (synCsn (synC0))))) (synCnc
            (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
              (synCxp (.cv y) (synCsn (synC0))))))).fv :=
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
      ((synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0)))))).fv :=
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
  have dv_cache_0008 : x ∉ ((Wff.classMem (synCplc A B) (synCncs))).fv :=
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
  have dv_cache_0009 : y ∉ ((Wff.classMem (synCplc A B) (synCncs))).fv :=
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
  have p0000 := @gElncs x A dv_cache_0001
  have p0001 := @gElncs y B dv_cache_0002
  have p0002 :=
    @gEeanv (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0003 := @gVex x
  have p0004 := @gN0ex
  have p0005 := @gComplex (synC0) p0004
  have p0006 := @gXpsnen (.cv x) (synCcompl (synC0)) p0003 p0005
  have p0007 := @gSnex (synCcompl (synC0))
  have p0008 := @gXpex (.cv x) (synCsn (synCcompl (synC0))) p0003 p0007
  have p0009 := @gEqnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))) (.cv x) p0008
  have p0010 :=
    @gMpbir
      (.classEq (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))) (synCnc (.cv x)))
      (synWbr (synCxp (.cv x) (synCsn (synCcompl (synC0)))) (synCen) (.cv x)) p0006
      p0009
  have p0011 :=
    @gEqcomi (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
      (synCnc (.cv x)) p0010
  have p0012 :=
    @gEqtr A (synCnc (.cv x))
      (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
  have p0013 :=
    @gMpan2 (.classEq A (synCnc (.cv x)))
      (.classEq (synCnc (.cv x)) (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
      (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))) p0011 p0012
  have p0014 := @gVex y
  have p0016 := @gXpsnen (.cv y) (synC0) p0014 p0004
  have p0017 := @gSnex (synC0)
  have p0018 := @gXpex (.cv y) (synCsn (synC0)) p0014 p0017
  have p0019 := @gEqnc (synCxp (.cv y) (synCsn (synC0))) (.cv y) p0018
  have p0020 :=
    @gMpbir (.classEq (synCnc (synCxp (.cv y) (synCsn (synC0)))) (synCnc (.cv y)))
      (synWbr (synCxp (.cv y) (synCsn (synC0))) (synCen) (.cv y)) p0016 p0019
  have p0021 :=
    @gEqcomi (synCnc (synCxp (.cv y) (synCsn (synC0)))) (synCnc (.cv y)) p0020
  have p0022 := @gEqtr B (synCnc (.cv y)) (synCnc (synCxp (.cv y) (synCsn (synC0))))
  have p0023 :=
    @gMpan2 (.classEq B (synCnc (.cv y)))
      (.classEq (synCnc (.cv y)) (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0))))) p0021 p0022
  have p0024 :=
    @gAddceq12 A B (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
      (synCnc (synCxp (.cv y) (synCsn (synC0))))
  have p0025 := @gNecompl (synC0)
  have p0026 := @gXpnedisj (.cv x) (.cv y) (synCcompl (synC0)) (synC0) p0005 p0025
  have p0027 :=
    @gNcdisjun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
      (synCxp (.cv y) (synCsn (synC0))) p0008 p0018
  have p0028 := Nominal.mp p0026 p0027
  have p0029 :=
    @gEqcomi
      (synCnc (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
          (synCxp (.cv y) (synCsn (synC0)))))
      (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      p0028
  have p0030 :=
    @gUnex (synCxp (.cv x) (synCsn (synCcompl (synC0))))
      (synCxp (.cv y) (synCsn (synC0))) p0008 p0018
  have p0031 :=
    @gNceq (.cv z)
      (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
        (synCxp (.cv y) (synCsn (synC0))))
  have p0032 :=
    @gEqeq2d
      (.classEq (.cv z) (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
          (synCxp (.cv y) (synCsn (synC0)))))
      (synCnc (.cv z))
      (synCnc (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
          (synCxp (.cv y) (synCsn (synC0)))))
      (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      p0031
  have p0033 :=
    @gSpcev
      (.classEq (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0))))) (synCnc (.cv z)))
      (.classEq (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0))))) (synCnc
          (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
            (synCxp (.cv y) (synCsn (synC0))))))
      z
      (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
        (synCxp (.cv y) (synCsn (synC0))))
      dv_cache_0005 dv_cache_0006 p0030 p0032
  have p0034 := Nominal.mp p0029 p0033
  have p0035 :=
    @gElncs z
      (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      dv_cache_0007
  have p0036 :=
    @gMpbir
      (.classMem (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0))))) (synCncs))
      (synWex z (.classEq (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
            (synCnc (synCxp (.cv y) (synCsn (synC0))))) (synCnc (.cv z))))
      p0034 p0035
  have p0037 :=
    @gSyl6eqel
      (synWa (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
        (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (synCplc A B)
      (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      (synCncs) p0024 p0036
  have p0038 :=
    @gSyl2an (.classEq A (synCnc (.cv x)))
      (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
      (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      (.classMem (synCplc A B) (synCncs)) (.classEq B (synCnc (.cv y))) p0013 p0023
      p0037
  have p0039 :=
    @gExlimivv (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))
      (.classMem (synCplc A B) (synCncs)) x y dv_cache_0008 dv_cache_0009 p0038
  have p0040 :=
    @gSylbir
      (synWa (synWex x (.classEq A (synCnc (.cv x))))
        (synWex y (.classEq B (synCnc (.cv y)))))
      (synWex x (synWex y
          (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))))
      (.classMem (synCplc A B) (synCncs)) p0002 p0039
  have p0041 :=
    @gSyl2anb (.classMem A (synCncs)) (synWex x (.classEq A (synCnc (.cv x))))
      (synWex y (.classEq B (synCnc (.cv y)))) (.classMem (synCplc A B) (synCncs))
      (.classMem B (synCncs)) p0000 p0001 p0040
  exact p0041

/-- Checked nominal proof certificate identified upstream as `g_peano2nc`. -/
@[expose]
noncomputable def gPeano2nc (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCncs)) (.classMem (synCplc A (synC1c)) (synCncs))) :=
  by
  have p0000 := @gN1cnc
  have p0001 := @gNcaddccl A (synC1c)
  have p0002 :=
    @gMpan2 (.classMem A (synCncs)) (.classMem (synC1c) (synCncs))
      (.classMem (synCplc A (synC1c)) (synCncs)) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_nnnc`. -/
@[expose]
noncomputable def gNnnc (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCnnc)) (.classMem A (synCncs))) :=
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
  have dv_cache_0001 : x ∉ ((synCncs)).fv := by
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
  have dv_cache_0003 : x ∉ ((Wff.classMem (.cv n) (synCncs))).fv :=
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
  have dv_cache_0004 : n ∉ ((Wff.classMem (.cv x) (synCncs))).fv :=
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
  have dv_cache_0005 : x ∉ ((Wff.classMem (synC0c) (synCncs))).fv :=
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
  have dv_cache_0006 : x ∉ ((Wff.classMem A (synCncs))).fv :=
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
  have dv_cache_0007 : x ∉ ((Wff.classMem (synCplc (.cv n) (synC1c)) (synCncs))).fv :=
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
  have p0000 := @gAbid2 x (synCncs) dv_cache_0001
  have p0001 := @gNcsex
  have p0002 :=
    @gEqeltri (.cab x (.classMem (.cv x) (synCncs))) (synCncs) (synCvv) p0000 p0001
  have p0003 := @gEleq1 (.cv x) (synC0c) (synCncs)
  have p0004 := @gEleq1 (.cv x) (.cv n) (synCncs)
  have p0005 := @gEleq1 (.cv x) (synCplc (.cv n) (synC1c)) (synCncs)
  have p0006 := @gEleq1 (.cv x) A (synCncs)
  have p0007 := @gN0cnc
  have p0008 := @gPeano2nc (.cv n)
  have p0009 :=
    @gA1i
      (.imp (.classMem (.cv n) (synCncs)) (.classMem (synCplc (.cv n) (synC1c)) (synCncs)))
      (.classMem (.cv n) (synCnnc)) p0008
  have p0010_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq x n)
        (synWb (.classMem (.cv x) (synCncs)) (.classMem (.cv n) (synCncs)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCncs synCqs synWrex synWex synWa synCec synCima synCsn
          synCvv synCen synCopab
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0010 :=
    @gFinds (.classMem (.cv x) (synCncs)) (.classMem (synC0c) (synCncs))
      (.classMem (.cv n) (synCncs)) (.classMem (synCplc (.cv n) (synC1c)) (synCncs))
      (.classMem A (synCncs)) x n A dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 p0002 p0003
      p0010_e02_recanon p0005 p0006 p0007 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_ncdisjeq`. -/
@[expose]
noncomputable def gNcdisjeq (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
        (synWo (.classEq (synCin A B) (synC0)) (.classEq A B))) :=
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
  have dv_cache_0003 : y ∉ ((Wff.classEq A (synCnc (.cv x)))).fv :=
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
  have dv_cache_0004 : x ∉ ((Wff.classEq B (synCnc (.cv y)))).fv :=
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
    x ∉ ((synWo (.classEq (synCin A B) (synC0)) (.classEq A B))).fv :=
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
    y ∉ ((synWo (.classEq (synCin A B) (synC0)) (.classEq A B))).fv :=
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
  have p0000 := @gElncs x A dv_cache_0001
  have p0001 := @gElncs y B dv_cache_0002
  have p0002 :=
    @gAnbi12i (.classMem A (synCncs)) (synWex x (.classEq A (synCnc (.cv x))))
      (.classMem B (synCncs)) (synWex y (.classEq B (synCnc (.cv y)))) p0000 p0001
  have p0003 :=
    @gEeanv (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))) x y
      dv_cache_0003 dv_cache_0004
  have p0004 :=
    @gBitr4i (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWa (synWex x (.classEq A (synCnc (.cv x))))
        (synWex y (.classEq B (synCnc (.cv y)))))
      (synWex x (synWex y
          (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))))
      p0002 p0003
  have p0005 := @gEner
  have p0006 := @gErdisj (.cv x) (.cv y) (synCen)
  have p0007 := Nominal.mp p0005 p0006
  have p0008 := (Nominal.classEqRefl (synCnc (.cv x)))
  have p0009 := @gEqtr A (synCnc (.cv x)) (synCec (.cv x) (synCen))
  have p0010 :=
    @gMpan2 (.classEq A (synCnc (.cv x)))
      (.classEq (synCnc (.cv x)) (synCec (.cv x) (synCen)))
      (.classEq A (synCec (.cv x) (synCen))) p0008 p0009
  have p0011 := (Nominal.classEqRefl (synCnc (.cv y)))
  have p0012 := @gEqtr B (synCnc (.cv y)) (synCec (.cv y) (synCen))
  have p0013 :=
    @gMpan2 (.classEq B (synCnc (.cv y)))
      (.classEq (synCnc (.cv y)) (synCec (.cv y) (synCen)))
      (.classEq B (synCec (.cv y) (synCen))) p0011 p0012
  have p0014 := @gEqeq12 A (synCec (.cv x) (synCen)) B (synCec (.cv y) (synCen))
  have p0015 := @gIneq12 A (synCec (.cv x) (synCen)) B (synCec (.cv y) (synCen))
  have p0016 :=
    @gEqeq1d
      (synWa (.classEq A (synCec (.cv x) (synCen))) (.classEq B (synCec (.cv y) (synCen))))
      (synCin A B) (synCin (synCec (.cv x) (synCen)) (synCec (.cv y) (synCen)))
      (synC0) p0015
  have p0017 :=
    @gOrbi12d
      (synWa (.classEq A (synCec (.cv x) (synCen))) (.classEq B (synCec (.cv y) (synCen))))
      (.classEq A B) (.classEq (synCec (.cv x) (synCen)) (synCec (.cv y) (synCen)))
      (.classEq (synCin A B) (synC0))
      (.classEq (synCin (synCec (.cv x) (synCen)) (synCec (.cv y) (synCen))) (synC0))
      p0014 p0016
  have p0018 :=
    @gSyl2an (.classEq A (synCnc (.cv x))) (.classEq A (synCec (.cv x) (synCen)))
      (.classEq B (synCec (.cv y) (synCen)))
      (synWb (synWo (.classEq A B) (.classEq (synCin A B) (synC0)))
        (synWo (.classEq (synCec (.cv x) (synCen)) (synCec (.cv y) (synCen)))
          (.classEq (synCin (synCec (.cv x) (synCen)) (synCec (.cv y) (synCen)))
            (synC0))))
      (.classEq B (synCnc (.cv y))) p0010 p0013 p0017
  have p0019 :=
    @gMpbiri (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))
      (synWo (.classEq A B) (.classEq (synCin A B) (synC0)))
      (synWo (.classEq (synCec (.cv x) (synCen)) (synCec (.cv y) (synCen)))
        (.classEq (synCin (synCec (.cv x) (synCen)) (synCec (.cv y) (synCen))) (synC0)))
      p0007 p0018
  have p0020 :=
    @gOrcomd (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))
      (.classEq A B) (.classEq (synCin A B) (synC0)) p0019
  have p0021 :=
    @gExlimivv (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))
      (synWo (.classEq (synCin A B) (synC0)) (.classEq A B)) x y dv_cache_0005
      dv_cache_0006 p0020
  have p0022 :=
    @gSylbi (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWex x (synWex y
          (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))))
      (synWo (.classEq (synCin A B) (synC0)) (.classEq A B)) p0004 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_nceleq`. -/
@[expose]
noncomputable def gNceleq (A : Class) (B : Class) (X : Class) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
          (synWa (.classMem X A) (.classMem X B))) (.classEq A B)) :=
  by
  have p0000 := @gElin X A B
  have p0001 := @gN0i (synCin A B) X
  have p0002 :=
    @gSylbir (synWa (.classMem X A) (.classMem X B)) (.classMem X (synCin A B))
      (.neg (.classEq (synCin A B) (synC0))) p0000 p0001
  have p0003 := @gNcdisjeq A B
  have p0004 :=
    @gOrd (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (.classEq (synCin A B) (synC0)) (.classEq A B) p0003
  have p0005 :=
    @gSyl5 (synWa (.classMem X A) (.classMem X B))
      (.neg (.classEq (synCin A B) (synC0)))
      (synWa (.classMem A (synCncs)) (.classMem B (synCncs))) (.classEq A B) p0002
      p0004
  have p0006 :=
    @gImp (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWa (.classMem X A) (.classMem X B)) (.classEq A B) p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ncpw1`. -/
@[expose]
noncomputable def gNcpw1 (A : Class) (B : Class)
    (hyp_ncpw1_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (synWb (.classEq (synCnc A) (synCnc B))
        (.classEq (synCnc (synCpw1 A)) (synCnc (synCpw1 B)))) :=
  by
  have p0000 := @gEnpw1 A B
  have p0001 := @gEqnc A B hyp_ncpw1_1
  have p0002 := @gPw1ex A hyp_ncpw1_1
  have p0003 := @gEqnc (synCpw1 A) (synCpw1 B) p0002
  have p0004 :=
    @gN3bitr4i (synWbr A (synCen) B) (synWbr (synCpw1 A) (synCen) (synCpw1 B))
      (.classEq (synCnc A) (synCnc B))
      (.classEq (synCnc (synCpw1 A)) (synCnc (synCpw1 B))) p0000 p0001 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_ncpwpw1`. -/
@[expose]
noncomputable def gNcpwpw1 (A : Class)
    (hyp_ncpwpw1_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf
      (.classEq (synCnc (synCpw (synCpw1 A))) (synCnc (synCpw1 (synCpw A)))) :=
  by
  have p0000 := @gEnpw1pw A hyp_ncpwpw1_1
  have p0001 := @gEnsym (synCpw1 (synCpw A)) (synCpw (synCpw1 A))
  have p0002 :=
    @gMpbi (synWbr (synCpw1 (synCpw A)) (synCen) (synCpw (synCpw1 A)))
      (synWbr (synCpw (synCpw1 A)) (synCen) (synCpw1 (synCpw A))) p0000 p0001
  have p0003 := @gPw1ex A hyp_ncpwpw1_1
  have p0004 := @gPwex (synCpw1 A) p0003
  have p0005 := @gEqnc (synCpw (synCpw1 A)) (synCpw1 (synCpw A)) p0004
  have p0006 :=
    @gMpbir (.classEq (synCnc (synCpw (synCpw1 A))) (synCnc (synCpw1 (synCpw A))))
      (synWbr (synCpw (synCpw1 A)) (synCen) (synCpw1 (synCpw A))) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_ncpw1c`. -/
@[expose]
noncomputable def gNcpw1c :
    Nominal.NPrf (.classEq (synCnc (synCpw (synC1c))) (synCnc (synC1c))) :=
  by
  have p0000 := @gVvex
  have p0001 := @gNcpwpw1 (synCvv) p0000
  have p0002 := @gDf1c2
  have p0003 := @gPweqi (synC1c) (synCpw1 (synCvv)) p0002
  have p0004 := @gNceqi (synCpw (synC1c)) (synCpw (synCpw1 (synCvv))) p0003
  have p0006 := @gPwv
  have p0007 := @gPw1eq (synCpw (synCvv)) (synCvv)
  have p0008 := Nominal.mp p0006 p0007
  have p0009 :=
    @gEqtr4i (synC1c) (synCpw1 (synCvv)) (synCpw1 (synCpw (synCvv))) p0002 p0008
  have p0010 := @gNceqi (synC1c) (synCpw1 (synCpw (synCvv))) p0009
  have p0011 :=
    @gN3eqtr4i (synCnc (synCpw (synCpw1 (synCvv))))
      (synCnc (synCpw1 (synCpw (synCvv)))) (synCnc (synCpw (synC1c)))
      (synCnc (synC1c)) p0001 p0004 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_n_1p1e2c`. -/
@[expose]
noncomputable def gN1p1e2c :
    Nominal.NPrf (.classEq (synCplc (synC1c) (synC1c)) (synC2c)) :=
  by
  have p0000 := @gN0ex
  have p0001 := @gN0i (synCvv) (synC0)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gVvex
  have p0004 := @gElsnc (synCvv) (synC0) p0003
  have p0005 :=
    @gMtbir (.classMem (synCvv) (synCsn (synC0))) (.classEq (synCvv) (synC0)) p0002
      p0004
  have p0006 := @gDisjsn (synCsn (synC0)) (synCvv)
  have p0007 :=
    @gMpbir (.classEq (synCin (synCsn (synC0)) (synCsn (synCvv))) (synC0))
      (.neg (.classMem (synCvv) (synCsn (synC0)))) p0005 p0006
  have p0008 := @gSnex (synC0)
  have p0009 := @gSnex (synCvv)
  have p0010 := @gNcdisjun (synCsn (synC0)) (synCsn (synCvv)) p0008 p0009
  have p0011 := Nominal.mp p0007 p0010
  have p0012 := (Nominal.classEqRefl (synC2c))
  have p0013 := (Nominal.classEqRefl (synCpr (synC0) (synCvv)))
  have p0014 :=
    @gNceqi (synCpr (synC0) (synCvv)) (synCun (synCsn (synC0)) (synCsn (synCvv)))
      p0013
  have p0015 :=
    @gEqtri (synC2c) (synCnc (synCpr (synC0) (synCvv)))
      (synCnc (synCun (synCsn (synC0)) (synCsn (synCvv)))) p0012 p0014
  have p0017 := @gDf1c3 (synC0) p0000
  have p0019 := @gDf1c3 (synCvv) p0003
  have p0020 :=
    @gAddceq12i (synC1c) (synCnc (synCsn (synC0))) (synC1c)
      (synCnc (synCsn (synCvv))) p0017 p0019
  have p0021 :=
    @gN3eqtr4ri (synCnc (synCun (synCsn (synC0)) (synCsn (synCvv))))
      (synCplc (synCnc (synCsn (synC0))) (synCnc (synCsn (synCvv)))) (synC2c)
      (synCplc (synC1c) (synC1c)) p0011 p0015 p0020
  exact p0021

/-- Checked nominal proof certificate identified upstream as `g_tcex`. -/
@[expose]
noncomputable def gTcex (A : Class) : Nominal.NPrf (.classMem (synCtc A) (synCvv)) :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTc y A x
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 :=
    @gIotaex
      (synWa (.classMem (.cv x) (synCncs))
        (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))
      x
  have p0002 :=
    @gEqeltri (synCtc A)
      (synCio x (synWa (.classMem (.cv x) (synCncs))
          (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))))
      (synCvv) p0000 p0001
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

/-- Checked nominal proof certificate identified upstream as `g_tceq`. -/
@[expose]
noncomputable def gTceq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCtc A) (synCtc B))) :=
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
    @gRexeq (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))) y A B dv_cache_0001
      dv_cache_0002
  have p0001 :=
    @gAnbi2d (.classEq A B)
      (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))
      (synWrex y B (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))
      (.classMem (.cv x) (synCncs)) p0000
  have p0002 :=
    @gIotabidv (.classEq A B)
      (synWa (.classMem (.cv x) (synCncs))
        (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))
      (synWa (.classMem (.cv x) (synCncs))
        (synWrex y B (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))
      x dv_cache_0003 p0001
  have p0003 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTc y A x
      dv_cache_0004 dv_cache_0001 dv_cache_0005
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTc y B x
      dv_cache_0006 dv_cache_0002 dv_cache_0005
  have p0005 :=
    @gN3eqtr4g (.classEq A B)
      (synCio x (synWa (.classMem (.cv x) (synCncs))
          (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))))
      (synCio x (synWa (.classMem (.cv x) (synCncs))
          (synWrex y B (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))))
      (synCtc A) (synCtc B) p0002 p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_ncspw1eu`. -/
@[expose]
noncomputable def gNcspw1eu (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.imp (.classMem A (synCncs)) (synWreu x (synCncs)
          (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))) :=
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
  have dv_cache_0002 : x ∉ ((synCnc (synCpw1 (.cv y)))).fv :=
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
  have dv_cache_0003 : x ∉ ((synCncs)).fv :=
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
    x ∉ ((Wff.classEq (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv y))))).fv :=
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
  have dv_cache_0005 : y ∉ ((Wff.classMem A (synCncs))).fv :=
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
  have dv_cache_0006 : y ∉ ((synCncs)).fv :=
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
  have dv_cache_0010 : w ∉ ((Wff.classEq (.cv x) (synCnc (synCpw1 (.cv y))))).fv :=
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
  have dv_cache_0011 : y ∉ ((Wff.classEq (.cv z) (synCnc (synCpw1 (.cv w))))).fv :=
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
      ((synWa (.classMem A (synCncs))
          (synWa (.classMem (.cv x) (synCncs)) (.classMem (.cv z) (synCncs))))).fv :=
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
      ((synWa (.classMem A (synCncs))
          (synWa (.classMem (.cv x) (synCncs)) (.classMem (.cv z) (synCncs))))).fv :=
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
  have dv_cache_0017 : z ∉ ((synCncs)).fv :=
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
  have dv_cache_0018 : x ∉ ((Wff.classMem A (synCncs))).fv :=
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
  have dv_cache_0019 : z ∉ ((Wff.classMem A (synCncs))).fv :=
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
  have dv_cache_0021 : w ∉ ((Wff.classEq (.cv z) (synCnc (synCpw1 (.cv y))))).fv :=
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
    z ∉ ((synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))).fv :=
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
    x ∉ ((synWrex w A (.classEq (.cv z) (synCnc (synCpw1 (.cv w)))))).fv :=
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
  have p0000 := @gNulnnc
  have p0001 := @gEleq1 A (synC0) (synCncs)
  have p0002 :=
    @gMtbiri (.classEq A (synC0)) (.classMem A (synCncs))
      (.classMem (synC0) (synCncs)) p0000 p0001
  have p0003 := @gNecon2ai (.classMem A (synCncs)) A (synC0) p0002
  have p0004 := @gN0 y A dv_cache_0001
  have p0005 :=
    @gSylib (.classMem A (synCncs)) (synWne A (synC0))
      (synWex y (.classMem (.cv y) A)) p0003 p0004
  have p0006 := @gVex y
  have p0007 := @gPw1ex (.cv y) p0006
  have p0008 := @gNcelncsi (synCpw1 (.cv y)) p0007
  have p0009 := @gEqid (synCnc (synCpw1 (.cv y)))
  have p0010 := @gEqeq1 (.cv x) (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv y)))
  have p0011 :=
    @gRspcev (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))
      (.classEq (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv y)))) x
      (synCnc (synCpw1 (.cv y))) (synCncs) dv_cache_0002 dv_cache_0003 dv_cache_0004
      p0010
  have p0012 :=
    @gMp2an (.classMem (synCnc (synCpw1 (.cv y))) (synCncs))
      (.classEq (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv y))))
      (synWrex x (synCncs) (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))) p0008 p0009
      p0011
  have p0013 :=
    @gJctr (.classMem (.cv y) A)
      (synWrex x (synCncs) (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))) p0012
  have p0014 :=
    @gA1i
      (.imp (.classMem (.cv y) A) (synWa (.classMem (.cv y) A)
          (synWrex x (synCncs) (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))))
      (.classMem A (synCncs)) p0013
  have p0015 :=
    @gEximdv (.classMem A (synCncs)) (.classMem (.cv y) A)
      (synWa (.classMem (.cv y) A)
        (synWrex x (synCncs) (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))
      y dv_cache_0005 p0014
  have p0016 :=
    @gMpd (.classMem A (synCncs)) (synWex y (.classMem (.cv y) A))
      (synWex y (synWa (.classMem (.cv y) A)
          (synWrex x (synCncs) (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))))
      p0005 p0015
  have p0017 :=
    @gRexcom (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))) x y (synCncs) A
      dv_cache_0006 dv_cache_0007 dv_cache_0008
  have p0018 :=
    (Nominal.biimpRefl (synWrex y A
        (synWrex x (synCncs) (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))))
  have p0019 :=
    @gBitri
      (synWrex x (synCncs) (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))
      (synWrex y A (synWrex x (synCncs) (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))
      (synWex y (synWa (.classMem (.cv y) A)
          (synWrex x (synCncs) (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))))
      p0017 p0018
  have p0020 :=
    @gSylibr (.classMem A (synCncs))
      (synWex y (synWa (.classMem (.cv y) A)
          (synWrex x (synCncs) (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))))
      (synWrex x (synCncs) (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))
      p0016 p0019
  have p0021 :=
    @gReeanv (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))
      (.classEq (.cv z) (synCnc (synCpw1 (.cv w)))) y w A A dv_cache_0009 dv_cache_0001
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0022 := @gNcseqnc A (.cv y)
  have p0023 :=
    @gBiimpar (.classMem A (synCncs)) (.classEq A (synCnc (.cv y)))
      (.classMem (.cv y) A) p0022
  have p0024 :=
    @gAdantrr (.classMem A (synCncs)) (.classMem (.cv y) A)
      (.classEq A (synCnc (.cv y))) (.classMem (.cv w) A) p0023
  have p0025 := @gNcseqnc A (.cv w)
  have p0026 :=
    @gBiimpar (.classMem A (synCncs)) (.classEq A (synCnc (.cv w)))
      (.classMem (.cv w) A) p0025
  have p0027 :=
    @gAdantrl (.classMem A (synCncs)) (.classMem (.cv w) A)
      (.classEq A (synCnc (.cv w))) (.classMem (.cv y) A) p0026
  have p0028 :=
    @gEqtr3d
      (synWa (.classMem A (synCncs)) (synWa (.classMem (.cv y) A) (.classMem (.cv w) A)))
      A (synCnc (.cv y)) (synCnc (.cv w)) p0024 p0027
  have p0029 := @gNcpw1 (.cv y) (.cv w) p0006
  have p0030 :=
    @gSylib
      (synWa (.classMem A (synCncs)) (synWa (.classMem (.cv y) A) (.classMem (.cv w) A)))
      (.classEq (synCnc (.cv y)) (synCnc (.cv w)))
      (.classEq (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv w)))) p0028 p0029
  have p0031 :=
    @gN3adant2 (.classMem A (synCncs))
      (synWa (.classMem (.cv y) A) (.classMem (.cv w) A))
      (.classEq (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv w))))
      (synWa (.classMem (.cv x) (synCncs)) (.classMem (.cv z) (synCncs))) p0030
  have p0032 := @gEqeq2 (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv w))) (.cv x)
  have p0033 :=
    @gAnbi1d (.classEq (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv w))))
      (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))
      (.classEq (.cv x) (synCnc (synCpw1 (.cv w))))
      (.classEq (.cv z) (synCnc (synCpw1 (.cv w)))) p0032
  have p0034 := @gEqtr3 (.cv x) (.cv z) (synCnc (synCpw1 (.cv w)))
  have p0035_e01_recanon :
    Nominal.NPrf
      (.imp (synWa (.classEq (.cv x) (synCnc (synCpw1 (.cv w))))
          (.classEq (.cv z) (synCnc (synCpw1 (.cv w))))) (.objEq x z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCnc synCec synCima synWrex synWex synWbr synCop synCun
          synCnin synWnan synCcompl synCsn synCen synCopab synCpw1 synCin synCpw
          synWss synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0034
  have p0035 :=
    @gSyl6bi (.classEq (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv w))))
      (synWa (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))
        (.classEq (.cv z) (synCnc (synCpw1 (.cv w)))))
      (synWa (.classEq (.cv x) (synCnc (synCpw1 (.cv w))))
        (.classEq (.cv z) (synCnc (synCpw1 (.cv w)))))
      (.objEq x z) p0033 p0035_e01_recanon
  have p0036 :=
    @gSyl
      (synW3a (.classMem A (synCncs))
        (synWa (.classMem (.cv x) (synCncs)) (.classMem (.cv z) (synCncs)))
        (synWa (.classMem (.cv y) A) (.classMem (.cv w) A)))
      (.classEq (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv w))))
      (.imp (synWa (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))
          (.classEq (.cv z) (synCnc (synCpw1 (.cv w))))) (.objEq x z))
      p0031 p0035
  have p0037 :=
    @gN3expa (.classMem A (synCncs))
      (synWa (.classMem (.cv x) (synCncs)) (.classMem (.cv z) (synCncs)))
      (synWa (.classMem (.cv y) A) (.classMem (.cv w) A))
      (.imp (synWa (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))
          (.classEq (.cv z) (synCnc (synCpw1 (.cv w))))) (.objEq x z))
      p0036
  have p0038 :=
    @gRexlimdvva
      (synWa (.classMem A (synCncs))
        (synWa (.classMem (.cv x) (synCncs)) (.classMem (.cv z) (synCncs))))
      (synWa (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))
        (.classEq (.cv z) (synCnc (synCpw1 (.cv w)))))
      (.objEq x z) y w A A dv_cache_0009 dv_cache_0013 dv_cache_0014 dv_cache_0015
      dv_cache_0016 dv_cache_0012 p0037
  have p0039 :=
    @gSyl5bir
      (synWa (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))
        (synWrex w A (.classEq (.cv z) (synCnc (synCpw1 (.cv w))))))
      (synWrex y A (synWrex w A (synWa (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))
            (.classEq (.cv z) (synCnc (synCpw1 (.cv w)))))))
      (synWa (.classMem A (synCncs))
        (synWa (.classMem (.cv x) (synCncs)) (.classMem (.cv z) (synCncs))))
      (.objEq x z) p0021 p0038
  have p0040 :=
    @gRalrimivva (.classMem A (synCncs))
      (.imp (synWa (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))
          (synWrex w A (.classEq (.cv z) (synCnc (synCpw1 (.cv w)))))) (.objEq x z))
      x z (synCncs) (synCncs) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020
      p0039
  have p0041 := @gEqeq1 (.cv x) (.cv z) (synCnc (synCpw1 (.cv y)))
  have p0042_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (synWb (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))
          (.classEq (.cv z) (synCnc (synCpw1 (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCnc synCec synCima synWrex synWex synWa synWbr synCop
          synCun synCnin synWnan synCcompl synCsn synCen synCopab synCpw1 synCin
          synCpw synWss synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0041
  have p0042 :=
    @gRexbidv (.objEq x z) (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))
      (.classEq (.cv z) (synCnc (synCpw1 (.cv y)))) y A dv_cache_0013 p0042_e00_recanon
  have p0043 := @gPw1eq (.cv y) (.cv w)
  have p0044_e00_recanon :
    Nominal.NPrf (.imp (.objEq y w) (.classEq (synCpw1 (.cv y)) (synCpw1 (.cv w)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw1 synCin synCcompl synCnin synWnan synWa synCpw synWss
          synC1c synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0043
  have p0044 :=
    @gNceqd (.objEq y w) (synCpw1 (.cv y)) (synCpw1 (.cv w)) p0044_e00_recanon
  have p0045 :=
    @gEqeq2d (.objEq y w) (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 (.cv w)))
      (.cv z) p0044
  have p0046 :=
    @gCbvrexv (.classEq (.cv z) (synCnc (synCpw1 (.cv y))))
      (.classEq (.cv z) (synCnc (synCpw1 (.cv w)))) y w A dv_cache_0001 dv_cache_0009
      dv_cache_0021 dv_cache_0011 p0045
  have p0047 :=
    @gSyl6bb (.objEq x z) (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))
      (synWrex y A (.classEq (.cv z) (synCnc (synCpw1 (.cv y)))))
      (synWrex w A (.classEq (.cv z) (synCnc (synCpw1 (.cv w))))) p0042 p0046
  have p0048 :=
    @gReu4 (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))
      (synWrex w A (.classEq (.cv z) (synCnc (synCpw1 (.cv w))))) x z (synCncs)
      dv_cache_0003 dv_cache_0017 dv_cache_0022 dv_cache_0023 dv_cache_0020 p0047
  have p0049 :=
    @gSylanbrc (.classMem A (synCncs))
      (synWrex x (synCncs) (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))
      (synWral x (synCncs) (synWral z (synCncs) (.imp
            (synWa (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))
              (synWrex w A (.classEq (.cv z) (synCnc (synCpw1 (.cv w)))))) (.objEq x z))))
      (synWreu x (synCncs) (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))
      p0020 p0040 p0048
  exact p0049

/-- Checked nominal proof certificate identified upstream as `g_tccl`. -/
@[expose]
noncomputable def gTccl (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCncs)) (.classMem (synCtc A) (synCncs))) :=
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
  have dv_cache_0004 : x ∉ ((synCncs)).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTc y A x
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gNcspw1eu x y A dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0002 :=
    @gReiotacl (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))) x
      (synCncs) dv_cache_0004
  have p0003 :=
    @gSyl (.classMem A (synCncs))
      (synWreu x (synCncs) (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))
      (.classMem (synCio x (synWa (.classMem (.cv x) (synCncs))
            (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y))))))) (synCncs))
      p0001 p0002
  have p0004 :=
    @gSyl5eqel (.classMem A (synCncs)) (synCtc A)
      (synCio x (synWa (.classMem (.cv x) (synCncs))
          (synWrex y A (.classEq (.cv x) (synCnc (synCpw1 (.cv y)))))))
      (synCncs) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_eqtc`. -/
@[expose]
noncomputable def gEqtc (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) :
    Nominal.NPrf
      (.imp (.classMem A (synCncs)) (synWb (.classEq (synCtc A) B)
          (synWrex x A (.classEq B (synCnc (synCpw1 (.cv x))))))) :=
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
  have dv_cache_0001 : x ∉ ((Wff.classMem B (synCncs))).fv := by
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
  have dv_cache_0006 : y ∉ ((synCncs)).fv :=
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
    y ∉ ((synWrex x A (.classEq B (synCnc (synCpw1 (.cv x)))))).fv :=
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
  have p0000 := @gSimpr (.classMem A (synCncs)) (.classEq (synCtc A) B)
  have p0001 := @gTccl A
  have p0002 :=
    @gAdantr (.classMem A (synCncs)) (.classMem (synCtc A) (synCncs))
      (.classEq (synCtc A) B) p0001
  have p0003 :=
    @gEqeltrrd (synWa (.classMem A (synCncs)) (.classEq (synCtc A) B)) (synCtc A) B
      (synCncs) p0000 p0002
  have p0004 :=
    @gEx (.classMem A (synCncs)) (.classEq (synCtc A) B) (.classMem B (synCncs)) p0003
  have p0005 := @gVex x
  have p0006 := @gPw1ex (.cv x) p0005
  have p0007 := @gNcelncsi (synCpw1 (.cv x)) p0006
  have p0008 := @gEleq1 B (synCnc (synCpw1 (.cv x))) (synCncs)
  have p0009 :=
    @gMpbiri (.classEq B (synCnc (synCpw1 (.cv x)))) (.classMem B (synCncs))
      (.classMem (synCnc (synCpw1 (.cv x))) (synCncs)) p0007 p0008
  have p0010 :=
    @gRexlimivw (.classEq B (synCnc (synCpw1 (.cv x)))) (.classMem B (synCncs)) x A
      dv_cache_0001 p0009
  have p0011 :=
    @gA1i
      (.imp (synWrex x A (.classEq B (synCnc (synCpw1 (.cv x))))) (.classMem B (synCncs)))
      (.classMem A (synCncs)) p0010
  have p0012 := @gNcspw1eu y x A dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0013 := @gEqeq1 (.cv y) B (synCnc (synCpw1 (.cv x)))
  have p0014 :=
    @gRexbidv (.classEq (.cv y) B) (.classEq (.cv y) (synCnc (synCpw1 (.cv x))))
      (.classEq B (synCnc (synCpw1 (.cv x)))) x A dv_cache_0005 p0013
  have p0015 :=
    @gReiota2 (synWrex x A (.classEq (.cv y) (synCnc (synCpw1 (.cv x)))))
      (synWrex x A (.classEq B (synCnc (synCpw1 (.cv x))))) y (synCncs) B
      dv_cache_0006 dv_cache_0007 dv_cache_0008 p0014
  have p0016 :=
    @gSylan2 (.classMem A (synCncs)) (.classMem B (synCncs))
      (synWreu y (synCncs) (synWrex x A (.classEq (.cv y) (synCnc (synCpw1 (.cv x))))))
      (synWb (synWrex x A (.classEq B (synCnc (synCpw1 (.cv x))))) (.classEq (synCio y
            (synWa (.classMem (.cv y) (synCncs))
              (synWrex x A (.classEq (.cv y) (synCnc (synCpw1 (.cv x))))))) B))
      p0012 p0015
  have p0017 :=
    @gAncoms (.classMem B (synCncs)) (.classMem A (synCncs))
      (synWb (synWrex x A (.classEq B (synCnc (synCpw1 (.cv x))))) (.classEq (synCio y
            (synWa (.classMem (.cv y) (synCncs))
              (synWrex x A (.classEq (.cv y) (synCnc (synCpw1 (.cv x))))))) B))
      p0016
  have p0018 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfTc x A y
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0019 :=
    @gEqeq1i (synCtc A)
      (synCio y (synWa (.classMem (.cv y) (synCncs))
          (synWrex x A (.classEq (.cv y) (synCnc (synCpw1 (.cv x)))))))
      B p0018
  have p0020 :=
    @gSyl6rbbr (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWrex x A (.classEq B (synCnc (synCpw1 (.cv x)))))
      (.classEq (synCio y (synWa (.classMem (.cv y) (synCncs))
            (synWrex x A (.classEq (.cv y) (synCnc (synCpw1 (.cv x))))))) B)
      (.classEq (synCtc A) B) p0017 p0019
  have p0021 :=
    @gEx (.classMem A (synCncs)) (.classMem B (synCncs))
      (synWb (.classEq (synCtc A) B) (synWrex x A (.classEq B (synCnc (synCpw1 (.cv x))))))
      p0020
  have p0022 :=
    @gPm521ndd (.classMem A (synCncs)) (.classMem B (synCncs))
      (.classEq (synCtc A) B) (synWrex x A (.classEq B (synCnc (synCpw1 (.cv x)))))
      p0004 p0011 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_pw1eltc`. -/
@[expose]
noncomputable def gPw1eltc (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCncs)) (.classMem B A))
        (.classMem (synCpw1 B) (synCtc A))) :=
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
    y ∉ ((Wff.classEq (synCnc (synCpw1 B)) (synCnc (synCpw1 B)))).fv :=
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
  have dv_cache_0004 : y ∉ ((synCnc (synCpw1 B))).fv :=
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
  have p0000 := @gPw1exg B A
  have p0001 := @gNcidg (synCpw1 B) (synCvv)
  have p0002 :=
    @gSyl (.classMem B A) (.classMem (synCpw1 B) (synCvv))
      (.classMem (synCpw1 B) (synCnc (synCpw1 B))) p0000 p0001
  have p0003 :=
    @gAdantl (.classMem B A) (.classMem (synCpw1 B) (synCnc (synCpw1 B)))
      (.classMem A (synCncs)) p0002
  have p0004 := @gEqid (synCnc (synCpw1 B))
  have p0005 := @gPw1eq (.cv y) B
  have p0006 := @gNceqd (.classEq (.cv y) B) (synCpw1 (.cv y)) (synCpw1 B) p0005
  have p0007 :=
    @gEqeq2d (.classEq (.cv y) B) (synCnc (synCpw1 (.cv y))) (synCnc (synCpw1 B))
      (synCnc (synCpw1 B)) p0006
  have p0008 :=
    @gRspcev (.classEq (synCnc (synCpw1 B)) (synCnc (synCpw1 (.cv y))))
      (.classEq (synCnc (synCpw1 B)) (synCnc (synCpw1 B))) y B A dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0007
  have p0009 :=
    @gMpan2 (.classMem B A) (.classEq (synCnc (synCpw1 B)) (synCnc (synCpw1 B)))
      (synWrex y A (.classEq (synCnc (synCpw1 B)) (synCnc (synCpw1 (.cv y))))) p0004
      p0008
  have p0010 :=
    @gAdantl (.classMem B A)
      (synWrex y A (.classEq (synCnc (synCpw1 B)) (synCnc (synCpw1 (.cv y)))))
      (.classMem A (synCncs)) p0009
  have p0011 := @gEqtc y A (synCnc (synCpw1 B)) dv_cache_0002 dv_cache_0004
  have p0012 :=
    @gAdantr (.classMem A (synCncs))
      (synWb (.classEq (synCtc A) (synCnc (synCpw1 B)))
        (synWrex y A (.classEq (synCnc (synCpw1 B)) (synCnc (synCpw1 (.cv y))))))
      (.classMem B A) p0011
  have p0013 :=
    @gMpbird (synWa (.classMem A (synCncs)) (.classMem B A))
      (.classEq (synCtc A) (synCnc (synCpw1 B)))
      (synWrex y A (.classEq (synCnc (synCpw1 B)) (synCnc (synCpw1 (.cv y))))) p0010
      p0012
  have p0014 :=
    @gEleqtrrd (synWa (.classMem A (synCncs)) (.classMem B A)) (synCpw1 B)
      (synCnc (synCpw1 B)) (synCtc A) p0003 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_tc0c`. -/
@[expose]
noncomputable def gTc0c : Nominal.NPrf (.classEq (synCtc (synC0c)) (synC0c)) :=
  by
  have p0000 := @gN0cnc
  have p0001 := @gTccl (synC0c)
  have p0002 := Nominal.mp p0000 p0001
  have p0004 := @gPw10
  have p0006 := @gNulel0c
  have p0007 := @gPw1eltc (synC0c) (synC0)
  have p0008 :=
    @gMp2an (.classMem (synC0c) (synCncs)) (.classMem (synC0) (synC0c))
      (.classMem (synCpw1 (synC0)) (synCtc (synC0c))) p0000 p0006 p0007
  have p0009 := @gEqeltrri (synCpw1 (synC0)) (synC0) (synCtc (synC0c)) p0004 p0008
  have p0011 := @gNceleq (synCtc (synC0c)) (synC0c) (synC0)
  have p0012 :=
    @gMp4an (.classMem (synCtc (synC0c)) (synCncs)) (.classMem (synC0c) (synCncs))
      (.classMem (synC0) (synCtc (synC0c))) (.classMem (synC0) (synC0c))
      (.classEq (synCtc (synC0c)) (synC0c)) p0002 p0000 p0009 p0006 p0011
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

/-- Checked nominal proof certificate identified upstream as `g_tcdi`. -/
@[expose]
noncomputable def gTcdi (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
        (.classEq (synCtc (synCplc A B)) (synCplc (synCtc A) (synCtc B)))) :=
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
  have dv_cache_0001 : y ∉ ((Wff.classEq A (synCnc (.cv x)))).fv := by
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
  have dv_cache_0002 : x ∉ ((Wff.classEq B (synCnc (.cv y)))).fv :=
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
    x ∉ ((Wff.classEq (synCtc (synCplc A B)) (synCplc (synCtc A) (synCtc B)))).fv :=
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
    y ∉ ((Wff.classEq (synCtc (synCplc A B)) (synCplc (synCtc A) (synCtc B)))).fv :=
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
    @gEeanv (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))) x y
      dv_cache_0001 dv_cache_0002
  have p0001 := @gVex x
  have p0002 := @gN0ex
  have p0003 := @gComplex (synC0) p0002
  have p0004 := @gXpsnen (.cv x) (synCcompl (synC0)) p0001 p0003
  have p0005 := @gSnex (synCcompl (synC0))
  have p0006 := @gXpex (.cv x) (synCsn (synCcompl (synC0))) p0001 p0005
  have p0007 := @gEqnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))) (.cv x) p0006
  have p0008 :=
    @gMpbir
      (.classEq (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))) (synCnc (.cv x)))
      (synWbr (synCxp (.cv x) (synCsn (synCcompl (synC0)))) (synCen) (.cv x)) p0004
      p0007
  have p0009 :=
    @gEqeq2i (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
      (synCnc (.cv x)) A p0008
  have p0010 := @gVex y
  have p0012 := @gXpsnen (.cv y) (synC0) p0010 p0002
  have p0013 := @gSnex (synC0)
  have p0014 := @gXpex (.cv y) (synCsn (synC0)) p0010 p0013
  have p0015 := @gEqnc (synCxp (.cv y) (synCsn (synC0))) (.cv y) p0014
  have p0016 :=
    @gMpbir (.classEq (synCnc (synCxp (.cv y) (synCsn (synC0)))) (synCnc (.cv y)))
      (synWbr (synCxp (.cv y) (synCsn (synC0))) (synCen) (.cv y)) p0012 p0015
  have p0017 :=
    @gEqeq2i (synCnc (synCxp (.cv y) (synCsn (synC0)))) (synCnc (.cv y)) B p0016
  have p0018 :=
    @gAnbi12i (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
      (.classEq A (synCnc (.cv x)))
      (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      (.classEq B (synCnc (.cv y))) p0009 p0017
  have p0019 :=
    @gN2exbii
      (synWa (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
        (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y)))) x y p0018
  have p0020 := @gElncs x A dv_cache_0003
  have p0021 := @gElncs y B dv_cache_0004
  have p0022 :=
    @gAnbi12i (.classMem A (synCncs)) (synWex x (.classEq A (synCnc (.cv x))))
      (.classMem B (synCncs)) (synWex y (.classEq B (synCnc (.cv y)))) p0020 p0021
  have p0023 :=
    @gN3bitr4ri
      (synWex x (synWex y
          (synWa (.classEq A (synCnc (.cv x))) (.classEq B (synCnc (.cv y))))))
      (synWa (synWex x (.classEq A (synCnc (.cv x))))
        (synWex y (.classEq B (synCnc (.cv y)))))
      (synWex x (synWex y
          (synWa (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
            (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0))))))))
      (synWa (.classMem A (synCncs)) (.classMem B (synCncs))) p0000 p0019 p0022
  have p0024 := @gNcelncsi (synCxp (.cv x) (synCsn (synCcompl (synC0)))) p0006
  have p0025 := @gNcelncsi (synCxp (.cv y) (synCsn (synC0))) p0014
  have p0026 :=
    @gNcaddccl (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
      (synCnc (synCxp (.cv y) (synCsn (synC0))))
  have p0027 :=
    @gMp2an
      (.classMem (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))) (synCncs))
      (.classMem (synCnc (synCxp (.cv y) (synCsn (synC0)))) (synCncs))
      (.classMem (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0))))) (synCncs))
      p0024 p0025 p0026
  have p0028 :=
    @gTccl
      (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCnc (synCxp (.cv y) (synCsn (synC0)))))
  have p0029 := Nominal.mp p0027 p0028
  have p0030 := @gTccl (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
  have p0031 := Nominal.mp p0024 p0030
  have p0032 := @gTccl (synCnc (synCxp (.cv y) (synCsn (synC0))))
  have p0033 := Nominal.mp p0025 p0032
  have p0034 :=
    @gNcaddccl (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
      (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0)))))
  have p0035 :=
    @gMp2an
      (.classMem (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
        (synCncs))
      (.classMem (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0))))) (synCncs))
      (.classMem (synCplc (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
          (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0)))))) (synCncs))
      p0031 p0033 p0034
  have p0036 := @gNcid (synCxp (.cv x) (synCsn (synCcompl (synC0)))) p0006
  have p0037 := @gNcid (synCxp (.cv y) (synCsn (synC0))) p0014
  have p0038 := @gNecompl (synC0)
  have p0039 := @gXpnedisj (.cv x) (.cv y) (synCcompl (synC0)) (synC0) p0003 p0038
  have p0040 :=
    @gEladdci (synCxp (.cv x) (synCsn (synCcompl (synC0))))
      (synCxp (.cv y) (synCsn (synC0)))
      (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
      (synCnc (synCxp (.cv y) (synCsn (synC0))))
  have p0041 :=
    @gMp3an
      (.classMem (synCxp (.cv x) (synCsn (synCcompl (synC0))))
        (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
      (.classMem (synCxp (.cv y) (synCsn (synC0)))
        (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      (.classEq (synCin (synCxp (.cv x) (synCsn (synCcompl (synC0))))
          (synCxp (.cv y) (synCsn (synC0)))) (synC0))
      (.classMem (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
          (synCxp (.cv y) (synCsn (synC0))))
        (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      p0036 p0037 p0039 p0040
  have p0042 :=
    @gPw1eltc
      (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
        (synCxp (.cv y) (synCsn (synC0))))
  have p0043 :=
    @gMp2an
      (.classMem (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0))))) (synCncs))
      (.classMem (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
          (synCxp (.cv y) (synCsn (synC0))))
        (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (.classMem (synCpw1 (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
            (synCxp (.cv y) (synCsn (synC0))))) (synCtc
          (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
            (synCnc (synCxp (.cv y) (synCsn (synC0)))))))
      p0027 p0041 p0042
  have p0044 :=
    @gPw1un (synCxp (.cv x) (synCsn (synCcompl (synC0))))
      (synCxp (.cv y) (synCsn (synC0)))
  have p0045 :=
    @gPw1eltc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
      (synCxp (.cv x) (synCsn (synCcompl (synC0))))
  have p0046 :=
    @gMp2an
      (.classMem (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))) (synCncs))
      (.classMem (synCxp (.cv x) (synCsn (synCcompl (synC0))))
        (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
      (.classMem (synCpw1 (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))))
      p0024 p0036 p0045
  have p0047 :=
    @gPw1eltc (synCnc (synCxp (.cv y) (synCsn (synC0))))
      (synCxp (.cv y) (synCsn (synC0)))
  have p0048 :=
    @gMp2an (.classMem (synCnc (synCxp (.cv y) (synCsn (synC0)))) (synCncs))
      (.classMem (synCxp (.cv y) (synCsn (synC0)))
        (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      (.classMem (synCpw1 (synCxp (.cv y) (synCsn (synC0))))
        (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      p0025 p0037 p0047
  have p0049 :=
    @gPw1eq
      (synCin (synCxp (.cv x) (synCsn (synCcompl (synC0))))
        (synCxp (.cv y) (synCsn (synC0))))
      (synC0)
  have p0050 := Nominal.mp p0039 p0049
  have p0051 :=
    @gPw1in (synCxp (.cv x) (synCsn (synCcompl (synC0))))
      (synCxp (.cv y) (synCsn (synC0)))
  have p0052 := @gPw10
  have p0053 :=
    @gN3eqtr3i
      (synCpw1 (synCin (synCxp (.cv x) (synCsn (synCcompl (synC0))))
          (synCxp (.cv y) (synCsn (synC0)))))
      (synCpw1 (synC0))
      (synCin (synCpw1 (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCpw1 (synCxp (.cv y) (synCsn (synC0)))))
      (synC0) p0050 p0051 p0052
  have p0054 :=
    @gEladdci (synCpw1 (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
      (synCpw1 (synCxp (.cv y) (synCsn (synC0))))
      (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
      (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0)))))
  have p0055 :=
    @gMp3an
      (.classMem (synCpw1 (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))))
      (.classMem (synCpw1 (synCxp (.cv y) (synCsn (synC0))))
        (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (.classEq (synCin (synCpw1 (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCpw1 (synCxp (.cv y) (synCsn (synC0))))) (synC0))
      (.classMem (synCun (synCpw1 (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCpw1 (synCxp (.cv y) (synCsn (synC0)))))
        (synCplc (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
          (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0)))))))
      p0046 p0048 p0053 p0054
  have p0056 :=
    @gEqeltri
      (synCpw1 (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
          (synCxp (.cv y) (synCsn (synC0)))))
      (synCun (synCpw1 (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCpw1 (synCxp (.cv y) (synCsn (synC0)))))
      (synCplc (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
        (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      p0044 p0055
  have p0057 :=
    @gNceleq
      (synCtc (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (synCplc (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
        (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (synCpw1 (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
          (synCxp (.cv y) (synCsn (synC0)))))
  have p0058 :=
    @gMp4an
      (.classMem (synCtc (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
            (synCnc (synCxp (.cv y) (synCsn (synC0)))))) (synCncs))
      (.classMem (synCplc (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
          (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0)))))) (synCncs))
      (.classMem (synCpw1 (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
            (synCxp (.cv y) (synCsn (synC0))))) (synCtc
          (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
            (synCnc (synCxp (.cv y) (synCsn (synC0)))))))
      (.classMem (synCpw1 (synCun (synCxp (.cv x) (synCsn (synCcompl (synC0))))
            (synCxp (.cv y) (synCsn (synC0)))))
        (synCplc (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
          (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0)))))))
      (.classEq (synCtc (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
            (synCnc (synCxp (.cv y) (synCsn (synC0))))))
        (synCplc (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
          (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0)))))))
      p0029 p0035 p0043 p0056 p0057
  have p0059 :=
    @gAddceq12 A B (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
      (synCnc (synCxp (.cv y) (synCsn (synC0))))
  have p0060 :=
    @gTceq (synCplc A B)
      (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
        (synCnc (synCxp (.cv y) (synCsn (synC0)))))
  have p0061 :=
    @gSyl
      (synWa (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
        (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (.classEq (synCplc A B)
        (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (.classEq (synCtc (synCplc A B)) (synCtc
          (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
            (synCnc (synCxp (.cv y) (synCsn (synC0)))))))
      p0059 p0060
  have p0062 := @gTceq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
  have p0063 :=
    @gAdantr (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
      (.classEq (synCtc A)
        (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))))
      (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0))))) p0062
  have p0064 := @gTceq B (synCnc (synCxp (.cv y) (synCsn (synC0))))
  have p0065 :=
    @gAdantl (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0)))))
      (.classEq (synCtc B) (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))) p0064
  have p0066 :=
    @gAddceq12d
      (synWa (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
        (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (synCtc A) (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
      (synCtc B) (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0))))) p0063 p0065
  have p0067 :=
    @gN3eqtr4a
      (synWa (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
        (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (synCtc (synCplc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0)))))
          (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (synCplc (synCtc (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
        (synCtc (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (synCtc (synCplc A B)) (synCplc (synCtc A) (synCtc B)) p0058 p0061 p0066
  have p0068 :=
    @gExlimivv
      (synWa (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
        (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0))))))
      (.classEq (synCtc (synCplc A B)) (synCplc (synCtc A) (synCtc B))) x y
      dv_cache_0005 dv_cache_0006 p0067
  have p0069 :=
    @gSylbi (synWa (.classMem A (synCncs)) (.classMem B (synCncs)))
      (synWex x (synWex y
          (synWa (.classEq A (synCnc (synCxp (.cv x) (synCsn (synCcompl (synC0))))))
            (.classEq B (synCnc (synCxp (.cv y) (synCsn (synC0))))))))
      (.classEq (synCtc (synCplc A B)) (synCplc (synCtc A) (synCtc B))) p0023 p0068
  exact p0069

/-- Checked nominal proof certificate identified upstream as `g_tc1c`. -/
@[expose]
noncomputable def gTc1c : Nominal.NPrf (.classEq (synCtc (synC1c)) (synC1c)) :=
  by
  have p0000 := @gN1cnc
  have p0001 := @gTccl (synC1c)
  have p0002 := Nominal.mp p0000 p0001
  have p0004 := @gN0ex
  have p0005 := @gPw1sn (synC0) p0004
  have p0008 := @gSnel1c (synC0) p0004
  have p0009 := @gPw1eltc (synC1c) (synCsn (synC0))
  have p0010 :=
    @gMp2an (.classMem (synC1c) (synCncs)) (.classMem (synCsn (synC0)) (synC1c))
      (.classMem (synCpw1 (synCsn (synC0))) (synCtc (synC1c))) p0000 p0008 p0009
  have p0011 :=
    @gEqeltrri (synCpw1 (synCsn (synC0))) (synCsn (synCsn (synC0)))
      (synCtc (synC1c)) p0005 p0010
  have p0012 := @gSnex (synC0)
  have p0013 := @gSnel1c (synCsn (synC0)) p0012
  have p0014 := @gNceleq (synCtc (synC1c)) (synC1c) (synCsn (synCsn (synC0)))
  have p0015 :=
    @gMp4an (.classMem (synCtc (synC1c)) (synCncs)) (.classMem (synC1c) (synCncs))
      (.classMem (synCsn (synCsn (synC0))) (synCtc (synC1c)))
      (.classMem (synCsn (synCsn (synC0))) (synC1c))
      (.classEq (synCtc (synC1c)) (synC1c)) p0002 p0000 p0011 p0013 p0014
  exact p0015

/-- Checked nominal proof certificate identified upstream as `g_n_2nnc`. -/
@[expose]
noncomputable def gN2nnc : Nominal.NPrf (.classMem (synC2c) (synCnnc)) :=
  by
  have p0000 := @gN1p1e2c
  have p0001 := @gN1cnnc
  have p0002 := @gPeano2 (synC1c)
  have p0003 := Nominal.mp p0001 p0002
  have p0004 :=
    @gEqeltrri (synCplc (synC1c) (synC1c)) (synC2c) (synCnnc) p0000 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_pw1fin`. -/
@[expose]
noncomputable def gPw1fin (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCfin)) (.classMem (synCpw1 A) (synCfin))) :=
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
      ((synWrex m (synCnnc) (synWa (.classMem (synCpw1 A) (.cv m))
            (.classMem (synCpw1 A) (.cv m))))).fv :=
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
  have dv_cache_0004 : m ∉ ((synCpw1 A)).fv :=
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
  have p0000 := @gNcfinraise A A m (.cv n) dv_cache_0001 dv_cache_0001
  have p0001 :=
    @gN3anidm23 (.classMem (.cv n) (synCnnc)) (.classMem A (.cv n))
      (synWrex m (synCnnc)
        (synWa (.classMem (synCpw1 A) (.cv m)) (.classMem (synCpw1 A) (.cv m))))
      p0000
  have p0002 :=
    @gRexlimiva (.classMem A (.cv n))
      (synWrex m (synCnnc)
        (synWa (.classMem (synCpw1 A) (.cv m)) (.classMem (synCpw1 A) (.cv m))))
      n (synCnnc) dv_cache_0002 p0001
  have p0003 := @gSimpl (.classMem (synCpw1 A) (.cv m)) (.classMem (synCpw1 A) (.cv m))
  have p0004 :=
    @gReximi (synWa (.classMem (synCpw1 A) (.cv m)) (.classMem (synCpw1 A) (.cv m)))
      (.classMem (synCpw1 A) (.cv m)) m (synCnnc) p0003
  have p0005 :=
    @gSyl (synWrex n (synCnnc) (.classMem A (.cv n)))
      (synWrex m (synCnnc)
        (synWa (.classMem (synCpw1 A) (.cv m)) (.classMem (synCpw1 A) (.cv m))))
      (synWrex m (synCnnc) (.classMem (synCpw1 A) (.cv m))) p0002 p0004
  have p0006 := @gElfin n A dv_cache_0003
  have p0007 := @gElfin m (synCpw1 A) dv_cache_0004
  have p0008 :=
    @gN3imtr4i (synWrex n (synCnnc) (.classMem A (.cv n)))
      (synWrex m (synCnnc) (.classMem (synCpw1 A) (.cv m))) (.classMem A (synCfin))
      (.classMem (synCpw1 A) (synCfin)) p0005 p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_nntccl`. -/
@[expose]
noncomputable def gNntccl (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCnnc)) (.classMem (synCtc A) (synCnnc))) :=
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
  have dv_cache_0003 : a ∉ ((synCnnc)).fv :=
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
  have dv_cache_0006 : m ∉ ((synCpw1 (.cv n))).fv :=
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
  have dv_cache_0007 : m ∉ ((Wff.classMem (synCtc A) (synCnnc))).fv :=
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
  have dv_cache_0008 : m ∉ ((synWa (.classMem A (synCnnc)) (.classMem (.cv n) A))).fv :=
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
  have dv_cache_0009 : n ∉ ((Wff.classMem (synCtc A) (synCnnc))).fv :=
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
  have dv_cache_0010 : n ∉ ((Wff.classMem A (synCnnc))).fv :=
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
  have p0000 := @gNulnnn
  have p0001 := @gEleq1 A (synC0) (synCnnc)
  have p0002 :=
    @gMtbiri (.classEq A (synC0)) (.classMem A (synCnnc))
      (.classMem (synC0) (synCnnc)) p0000 p0001
  have p0003 := @gNecon2ai (.classMem A (synCnnc)) A (synC0) p0002
  have p0004 := @gN0 n A dv_cache_0001
  have p0005 :=
    @gSylib (.classMem A (synCnnc)) (synWne A (synC0))
      (synWex n (.classMem (.cv n) A)) p0003 p0004
  have p0006 := @gEleq2 (.cv a) A (.cv n)
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) A) (synWb (.objMem n a) (.classMem (.cv n) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
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
    @gRspcev (.objMem n a) (.classMem (.cv n) A) a A (synCnnc) dv_cache_0002
      dv_cache_0003 dv_cache_0004 p0007_e00_recanon
  have p0008 := @gElfin a (.cv n) dv_cache_0005
  have p0009_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv n) (synCfin)) (synWrex a (synCnnc) (.objMem n a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCfin synCuni synWex synWa synCnnc synCint synWrex
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
    @gSylibr (synWa (.classMem A (synCnnc)) (.classMem (.cv n) A))
      (synWrex a (synCnnc) (.objMem n a)) (.classMem (.cv n) (synCfin)) p0007
      p0009_e01_recanon
  have p0010 := @gPw1fin (.cv n)
  have p0011 :=
    @gSyl (synWa (.classMem A (synCnnc)) (.classMem (.cv n) A))
      (.classMem (.cv n) (synCfin)) (.classMem (synCpw1 (.cv n)) (synCfin)) p0009 p0010
  have p0012 := @gElfin m (synCpw1 (.cv n)) dv_cache_0006
  have p0013 :=
    @gSylib (synWa (.classMem A (synCnnc)) (.classMem (.cv n) A))
      (.classMem (synCpw1 (.cv n)) (synCfin))
      (synWrex m (synCnnc) (.classMem (synCpw1 (.cv n)) (.cv m))) p0011 p0012
  have p0014 := @gNnnc A
  have p0015 := @gTccl A
  have p0016 :=
    @gSyl (.classMem A (synCnnc)) (.classMem A (synCncs))
      (.classMem (synCtc A) (synCncs)) p0014 p0015
  have p0017 :=
    @gAd2antrr (.classMem A (synCnnc)) (.classMem (synCtc A) (synCncs))
      (.classMem (.cv m) (synCnnc))
      (synWa (.classMem (.cv n) A) (.classMem (synCpw1 (.cv n)) (.cv m))) p0016
  have p0018 := @gNnnc (.cv m)
  have p0019 :=
    @gAd2antlr (.classMem (.cv m) (synCnnc)) (.classMem (.cv m) (synCncs))
      (.classMem A (synCnnc))
      (synWa (.classMem (.cv n) A) (.classMem (synCpw1 (.cv n)) (.cv m))) p0018
  have p0020 :=
    @gAd2antrr (.classMem A (synCnnc)) (.classMem A (synCncs))
      (.classMem (.cv m) (synCnnc))
      (synWa (.classMem (.cv n) A) (.classMem (synCpw1 (.cv n)) (.cv m))) p0014
  have p0021 :=
    @gSimprl (synWa (.classMem A (synCnnc)) (.classMem (.cv m) (synCnnc)))
      (.classMem (.cv n) A) (.classMem (synCpw1 (.cv n)) (.cv m))
  have p0022 := @gPw1eltc A (.cv n)
  have p0023 :=
    @gSyl2anc
      (synWa (synWa (.classMem A (synCnnc)) (.classMem (.cv m) (synCnnc)))
        (synWa (.classMem (.cv n) A) (.classMem (synCpw1 (.cv n)) (.cv m))))
      (.classMem A (synCncs)) (.classMem (.cv n) A)
      (.classMem (synCpw1 (.cv n)) (synCtc A)) p0020 p0021 p0022
  have p0024 :=
    @gSimprr (synWa (.classMem A (synCnnc)) (.classMem (.cv m) (synCnnc)))
      (.classMem (.cv n) A) (.classMem (synCpw1 (.cv n)) (.cv m))
  have p0025 := @gNceleq (synCtc A) (.cv m) (synCpw1 (.cv n))
  have p0026 :=
    @gSyl22anc
      (synWa (synWa (.classMem A (synCnnc)) (.classMem (.cv m) (synCnnc)))
        (synWa (.classMem (.cv n) A) (.classMem (synCpw1 (.cv n)) (.cv m))))
      (.classMem (synCtc A) (synCncs)) (.classMem (.cv m) (synCncs))
      (.classMem (synCpw1 (.cv n)) (synCtc A)) (.classMem (synCpw1 (.cv n)) (.cv m))
      (.classEq (synCtc A) (.cv m)) p0017 p0019 p0023 p0024 p0025
  have p0027 :=
    @gSimplr (.classMem A (synCnnc)) (.classMem (.cv m) (synCnnc))
      (synWa (.classMem (.cv n) A) (.classMem (synCpw1 (.cv n)) (.cv m)))
  have p0028 :=
    @gEqeltrd
      (synWa (synWa (.classMem A (synCnnc)) (.classMem (.cv m) (synCnnc)))
        (synWa (.classMem (.cv n) A) (.classMem (synCpw1 (.cv n)) (.cv m))))
      (synCtc A) (.cv m) (synCnnc) p0026 p0027
  have p0029 :=
    @gExpr (synWa (.classMem A (synCnnc)) (.classMem (.cv m) (synCnnc)))
      (.classMem (.cv n) A) (.classMem (synCpw1 (.cv n)) (.cv m))
      (.classMem (synCtc A) (synCnnc)) p0028
  have p0030 :=
    @gAn32s (.classMem A (synCnnc)) (.classMem (.cv m) (synCnnc)) (.classMem (.cv n) A)
      (.imp (.classMem (synCpw1 (.cv n)) (.cv m)) (.classMem (synCtc A) (synCnnc)))
      p0029
  have p0031 :=
    @gRexlimdva (synWa (.classMem A (synCnnc)) (.classMem (.cv n) A))
      (.classMem (synCpw1 (.cv n)) (.cv m)) (.classMem (synCtc A) (synCnnc)) m
      (synCnnc) dv_cache_0007 dv_cache_0008 p0030
  have p0032 :=
    @gMpd (synWa (.classMem A (synCnnc)) (.classMem (.cv n) A))
      (synWrex m (synCnnc) (.classMem (synCpw1 (.cv n)) (.cv m)))
      (.classMem (synCtc A) (synCnnc)) p0013 p0031
  have p0033 :=
    @gEx (.classMem A (synCnnc)) (.classMem (.cv n) A)
      (.classMem (synCtc A) (synCnnc)) p0032
  have p0034 :=
    @gExlimdv (.classMem A (synCnnc)) (.classMem (.cv n) A)
      (.classMem (synCtc A) (synCnnc)) n dv_cache_0009 dv_cache_0010 p0033
  have p0035 :=
    @gMpd (.classMem A (synCnnc)) (synWex n (.classMem (.cv n) A))
      (.classMem (synCtc A) (synCnnc)) p0005 p0034
  exact p0035

/-- Checked nominal proof certificate identified upstream as `g_nclec`. -/
@[expose]
noncomputable def gNclec (A : Class) (B : Class)
    (hyp_nclec_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_nclec_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.imp (synWss A B) (synWbr (synCnc A) (synClec) (synCnc B))) :=
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
  have dv_cache_0004 : x ∉ ((synCnc A)).fv :=
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
  have dv_cache_0005 : x ∉ ((synCnc B)).fv :=
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
  have dv_cache_0006 : y ∉ ((synCnc B)).fv :=
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
  have dv_cache_0007 : x ∉ ((synWss A (.cv y))).fv :=
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
  have dv_cache_0008 : y ∉ ((synWss A B)).fv :=
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
  have p0000 := @gNcid A hyp_nclec_1
  have p0001 := @gNcid B hyp_nclec_2
  have p0002 := @gSseq1 (.cv x) A (.cv y)
  have p0003 := @gSseq2 (.cv y) B A
  have p0004 :=
    @gRspc2ev (synWss (.cv x) (.cv y)) (synWss A B) (synWss A (.cv y)) x y A B
      (synCnc A) (synCnc B) dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
      dv_cache_0005 dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0002 p0003
  have p0005 :=
    @gMp3an12 (.classMem A (synCnc A)) (.classMem B (synCnc B)) (synWss A B)
      (synWrex x (synCnc A) (synWrex y (synCnc B) (synWss (.cv x) (.cv y)))) p0000
      p0001 p0004
  have p0006 := @gNcex A
  have p0007 := @gNcex B
  have p0008 :=
    @gBrlec x y (synCnc A) (synCnc B) dv_cache_0004 dv_cache_0005 dv_cache_0006
      dv_cache_0009 p0006 p0007
  have p0009 :=
    @gSylibr (synWss A B)
      (synWrex x (synCnc A) (synWrex y (synCnc B) (synWss (.cv x) (.cv y))))
      (synWbr (synCnc A) (synClec) (synCnc B)) p0005 p0008
  exact p0009

/-- Checked nominal proof certificate identified upstream as `g_lecidg`. -/
@[expose]
noncomputable def gLecidg (A : Class) (V : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (synWne A (synC0))) (synWbr A (synClec) A)) :=
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
  have dv_cache_0003 : y ∉ ((synWss (.cv x) (.cv x))).fv :=
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
  have p0000 := @gSsid (.cv x)
  have p0001 := @gSseq2 (.cv y) (.cv x) (.cv x)
  have p0002 :=
    @gRspcev (synWss (.cv x) (.cv y)) (synWss (.cv x) (.cv x)) y (.cv x) A
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0001
  have p0003 :=
    @gMpan2 (.classMem (.cv x) A) (synWss (.cv x) (.cv x))
      (synWrex y A (synWss (.cv x) (.cv y))) p0000 p0002
  have p0004 :=
    @gAncli (.classMem (.cv x) A) (synWrex y A (synWss (.cv x) (.cv y))) p0003
  have p0005 :=
    @gEximi (.classMem (.cv x) A)
      (synWa (.classMem (.cv x) A) (synWrex y A (synWss (.cv x) (.cv y)))) x p0004
  have p0006 := @gN0 x A dv_cache_0004
  have p0007 :=
    (Nominal.biimpRefl (synWrex x A (synWrex y A (synWss (.cv x) (.cv y)))))
  have p0008 :=
    @gN3imtr4i (synWex x (.classMem (.cv x) A))
      (synWex x (synWa (.classMem (.cv x) A) (synWrex y A (synWss (.cv x) (.cv y)))))
      (synWne A (synC0)) (synWrex x A (synWrex y A (synWss (.cv x) (.cv y)))) p0005
      p0006 p0007
  have p0009 :=
    @gAdantl (synWne A (synC0)) (synWrex x A (synWrex y A (synWss (.cv x) (.cv y))))
      (.classMem A V) p0008
  have p0010 :=
    @gBrlecg x y A A V V dv_cache_0004 dv_cache_0004 dv_cache_0002 dv_cache_0005
  have p0011 :=
    @gAnidms (.classMem A V)
      (synWb (synWbr A (synClec) A) (synWrex x A (synWrex y A (synWss (.cv x) (.cv y)))))
      p0010
  have p0012 :=
    @gAdantr (.classMem A V)
      (synWb (synWbr A (synClec) A) (synWrex x A (synWrex y A (synWss (.cv x) (.cv y)))))
      (synWne A (synC0)) p0011
  have p0013 :=
    @gMpbird (synWa (.classMem A V) (synWne A (synC0))) (synWbr A (synClec) A)
      (synWrex x A (synWrex y A (synWss (.cv x) (.cv y)))) p0009 p0012
  exact p0013

/-- Checked nominal proof certificate identified upstream as `g_nclecid`. -/
@[expose]
noncomputable def gNclecid (A : Class) :
    Nominal.NPrf (.imp (.classMem A (synCncs)) (synWbr A (synClec) A)) :=
  by
  have p0000 := @gNulnnc
  have p0001 := @gEleq1 A (synC0) (synCncs)
  have p0002 :=
    @gMtbiri (.classEq A (synC0)) (.classMem A (synCncs))
      (.classMem (synC0) (synCncs)) p0000 p0001
  have p0003 := @gNecon2ai (.classMem A (synCncs)) A (synC0) p0002
  have p0004 := @gLecidg A (synCncs)
  have p0005 :=
    @gMpdan (.classMem A (synCncs)) (synWne A (synC0)) (synWbr A (synClec) A) p0003
      p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end
