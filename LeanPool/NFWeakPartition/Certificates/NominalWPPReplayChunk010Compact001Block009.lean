/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block008

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part023`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_vfinspsslem1`. -/
@[expose]
noncomputable def gVfinspsslem1 (x : Var) (z : Var) (n : Var) (_dv_n_x : n ≠ x)
    (_dv_n_z : n ≠ z) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin)))
          (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
        (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ z } : Finset Var) ∪ ({ n } : Finset Var)
  let p : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let b : Var := freshVar proofSupport 2
  let d : Var := freshVar proofSupport 3
  let g : Var := freshVar proofSupport 4
  have fresh_p : p ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_p_ne_x : p ≠ x := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_z : p ≠ z := by
    intro h
    exact
      fresh_p
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_p_ne_n : p ≠ n := by
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
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_b_ne_x : b ≠ x := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_b_ne_z : b ≠ z := by
    intro h
    exact
      fresh_b
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_d : d ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_d_ne_x : d ≠ x := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_d : x ≠ d := Ne.symm fresh_d_ne_x
  have fresh_d_ne_z : d ≠ z := by
    intro h
    exact
      fresh_d
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_d_ne_n : d ≠ n := by
    intro h
    exact fresh_d (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_p_ne_a : p ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_p : a ≠ p := Ne.symm fresh_p_ne_a
  have fresh_p_ne_b : p ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_b_ne_p : b ≠ p := Ne.symm fresh_p_ne_b
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_d : a ≠ d :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_d_ne_a : d ≠ a := Ne.symm fresh_a_ne_d
  have fresh_a_ne_g : a ≠ g :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_g_ne_a : g ≠ a := Ne.symm fresh_a_ne_g
  have fresh_d_ne_g : d ≠ g :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_g_ne_d : g ≠ d := Ne.symm fresh_d_ne_g
  have dv_cache_0001 : a ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_z, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((synCtfin (.cv n))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_n,
          not_false_eq_true])
  have dv_cache_0003 : p ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_z, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((synCtfin (synCncfin (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0005 : a ∉ ((synCpw1 (synCpw1 (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0006 : b ∉ ((synCpw1 (synCpw1 (synCvv)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0007 : b ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_z, not_false_eq_true])
  have dv_cache_0008 : a ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_p, not_false_eq_true])
  have dv_cache_0009 : b ∉ ((Class.cv p)).fv :=
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
          fresh_b_ne_p, not_false_eq_true])
  have dv_cache_0010 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0011 : g ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_g_ne_a, not_false_eq_true])
  have dv_cache_0012 : g ∉ ((synCpw1 (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0013 : d ∉ ((Class.cv g)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_d_ne_g, not_false_eq_true])
  have dv_cache_0014 : d ∉ ((synCvv)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0015 : d ∉ ((Wff.classEq (.cv a) (synCpw1 (.cv g)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_d_ne_a, fresh_d_ne_g, or_false, not_false_eq_true])
  have dv_cache_0016 : g ∉ ((synCpw1 (.cv d))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_g_ne_d,
          not_false_eq_true])
  have dv_cache_0017 : g ∉ ((Wff.classEq (.cv a) (synCpw1 (synCpw1 (.cv d))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : g ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, fresh_g_ne_a, fresh_g_ne_d, or_false, not_false_eq_true])
  have dv_cache_0018 : a ∉ ((Class.cv d)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_d, not_false_eq_true])
  have dv_cache_0019 :
    a ∉
      ((synWa (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d))))
          (.classMem (synCpw (.cv d)) (synCncfin (synCpw (.cv d)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_d, or_false, not_false_eq_true])
  have dv_cache_0020 : a ∉ ((synCncfin (synCpw1 (.cv d)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_d,
          not_false_eq_true])
  have dv_cache_0021 : a ∉ ((synCncfin (synCpw (.cv d)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_d,
          not_false_eq_true])
  have dv_cache_0022 : x ∉ ((synCncfin (synCpw1 (.cv d)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_d,
          not_false_eq_true])
  have dv_cache_0023 : x ∉ ((synCspfin)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0024 :
    x ∉ ((Wff.classEq (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          Finset.mem_singleton, dv_x_z, fresh_x_ne_d, or_false, not_false_eq_true])
  have dv_cache_0025 :
    d ∉ ((synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_d_ne_z, fresh_d_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0026 :
    d ∉
      ((synWa (synWa (synWa (.classMem (synCvv) (synCfin))
              (.classMem (synCtfin (.cv n)) (synCspfin)))
            (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
          (.objMem a z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : d ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_d_ne_n, fresh_d_ne_z, fresh_d_ne_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0027 :
    a ∉ ((synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0028 :
    b ∉ ((synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_b_ne_z, fresh_b_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0029 :
    a ∉
      ((synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin)))
          (synWa (.classMem (.cv n) (synCspfin))
            (synWsfin (.cv z) (synCtfin (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_n, fresh_a_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0030 :
    b ∉
      ((synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin)))
          (synWa (.classMem (.cv n) (synCspfin))
            (synWsfin (.cv z) (synCtfin (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_n, fresh_b_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0031 :
    p ∉ ((synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_ne_z, fresh_p_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0032 :
    p ∉
      ((synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin)))
          (synWa (.classMem (.cv n) (synCspfin))
            (synWsfin (.cv z) (synCtfin (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_n, fresh_p_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 := @gSimpl (.classMem (synCvv) (synCfin)) (.classMem (.cv n) (synCspfin))
  have p0001 := @gVfinspnn
  have p0002 := @gDifss (synCnnc) (synCsn (synC0))
  have p0003 :=
    @gSyl6ss (.classMem (synCvv) (synCfin)) (synCspfin)
      (synCdif (synCnnc) (synCsn (synC0))) (synCnnc) p0001 p0002
  have p0004 :=
    @gSselda (.classMem (synCvv) (synCfin)) (synCspfin) (synCnnc) (.cv n) p0003
  have p0006 :=
    @gSselda (.classMem (synCvv) (synCfin)) (synCspfin)
      (synCdif (synCnnc) (synCsn (synC0))) (.cv n) p0001
  have p0007 := @gEldifsn (.cv n) (synCnnc) (synC0)
  have p0008 :=
    @gSimprbi (.classMem (.cv n) (synCdif (synCnnc) (synCsn (synC0))))
      (.classMem (.cv n) (synCnnc)) (synWne (.cv n) (synC0)) p0007
  have p0009 :=
    @gSyl (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv n) (synCspfin)))
      (.classMem (.cv n) (synCdif (synCnnc) (synCsn (synC0))))
      (synWne (.cv n) (synC0)) p0006 p0008
  have p0010 := @gVfintle (.cv n)
  have p0011 :=
    @gSyl3anc (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv n) (synCspfin)))
      (.classMem (synCvv) (synCfin)) (.classMem (.cv n) (synCnnc))
      (synWne (.cv n) (synC0))
      (.classMem (synCopk (synCtfin (.cv n)) (synCncfin (synC1c))) (synClefin)) p0000
      p0004 p0009 p0010
  have p0012 :=
    @gAd2ant2r (.classMem (synCvv) (synCfin)) (.classMem (.cv n) (synCspfin))
      (.classMem (synCopk (synCtfin (.cv n)) (synCncfin (synC1c))) (synClefin))
      (.classMem (synCtfin (.cv n)) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))
      p0011
  have p0013 := @gT1csfin1c
  have p0014 :=
    @gAdantr (.classMem (synCvv) (synCfin))
      (synWsfin (synCtfin (synCncfin (synC1c))) (synCncfin (synC1c)))
      (.classMem (synCtfin (.cv n)) (synCspfin)) p0013
  have p0015 :=
    @gSimpr (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))
  have p0016 :=
    @gSfinltfin (.cv z) (synCtfin (.cv n)) (synCtfin (synCncfin (synC1c)))
      (synCncfin (synC1c))
  have p0017 :=
    @gEx
      (synWa (synWsfin (synCtfin (synCncfin (synC1c))) (synCncfin (synC1c)))
        (synWsfin (.cv z) (synCtfin (.cv n))))
      (.classMem (synCopk (synCtfin (synCncfin (synC1c))) (.cv z)) (synCltfin))
      (.classMem (synCopk (synCncfin (synC1c)) (synCtfin (.cv n))) (synCltfin)) p0016
  have p0018 :=
    @gSyl2an
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (synCtfin (.cv n)) (synCspfin)))
      (synWsfin (synCtfin (synCncfin (synC1c))) (synCncfin (synC1c)))
      (synWsfin (.cv z) (synCtfin (.cv n)))
      (.imp (.classMem (synCopk (synCtfin (synCncfin (synC1c))) (.cv z)) (synCltfin))
        (.classMem (synCopk (synCncfin (synC1c)) (synCtfin (.cv n))) (synCltfin)))
      (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n))))
      p0014 p0015 p0017
  have p0019 :=
    @gCon3d
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCopk (synCtfin (synCncfin (synC1c))) (.cv z)) (synCltfin))
      (.classMem (synCopk (synCncfin (synC1c)) (synCtfin (.cv n))) (synCltfin)) p0018
  have p0020 :=
    @gAd2ant2r (.classMem (synCvv) (synCfin)) (.classMem (.cv n) (synCspfin))
      (.classMem (.cv n) (synCnnc)) (.classMem (synCtfin (.cv n)) (synCspfin))
      (synWsfin (.cv z) (synCtfin (.cv n))) p0004
  have p0021 := @gTfincl (.cv n)
  have p0022 :=
    @gSyl
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (.cv n) (synCnnc)) (.classMem (synCtfin (.cv n)) (synCnnc)) p0020
      p0021
  have p0023 := @gN1cex
  have p0024 := @gNcfinprop (synC1c) (synCvv)
  have p0025 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synC1c) (synCvv))
      (synWa (.classMem (synCncfin (synC1c)) (synCnnc))
        (.classMem (synC1c) (synCncfin (synC1c))))
      p0023 p0024
  have p0026 :=
    @gAd2antrr (.classMem (synCvv) (synCfin))
      (synWa (.classMem (synCncfin (synC1c)) (synCnnc))
        (.classMem (synC1c) (synCncfin (synC1c))))
      (.classMem (synCtfin (.cv n)) (synCspfin))
      (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n))))
      p0025
  have p0027 :=
    @gSimpld
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCncfin (synC1c)) (synCnnc))
      (.classMem (synC1c) (synCncfin (synC1c))) p0026
  have p0028 := @gLenltfin (synCtfin (.cv n)) (synCncfin (synC1c))
  have p0029 :=
    @gSyl2anc
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCtfin (.cv n)) (synCnnc))
      (.classMem (synCncfin (synC1c)) (synCnnc))
      (synWb (.classMem (synCopk (synCtfin (.cv n)) (synCncfin (synC1c))) (synClefin))
        (.neg (.classMem (synCopk (synCncfin (synC1c)) (synCtfin (.cv n))) (synCltfin))))
      p0022 p0027 p0028
  have p0030 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin (.cv z)
      (synCtfin (.cv n)) a dv_cache_0001 dv_cache_0002
  have p0031 :=
    @gSimp1bi (synWsfin (.cv z) (synCtfin (.cv n))) (.classMem (.cv z) (synCnnc))
      (.classMem (synCtfin (.cv n)) (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (.cv z))
          (.classMem (synCpw (.cv a)) (synCtfin (.cv n)))))
      p0030
  have p0032 :=
    @gAd2antll (synWsfin (.cv z) (synCtfin (.cv n))) (.classMem (.cv z) (synCnnc))
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (synCtfin (.cv n)) (synCspfin)))
      (.classMem (.cv n) (synCspfin)) p0031
  have p0033 := @gTfincl (synCncfin (synC1c))
  have p0034 :=
    @gSyl
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCncfin (synC1c)) (synCnnc))
      (.classMem (synCtfin (synCncfin (synC1c))) (synCnnc)) p0027 p0033
  have p0035 := @gLenltfin (.cv z) (synCtfin (synCncfin (synC1c)))
  have p0036 :=
    @gSyl2anc
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (.cv z) (synCnnc))
      (.classMem (synCtfin (synCncfin (synC1c))) (synCnnc))
      (synWb (.classMem (synCopk (.cv z) (synCtfin (synCncfin (synC1c)))) (synClefin))
        (.neg (.classMem (synCopk (synCtfin (synCncfin (synC1c))) (.cv z)) (synCltfin))))
      p0032 p0034 p0035
  have p0037 :=
    @gN3imtr4d
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.neg (.classMem (synCopk (synCncfin (synC1c)) (synCtfin (.cv n))) (synCltfin)))
      (.neg (.classMem (synCopk (synCtfin (synCncfin (synC1c))) (.cv z)) (synCltfin)))
      (.classMem (synCopk (synCtfin (.cv n)) (synCncfin (synC1c))) (synClefin))
      (.classMem (synCopk (.cv z) (synCtfin (synCncfin (synC1c)))) (synClefin)) p0019
      p0029 p0036
  have p0038 :=
    @gMpd
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCopk (synCtfin (.cv n)) (synCncfin (synC1c))) (synClefin))
      (.classMem (synCopk (.cv z) (synCtfin (synCncfin (synC1c)))) (synClefin)) p0012
      p0037
  have p0039 := @gVex z
  have p0040 := @gTfinex (synCncfin (synC1c))
  have p0041 :=
    @gOpklefing p (.cv z) (synCtfin (synCncfin (synC1c))) (synCvv) (synCvv)
      dv_cache_0003 dv_cache_0004
  have p0042 :=
    @gMp2an (.classMem (.cv z) (synCvv))
      (.classMem (synCtfin (synCncfin (synC1c))) (synCvv))
      (synWb (.classMem (synCopk (.cv z) (synCtfin (synCncfin (synC1c)))) (synClefin))
        (synWrex p (synCnnc)
          (.classEq (synCtfin (synCncfin (synC1c))) (synCplc (.cv z) (.cv p)))))
      p0039 p0040 p0041
  have p0043 :=
    @gSylib
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCopk (.cv z) (synCtfin (synCncfin (synC1c)))) (synClefin))
      (synWrex p (synCnnc)
        (.classEq (synCtfin (synCncfin (synC1c))) (synCplc (.cv z) (.cv p))))
      p0038 p0042
  have p0044 := @gDf1c2
  have p0045 := @gPw1eq (synC1c) (synCpw1 (synCvv))
  have p0046 := Nominal.mp p0044 p0045
  have p0047 := @gTfinpw1 (synC1c) (synCncfin (synC1c))
  have p0048 :=
    @gSyl
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (synWa (.classMem (synCncfin (synC1c)) (synCnnc))
        (.classMem (synC1c) (synCncfin (synC1c))))
      (.classMem (synCpw1 (synC1c)) (synCtfin (synCncfin (synC1c)))) p0026 p0047
  have p0049 :=
    @gSyl5eqelr
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (synCpw1 (synCpw1 (synCvv))) (synCpw1 (synC1c))
      (synCtfin (synCncfin (synC1c))) p0046 p0048
  have p0050 :=
    @gEleq2 (synCtfin (synCncfin (synC1c))) (synCplc (.cv z) (.cv p))
      (synCpw1 (synCpw1 (synCvv)))
  have p0051 :=
    @gSyl5ibcom
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCpw1 (synCpw1 (synCvv))) (synCtfin (synCncfin (synC1c))))
      (.classEq (synCtfin (synCncfin (synC1c))) (synCplc (.cv z) (.cv p)))
      (.classMem (synCpw1 (synCpw1 (synCvv))) (synCplc (.cv z) (.cv p))) p0049 p0050
  have p0052 :=
    @gEladdc (synCpw1 (synCpw1 (synCvv))) (.cv z) (.cv p) a b dv_cache_0005
      dv_cache_0006 dv_cache_0001 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0053 := @gSsun1 (.cv a) (.cv b)
  have p0054 := @gSseq2 (synCpw1 (synCpw1 (synCvv))) (synCun (.cv a) (.cv b)) (.cv a)
  have p0055 :=
    @gMpbiri (.classEq (synCpw1 (synCpw1 (synCvv))) (synCun (.cv a) (.cv b)))
      (synWss (.cv a) (synCpw1 (synCpw1 (synCvv))))
      (synWss (.cv a) (synCun (.cv a) (.cv b))) p0053 p0054
  have p0056 := @gVex a
  have p0057 := @gSspw1 g (.cv a) (synCpw1 (synCvv)) dv_cache_0011 dv_cache_0012 p0056
  have p0058 := @gVex g
  have p0059 := @gSspw1 d (.cv g) (synCvv) dv_cache_0013 dv_cache_0014 p0058
  have p0060 := @gSsv (.cv d)
  have p0061 :=
    @gBiantrur (synWss (.cv d) (synCvv)) (.classEq (.cv g) (synCpw1 (.cv d))) p0060
  have p0062 :=
    @gExbii (.classEq (.cv g) (synCpw1 (.cv d)))
      (synWa (synWss (.cv d) (synCvv)) (.classEq (.cv g) (synCpw1 (.cv d)))) d p0061
  have p0063 :=
    @gBitr4i (synWss (.cv g) (synCpw1 (synCvv)))
      (synWex d (synWa (synWss (.cv d) (synCvv)) (.classEq (.cv g) (synCpw1 (.cv d)))))
      (synWex d (.classEq (.cv g) (synCpw1 (.cv d)))) p0059 p0062
  have p0064 :=
    @gAnbi1i (synWss (.cv g) (synCpw1 (synCvv)))
      (synWex d (.classEq (.cv g) (synCpw1 (.cv d))))
      (.classEq (.cv a) (synCpw1 (.cv g))) p0063
  have p0065 :=
    @gN1941v (.classEq (.cv g) (synCpw1 (.cv d)))
      (.classEq (.cv a) (synCpw1 (.cv g))) d dv_cache_0015
  have p0066 :=
    @gBitr4i
      (synWa (synWss (.cv g) (synCpw1 (synCvv))) (.classEq (.cv a) (synCpw1 (.cv g))))
      (synWa (synWex d (.classEq (.cv g) (synCpw1 (.cv d))))
        (.classEq (.cv a) (synCpw1 (.cv g))))
      (synWex d (synWa (.classEq (.cv g) (synCpw1 (.cv d)))
          (.classEq (.cv a) (synCpw1 (.cv g)))))
      p0064 p0065
  have p0067 :=
    @gExbii
      (synWa (synWss (.cv g) (synCpw1 (synCvv))) (.classEq (.cv a) (synCpw1 (.cv g))))
      (synWex d (synWa (.classEq (.cv g) (synCpw1 (.cv d)))
          (.classEq (.cv a) (synCpw1 (.cv g)))))
      g p0066
  have p0068 :=
    @gExcom
      (synWa (.classEq (.cv g) (synCpw1 (.cv d))) (.classEq (.cv a) (synCpw1 (.cv g))))
      g d
  have p0069 := @gVex d
  have p0070 := @gPw1ex (.cv d) p0069
  have p0071 := @gPw1eq (.cv g) (synCpw1 (.cv d))
  have p0072 :=
    @gEqeq2d (.classEq (.cv g) (synCpw1 (.cv d))) (synCpw1 (.cv g))
      (synCpw1 (synCpw1 (.cv d))) (.cv a) p0071
  have p0073 :=
    @gCeqsexv (.classEq (.cv a) (synCpw1 (.cv g)))
      (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d)))) g (synCpw1 (.cv d)) dv_cache_0016
      dv_cache_0017 p0070 p0072
  have p0074 :=
    @gExbii
      (synWex g (synWa (.classEq (.cv g) (synCpw1 (.cv d)))
          (.classEq (.cv a) (synCpw1 (.cv g)))))
      (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d)))) d p0073
  have p0075 :=
    @gBitri
      (synWex g (synWex d (synWa (.classEq (.cv g) (synCpw1 (.cv d)))
            (.classEq (.cv a) (synCpw1 (.cv g))))))
      (synWex d (synWex g (synWa (.classEq (.cv g) (synCpw1 (.cv d)))
            (.classEq (.cv a) (synCpw1 (.cv g))))))
      (synWex d (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d))))) p0068 p0074
  have p0076 :=
    @gN3bitri (synWss (.cv a) (synCpw1 (synCpw1 (synCvv))))
      (synWex g (synWa (synWss (.cv g) (synCpw1 (synCvv)))
          (.classEq (.cv a) (synCpw1 (.cv g)))))
      (synWex g (synWex d (synWa (.classEq (.cv g) (synCpw1 (.cv d)))
            (.classEq (.cv a) (synCpw1 (.cv g))))))
      (synWex d (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d))))) p0057 p0067 p0075
  have p0077 :=
    @gSylib (.classEq (synCpw1 (synCpw1 (synCvv))) (synCun (.cv a) (.cv b)))
      (synWss (.cv a) (synCpw1 (synCpw1 (synCvv))))
      (synWex d (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d))))) p0055 p0076
  have p0078 := @gEleq1 (.cv a) (synCpw1 (synCpw1 (.cv d))) (.cv z)
  have p0079_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d))))
        (synWb (.objMem a z) (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw1 synCin synCcompl synCnin synWnan synWa synCpw synWss
          synC1c synWex synCsn synWb
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
      p0078
  have p0079 :=
    @gBiimpac (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d)))) (.objMem a z)
      (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z)) p0079_e00_recanon
  have p0080 :=
    @gAdantr
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (.cv z) (synCnnc)) (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z))
      p0032
  have p0081 := @gNcfinprop (synCpw1 (.cv d)) (synCvv)
  have p0082 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCpw1 (.cv d)) (synCvv))
      (synWa (.classMem (synCncfin (synCpw1 (.cv d))) (synCnnc))
        (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d)))))
      p0070 p0081
  have p0083 :=
    @gAd2antrr (.classMem (synCvv) (synCfin))
      (synWa (.classMem (synCncfin (synCpw1 (.cv d))) (synCnnc))
        (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d)))))
      (.classMem (synCtfin (.cv n)) (synCspfin))
      (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n))))
      p0082
  have p0084 :=
    @gSimpld
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCncfin (synCpw1 (.cv d))) (synCnnc))
      (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d)))) p0083
  have p0085 := @gTfincl (synCncfin (synCpw1 (.cv d)))
  have p0086 :=
    @gSyl
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCncfin (synCpw1 (.cv d))) (synCnnc))
      (.classMem (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCnnc)) p0084 p0085
  have p0087 :=
    @gAdantr
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCnnc))
      (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z)) p0086
  have p0088 :=
    @gSimpr
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z))
  have p0089 := @gTfinpw1 (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d)))
  have p0090 :=
    @gSyl
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (synWa (.classMem (synCncfin (synCpw1 (.cv d))) (synCnnc))
        (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d)))))
      (.classMem (synCpw1 (synCpw1 (.cv d))) (synCtfin (synCncfin (synCpw1 (.cv d)))))
      p0083 p0089
  have p0091 :=
    @gAdantr
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCpw1 (synCpw1 (.cv d))) (synCtfin (synCncfin (synCpw1 (.cv d)))))
      (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z)) p0090
  have p0092 :=
    @gNnceleq (synCpw1 (synCpw1 (.cv d))) (.cv z)
      (synCtfin (synCncfin (synCpw1 (.cv d))))
  have p0093 :=
    @gSyl22anc
      (synWa (synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin)))
          (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
        (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z)))
      (.classMem (.cv z) (synCnnc))
      (.classMem (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCnnc))
      (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z))
      (.classMem (synCpw1 (synCpw1 (.cv d))) (synCtfin (synCncfin (synCpw1 (.cv d)))))
      (.classEq (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d))))) p0080 p0087 p0088
      p0091 p0092
  have p0094 :=
    @gEx
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z))
      (.classEq (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d))))) p0093
  have p0095 :=
    @gAd2ant2r (.classMem (synCvv) (synCfin)) (.classMem (.cv n) (synCspfin))
      (.classMem (.cv n) (synCnnc)) (.classMem (synCtfin (.cv n)) (synCspfin))
      (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n))) p0004
  have p0096 := @gPwex (.cv d) p0069
  have p0097 := @gNcfinprop (synCpw (.cv d)) (synCvv)
  have p0098 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCpw (.cv d)) (synCvv))
      (synWa (.classMem (synCncfin (synCpw (.cv d))) (synCnnc))
        (.classMem (synCpw (.cv d)) (synCncfin (synCpw (.cv d)))))
      p0096 p0097
  have p0099 :=
    @gSimpld (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCpw (.cv d))) (synCnnc))
      (.classMem (synCpw (.cv d)) (synCncfin (synCpw (.cv d)))) p0098
  have p0100 :=
    @gAd2antrr (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCpw (.cv d))) (synCnnc))
      (.classMem (synCtfin (.cv n)) (synCspfin))
      (synWa (.classMem (.cv n) (synCspfin))
        (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n))))
      p0099
  have p0101 :=
    @gSimprr
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (synCtfin (.cv n)) (synCspfin)))
      (.classMem (.cv n) (synCspfin))
      (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))
  have p0102 :=
    @gSimpld (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCpw1 (.cv d))) (synCnnc))
      (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d)))) p0082
  have p0103 :=
    @gSimprd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCpw1 (.cv d))) (synCnnc))
      (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d)))) p0082
  have p0104 :=
    @gSimprd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCpw (.cv d))) (synCnnc))
      (.classMem (synCpw (.cv d)) (synCncfin (synCpw (.cv d)))) p0098
  have p0105 := @gPw1eq (.cv a) (.cv d)
  have p0106_e00_recanon :
    Nominal.NPrf (.imp (.objEq a d) (.classEq (synCpw1 (.cv a)) (synCpw1 (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw1 synCin synCcompl synCnin synWnan synWa synCpw synWss
          synC1c synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0105
  have p0106 :=
    @gEleq1d (.objEq a d) (synCpw1 (.cv a)) (synCpw1 (.cv d))
      (synCncfin (synCpw1 (.cv d))) p0106_e00_recanon
  have p0107 := @gPweq (.cv a) (.cv d)
  have p0108_e00_recanon :
    Nominal.NPrf (.imp (.objEq a d) (.classEq (synCpw (.cv a)) (synCpw (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCpw synWss synCin synCcompl synCnin synWnan synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0107
  have p0108 :=
    @gEleq1d (.objEq a d) (synCpw (.cv a)) (synCpw (.cv d))
      (synCncfin (synCpw (.cv d))) p0108_e00_recanon
  have p0109 :=
    @gAnbi12d (.objEq a d) (.classMem (synCpw1 (.cv a)) (synCncfin (synCpw1 (.cv d))))
      (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d))))
      (.classMem (synCpw (.cv a)) (synCncfin (synCpw (.cv d))))
      (.classMem (synCpw (.cv d)) (synCncfin (synCpw (.cv d)))) p0106 p0108
  have p0110_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv d)) (synWb
          (synWa (.classMem (synCpw1 (.cv a)) (synCncfin (synCpw1 (.cv d))))
            (.classMem (synCpw (.cv a)) (synCncfin (synCpw (.cv d)))))
          (synWa (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d))))
            (.classMem (synCpw (.cv d)) (synCncfin (synCpw (.cv d))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWa synCpw1 synCin synCcompl synCnin synWnan synCpw synWss
          synC1c synWex synCsn synCncfin synCio synCuni
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0109
  have p0110 :=
    @gSpcev
      (synWa (.classMem (synCpw1 (.cv a)) (synCncfin (synCpw1 (.cv d))))
        (.classMem (synCpw (.cv a)) (synCncfin (synCpw (.cv d)))))
      (synWa (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d))))
        (.classMem (synCpw (.cv d)) (synCncfin (synCpw (.cv d)))))
      a (.cv d) dv_cache_0018 dv_cache_0019 p0069 p0110_e01_recanon
  have p0111 :=
    @gSyl2anc (.classMem (synCvv) (synCfin))
      (.classMem (synCpw1 (.cv d)) (synCncfin (synCpw1 (.cv d))))
      (.classMem (synCpw (.cv d)) (synCncfin (synCpw (.cv d))))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCncfin (synCpw1 (.cv d))))
          (.classMem (synCpw (.cv a)) (synCncfin (synCpw (.cv d))))))
      p0103 p0104 p0110
  have p0112 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin
      (synCncfin (synCpw1 (.cv d))) (synCncfin (synCpw (.cv d))) a dv_cache_0020
      dv_cache_0021
  have p0113 :=
    @gSyl3anbrc (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCpw1 (.cv d))) (synCnnc))
      (.classMem (synCncfin (synCpw (.cv d))) (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCncfin (synCpw1 (.cv d))))
          (.classMem (synCpw (.cv a)) (synCncfin (synCpw (.cv d))))))
      (synWsfin (synCncfin (synCpw1 (.cv d))) (synCncfin (synCpw (.cv d)))) p0102
      p0099 p0111 p0112
  have p0114 :=
    @gAd2antrr (.classMem (synCvv) (synCfin))
      (synWsfin (synCncfin (synCpw1 (.cv d))) (synCncfin (synCpw (.cv d))))
      (.classMem (synCtfin (.cv n)) (synCspfin))
      (synWa (.classMem (.cv n) (synCspfin))
        (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n))))
      p0113
  have p0115 := @gSfintfin (synCncfin (synCpw1 (.cv d))) (synCncfin (synCpw (.cv d)))
  have p0116 :=
    @gSyl
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin))) (synWa (.classMem (.cv n) (synCspfin))
          (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))))
      (synWsfin (synCncfin (synCpw1 (.cv d))) (synCncfin (synCpw (.cv d))))
      (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d))))
        (synCtfin (synCncfin (synCpw (.cv d)))))
      p0114 p0115
  have p0117 :=
    @gSfin112 (synCtfin (synCncfin (synCpw (.cv d))))
      (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n))
  have p0118 :=
    @gSyl2anc
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin))) (synWa (.classMem (.cv n) (synCspfin))
          (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))))
      (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))
      (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d))))
        (synCtfin (synCncfin (synCpw (.cv d)))))
      (.classEq (synCtfin (.cv n)) (synCtfin (synCncfin (synCpw (.cv d))))) p0101
      p0116 p0117
  have p0119 := @gTfin11 (.cv n) (synCncfin (synCpw (.cv d)))
  have p0120 :=
    @gSyl3anc
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin))) (synWa (.classMem (.cv n) (synCspfin))
          (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))))
      (.classMem (.cv n) (synCnnc)) (.classMem (synCncfin (synCpw (.cv d))) (synCnnc))
      (.classEq (synCtfin (.cv n)) (synCtfin (synCncfin (synCpw (.cv d)))))
      (.classEq (.cv n) (synCncfin (synCpw (.cv d)))) p0095 p0100 p0118 p0119
  have p0121 :=
    @gSimprl
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (synCtfin (.cv n)) (synCspfin)))
      (.classMem (.cv n) (synCspfin))
      (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))
  have p0122 :=
    @gEqeltrrd
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin))) (synWa (.classMem (.cv n) (synCspfin))
          (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))))
      (.cv n) (synCncfin (synCpw (.cv d))) (synCspfin) p0120 p0121
  have p0123 :=
    @gSpfinsfincl (synCncfin (synCpw (.cv d))) (synCncfin (synCpw1 (.cv d)))
  have p0124 :=
    @gSyl2anc
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin))) (synWa (.classMem (.cv n) (synCspfin))
          (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))))
      (.classMem (synCncfin (synCpw (.cv d))) (synCspfin))
      (synWsfin (synCncfin (synCpw1 (.cv d))) (synCncfin (synCpw (.cv d))))
      (.classMem (synCncfin (synCpw1 (.cv d))) (synCspfin)) p0122 p0114 p0123
  have p0125 :=
    @gRisset x (synCncfin (synCpw1 (.cv d))) (synCspfin) dv_cache_0022 dv_cache_0023
  have p0126 := @gTfineq (.cv x) (synCncfin (synCpw1 (.cv d)))
  have p0127 :=
    @gEqcomd (.classEq (.cv x) (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv x))
      (synCtfin (synCncfin (synCpw1 (.cv d)))) p0126
  have p0128 :=
    @gReximi (.classEq (.cv x) (synCncfin (synCpw1 (.cv d))))
      (.classEq (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv x))) x
      (synCspfin) p0127
  have p0129 :=
    @gSylbi (.classMem (synCncfin (synCpw1 (.cv d))) (synCspfin))
      (synWrex x (synCspfin) (.classEq (.cv x) (synCncfin (synCpw1 (.cv d)))))
      (synWrex x (synCspfin)
        (.classEq (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv x))))
      p0125 p0128
  have p0130 :=
    @gSyl
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin))) (synWa (.classMem (.cv n) (synCspfin))
          (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))))
      (.classMem (synCncfin (synCpw1 (.cv d))) (synCspfin))
      (synWrex x (synCspfin)
        (.classEq (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv x))))
      p0124 p0129
  have p0131 :=
    @gSfineq1 (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n))
  have p0132 :=
    @gAnbi2d (.classEq (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d)))))
      (synWsfin (.cv z) (synCtfin (.cv n)))
      (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))
      (.classMem (.cv n) (synCspfin)) p0131
  have p0133 :=
    @gAnbi2d (.classEq (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d)))))
      (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n))))
      (synWa (.classMem (.cv n) (synCspfin))
        (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n))))
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (synCtfin (.cv n)) (synCspfin)))
      p0132
  have p0134 :=
    @gEqeq1 (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv x))
  have p0135 :=
    @gRexbidv (.classEq (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d)))))
      (.classEq (.cv z) (synCtfin (.cv x)))
      (.classEq (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv x))) x
      (synCspfin) dv_cache_0024 p0134
  have p0136 :=
    @gImbi12d (.classEq (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d)))))
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin))) (synWa (.classMem (.cv n) (synCspfin))
          (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))
      (synWrex x (synCspfin)
        (.classEq (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv x))))
      p0133 p0135
  have p0137 :=
    @gMpbiri (.classEq (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d)))))
      (.imp (synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin)))
          (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
        (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))
      (.imp (synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin)))
          (synWa (.classMem (.cv n) (synCspfin))
            (synWsfin (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv n)))))
        (synWrex x (synCspfin)
          (.classEq (synCtfin (synCncfin (synCpw1 (.cv d)))) (synCtfin (.cv x)))))
      p0130 p0136
  have p0138 :=
    @gCom12 (.classEq (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d)))))
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0137
  have p0139 :=
    @gSyld
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z))
      (.classEq (.cv z) (synCtfin (synCncfin (synCpw1 (.cv d)))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0094 p0138
  have p0140 :=
    @gSyl5 (synWa (.objMem a z) (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d)))))
      (.classMem (synCpw1 (synCpw1 (.cv d))) (.cv z))
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0079 p0139
  have p0141 :=
    @gExpdimp
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.objMem a z) (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0140
  have p0142 :=
    @gExlimdv
      (synWa (synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin)))
          (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
        (.objMem a z))
      (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) d dv_cache_0025
      dv_cache_0026 p0141
  have p0143 :=
    @gSyl5 (.classEq (synCpw1 (synCpw1 (synCvv))) (synCun (.cv a) (.cv b)))
      (synWex d (.classEq (.cv a) (synCpw1 (synCpw1 (.cv d)))))
      (synWa (synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin)))
          (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
        (.objMem a z))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0077 p0142
  have p0144 :=
    @gAdantld
      (synWa (synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin)))
          (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
        (.objMem a z))
      (.classEq (synCpw1 (synCpw1 (synCvv))) (synCun (.cv a) (.cv b)))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))
      (.classEq (synCin (.cv a) (.cv b)) (synC0)) p0143
  have p0145 :=
    @gAdantrr
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.objMem a z)
      (.imp (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
          (.classEq (synCpw1 (synCpw1 (synCvv))) (synCun (.cv a) (.cv b))))
        (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))
      (.objMem b p) p0144
  have p0146_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (synWa (.classMem (synCvv) (synCfin))
              (.classMem (synCtfin (.cv n)) (synCspfin)))
            (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
          (synWa (.classMem (.cv a) (.cv z)) (.classMem (.cv b) (.cv p)))) (.imp
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (synCpw1 (synCpw1 (synCvv))) (synCun (.cv a) (.cv b))))
          (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synWrex synWex synCspfin synCint synCtfin synCif synWo synC0
          synCdif synCin synCcompl synCnin synWnan synCvv synCio synCuni synCsn
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.objMem_classMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0145
  have p0146 :=
    @gRexlimdvva
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
        (.classEq (synCpw1 (synCpw1 (synCvv))) (synCun (.cv a) (.cv b))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) a b (.cv z) (.cv p)
      dv_cache_0007 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0010
      p0146_e00_recanon
  have p0147 :=
    @gSyl5bi (.classMem (synCpw1 (synCpw1 (synCvv))) (synCplc (.cv z) (.cv p)))
      (synWrex a (.cv z) (synWrex b (.cv p)
          (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
            (.classEq (synCpw1 (synCpw1 (synCvv))) (synCun (.cv a) (.cv b))))))
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0052 p0146
  have p0148 :=
    @gSyld
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classEq (synCtfin (synCncfin (synC1c))) (synCplc (.cv z) (.cv p)))
      (.classMem (synCpw1 (synCpw1 (synCvv))) (synCplc (.cv z) (.cv p)))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0051 p0147
  have p0149 :=
    @gRexlimdvw
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (.classEq (synCtfin (synCncfin (synC1c))) (synCplc (.cv z) (.cv p)))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p (synCnnc)
      dv_cache_0031 dv_cache_0032 p0148
  have p0150 :=
    @gMpd
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin)))
        (synWa (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))))
      (synWrex p (synCnnc)
        (.classEq (synCtfin (synCncfin (synC1c))) (synCplc (.cv z) (.cv p))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0043 p0149
  exact p0150


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part024`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_vfinspss`. -/
@[expose]
noncomputable def gVfinspss (x : Var) (a : Var) (dv_a_x : a ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (synCvv) (synCfin)) (synWss (synCspfin) (synCun
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCncfin (synCvv)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ a } : Finset Var)
  let w : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_a : w ≠ a := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_w : a ≠ w := Ne.symm fresh_w_ne_a
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_a : z ≠ a := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_n_ne_x : n ≠ x := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_a : t ≠ a := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w_ne_z : w ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_w_ne_n : w ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_w : n ≠ w := Ne.symm fresh_w_ne_n
  have fresh_z_ne_n : z ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_z : n ≠ z := Ne.symm fresh_z_ne_n
  have dv_cache_0001 : x ∉ ((synCspfin)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((synCspfin)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((Wff.classEq (.cv w) (synCtfin (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_w, fresh_n_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv w) (synCtfin (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_w, fresh_x_ne_n, or_false, not_false_eq_true])
  have dv_cache_0005 : n ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0006 : n ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show n ≠ z from (by exact fresh_n_ne_z))
  have dv_cache_0007 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0008 :
    n ∉
      ((Wff.imp (synWsfin (.cv z) (.cv w))
          (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_z, fresh_n_ne_w,
          fresh_n_ne_x, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0009 :
    n ∉ ((synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_w, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 : x ∉ ((synCncfin (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0011 :
    x ∉ ((Wff.classEq (synCncfin (synC1c)) (synCtfin (synCncfin (synCvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((Wff.classEq (synCncfin (synC1c)) (.cv z))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 : x ∉ ((Wff.objEq a w)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, (Ne.symm dv_a_x), fresh_x_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0014 : a ∉ ((Class.cv w)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_w, not_false_eq_true])
  have dv_cache_0015 :
    a ∉ ((synWrex x (synCspfin) (.classEq (.cv w) (synCtfin (.cv x))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_w, dv_a_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Wff.objEq a z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, (Ne.symm dv_a_x), fresh_x_ne_z, or_false,
          not_false_eq_true])
  have dv_cache_0017 : a ∉ ((Class.cv z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_z, not_false_eq_true])
  have dv_cache_0018 :
    a ∉ ((synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_z, dv_a_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0019 :
    z ∉ ((synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0020 : w ∉ ((Wff.classMem (synCvv) (synCfin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 :
    t ∉
      ((synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif (synCcompl
              (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : t ∉ ((synCpw1 (synCspfin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0023 : t ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_a, not_false_eq_true])
  have dv_cache_0024 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0025 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (.cv a))
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, (Ne.symm dv_a_x), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0026 : t ∉ ((synCspfin)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0027 : x ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show x ≠ t from (by exact fresh_x_ne_t))
  have dv_cache_0028 : t ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0029 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (.cv x)) (.cv a))
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_a, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0030 :
    a ∉
      ((synCimak (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))
          (synCpw1 (synCspfin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0031 :
    w ∉
      ((synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_a, fresh_w_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0032 :
    z ∉
      ((synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_a, fresh_z_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0033 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have p0000 := @gTfineq (.cv x) (.cv n)
  have p0001_e00_recanon :
    Nominal.NPrf (.imp (.objEq x n) (.classEq (synCtfin (.cv x)) (synCtfin (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCtfin synCif synWo synWa synC0 synCdif synCin synCcompl synCnin
          synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0001 :=
    @gEqeq2d (.objEq x n) (synCtfin (.cv x)) (synCtfin (.cv n)) (.cv w)
      p0001_e00_recanon
  have p0002 :=
    @gCbvrexv (.classEq (.cv w) (synCtfin (.cv x)))
      (.classEq (.cv w) (synCtfin (.cv n))) x n (synCspfin) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 p0001
  have p0003 := @gVfinspsslem1 x z n dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @gExpr
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (synCtfin (.cv n)) (synCspfin)))
      (.classMem (.cv n) (synCspfin)) (synWsfin (.cv z) (synCtfin (.cv n)))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0003
  have p0005 := @gEleq1 (.cv w) (synCtfin (.cv n)) (synCspfin)
  have p0006 :=
    @gAnbi2d (.classEq (.cv w) (synCtfin (.cv n))) (.classMem (.cv w) (synCspfin))
      (.classMem (synCtfin (.cv n)) (synCspfin)) (.classMem (synCvv) (synCfin)) p0005
  have p0007 :=
    @gAnbi1d (.classEq (.cv w) (synCtfin (.cv n)))
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (synCtfin (.cv n)) (synCspfin)))
      (.classMem (.cv n) (synCspfin)) p0006
  have p0008 := @gSfineq2 (.cv w) (synCtfin (.cv n)) (.cv z)
  have p0009 :=
    @gImbi1d (.classEq (.cv w) (synCtfin (.cv n))) (synWsfin (.cv z) (.cv w))
      (synWsfin (.cv z) (synCtfin (.cv n)))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0008
  have p0010 :=
    @gImbi12d (.classEq (.cv w) (synCtfin (.cv n)))
      (synWa (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
        (.classMem (.cv n) (synCspfin)))
      (synWa (synWa (.classMem (synCvv) (synCfin))
          (.classMem (synCtfin (.cv n)) (synCspfin))) (.classMem (.cv n) (synCspfin)))
      (.imp (synWsfin (.cv z) (.cv w))
        (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))
      (.imp (synWsfin (.cv z) (synCtfin (.cv n)))
        (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))
      p0007 p0009
  have p0011 :=
    @gMpbiri (.classEq (.cv w) (synCtfin (.cv n)))
      (.imp (synWa (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
          (.classMem (.cv n) (synCspfin))) (.imp (synWsfin (.cv z) (.cv w))
          (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))))
      (.imp (synWa (synWa (.classMem (synCvv) (synCfin))
            (.classMem (synCtfin (.cv n)) (synCspfin))) (.classMem (.cv n) (synCspfin)))
        (.imp (synWsfin (.cv z) (synCtfin (.cv n)))
          (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))))
      p0004 p0010
  have p0012 :=
    @gCom12 (.classEq (.cv w) (synCtfin (.cv n)))
      (synWa (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
        (.classMem (.cv n) (synCspfin)))
      (.imp (synWsfin (.cv z) (.cv w))
        (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))
      p0011
  have p0013 :=
    @gRexlimdva
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
      (.classEq (.cv w) (synCtfin (.cv n)))
      (.imp (synWsfin (.cv z) (.cv w))
        (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))
      n (synCspfin) dv_cache_0008 dv_cache_0009 p0012
  have p0014 :=
    @gSyl5bi (synWrex x (synCspfin) (.classEq (.cv w) (synCtfin (.cv x))))
      (synWrex n (synCspfin) (.classEq (.cv w) (synCtfin (.cv n))))
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
      (.imp (synWsfin (.cv z) (.cv w))
        (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))
      p0002 p0013
  have p0015 := @gSfineq2 (.cv w) (synCncfin (synCvv)) (.cv z)
  have p0016 :=
    @gBiimpa (.classEq (.cv w) (synCncfin (synCvv))) (synWsfin (.cv z) (.cv w))
      (synWsfin (.cv z) (synCncfin (synCvv))) p0015
  have p0017 := @gN1cvsfin
  have p0018 := @gSfin111 (synCncfin (synCvv)) (synCncfin (synC1c)) (.cv z)
  have p0019 := @gTncveqnc1fin
  have p0020 :=
    @gEqcomd (.classMem (synCvv) (synCfin)) (synCtfin (synCncfin (synCvv)))
      (synCncfin (synC1c)) p0019
  have p0021 := @gNcvspfin
  have p0022 := @gTfineq (.cv x) (synCncfin (synCvv))
  have p0023 :=
    @gEqeq2d (.classEq (.cv x) (synCncfin (synCvv))) (synCtfin (.cv x))
      (synCtfin (synCncfin (synCvv))) (synCncfin (synC1c)) p0022
  have p0024 :=
    @gRspcev (.classEq (synCncfin (synC1c)) (synCtfin (.cv x)))
      (.classEq (synCncfin (synC1c)) (synCtfin (synCncfin (synCvv)))) x
      (synCncfin (synCvv)) (synCspfin) dv_cache_0010 dv_cache_0001 dv_cache_0011 p0023
  have p0025 :=
    @gMpan (.classMem (synCncfin (synCvv)) (synCspfin))
      (.classEq (synCncfin (synC1c)) (synCtfin (synCncfin (synCvv))))
      (synWrex x (synCspfin) (.classEq (synCncfin (synC1c)) (synCtfin (.cv x))))
      p0021 p0024
  have p0026 :=
    @gSyl (.classMem (synCvv) (synCfin))
      (.classEq (synCncfin (synC1c)) (synCtfin (synCncfin (synCvv))))
      (synWrex x (synCspfin) (.classEq (synCncfin (synC1c)) (synCtfin (.cv x))))
      p0020 p0025
  have p0027 := @gEqeq1 (synCncfin (synC1c)) (.cv z) (synCtfin (.cv x))
  have p0028 :=
    @gRexbidv (.classEq (synCncfin (synC1c)) (.cv z))
      (.classEq (synCncfin (synC1c)) (synCtfin (.cv x)))
      (.classEq (.cv z) (synCtfin (.cv x))) x (synCspfin) dv_cache_0012 p0027
  have p0029 :=
    @gBiimpd (.classEq (synCncfin (synC1c)) (.cv z))
      (synWrex x (synCspfin) (.classEq (synCncfin (synC1c)) (synCtfin (.cv x))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0028
  have p0030 :=
    @gCom12 (.classEq (synCncfin (synC1c)) (.cv z))
      (synWrex x (synCspfin) (.classEq (synCncfin (synC1c)) (synCtfin (.cv x))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0029
  have p0031 :=
    @gSyl (.classMem (synCvv) (synCfin))
      (synWrex x (synCspfin) (.classEq (synCncfin (synC1c)) (synCtfin (.cv x))))
      (.imp (.classEq (synCncfin (synC1c)) (.cv z))
        (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))
      p0026 p0030
  have p0032 :=
    @gSyl5
      (synWa (synWsfin (synCncfin (synC1c)) (synCncfin (synCvv)))
        (synWsfin (.cv z) (synCncfin (synCvv))))
      (.classEq (synCncfin (synC1c)) (.cv z)) (.classMem (synCvv) (synCfin))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0018 p0031
  have p0033 :=
    @gMpand (.classMem (synCvv) (synCfin))
      (synWsfin (synCncfin (synC1c)) (synCncfin (synCvv)))
      (synWsfin (.cv z) (synCncfin (synCvv)))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0017 p0032
  have p0034 :=
    @gSyl5 (synWa (.classEq (.cv w) (synCncfin (synCvv))) (synWsfin (.cv z) (.cv w)))
      (synWsfin (.cv z) (synCncfin (synCvv))) (.classMem (synCvv) (synCfin))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0016 p0033
  have p0035 :=
    @gExp3a (.classMem (synCvv) (synCfin)) (.classEq (.cv w) (synCncfin (synCvv)))
      (synWsfin (.cv z) (.cv w))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0034
  have p0036 :=
    @gAdantr (.classMem (synCvv) (synCfin))
      (.imp (.classEq (.cv w) (synCncfin (synCvv))) (.imp (synWsfin (.cv z) (.cv w))
          (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))))
      (.classMem (.cv w) (synCspfin)) p0035
  have p0037 :=
    @gJaod (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
      (synWrex x (synCspfin) (.classEq (.cv w) (synCtfin (.cv x))))
      (.imp (synWsfin (.cv z) (.cv w))
        (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))
      (.classEq (.cv w) (synCncfin (synCvv))) p0014 p0036
  have p0038 :=
    @gImp3a (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
      (synWo (synWrex x (synCspfin) (.classEq (.cv w) (synCtfin (.cv x))))
        (.classEq (.cv w) (synCncfin (synCvv))))
      (synWsfin (.cv z) (.cv w))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) p0037
  have p0039 :=
    @gElun (.cv w)
      (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCsn (synCncfin (synCvv)))
  have p0040 := @gVex w
  have p0041 := @gEqeq1 (.cv a) (.cv w) (synCtfin (.cv x))
  have p0042_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a w) (synWb (.classEq (.cv a) (synCtfin (.cv x)))
          (.classEq (.cv w) (synCtfin (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCtfin synCif synWo synWa synC0 synCdif synCin synCcompl
          synCnin synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0041
  have p0042 :=
    @gRexbidv (.objEq a w) (.classEq (.cv a) (synCtfin (.cv x)))
      (.classEq (.cv w) (synCtfin (.cv x))) x (synCspfin) dv_cache_0013
      p0042_e00_recanon
  have p0043_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv w))
        (synWb (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))
          (synWrex x (synCspfin) (.classEq (.cv w) (synCtfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCspfin, synCint, synCtfin,
          synCif, synWo, synC0, synCdif, synCin, synCcompl, synCnin, synWnan,
          synCvv, synCio, synCuni, synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0042
  have p0043 :=
    @gElab (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWrex x (synCspfin) (.classEq (.cv w) (synCtfin (.cv x)))) a (.cv w)
      dv_cache_0014 dv_cache_0015 p0040 p0043_e01_recanon
  have p0044 := @gElsnc (.cv w) (synCncfin (synCvv)) p0040
  have p0045 :=
    @gOrbi12i
      (.classMem (.cv w)
        (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
      (synWrex x (synCspfin) (.classEq (.cv w) (synCtfin (.cv x))))
      (.classMem (.cv w) (synCsn (synCncfin (synCvv))))
      (.classEq (.cv w) (synCncfin (synCvv))) p0043 p0044
  have p0046 :=
    @gBitri
      (.classMem (.cv w)
        (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))))
      (synWo (.classMem (.cv w)
          (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
        (.classMem (.cv w) (synCsn (synCncfin (synCvv)))))
      (synWo (synWrex x (synCspfin) (.classEq (.cv w) (synCtfin (.cv x))))
        (.classEq (.cv w) (synCncfin (synCvv))))
      p0039 p0045
  have p0047 :=
    @gAnbi1i
      (.classMem (.cv w)
        (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))))
      (synWo (synWrex x (synCspfin) (.classEq (.cv w) (synCtfin (.cv x))))
        (.classEq (.cv w) (synCncfin (synCvv))))
      (synWsfin (.cv z) (.cv w)) p0046
  have p0048 := @gVex z
  have p0049 := @gEqeq1 (.cv a) (.cv z) (synCtfin (.cv x))
  have p0050_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a z) (synWb (.classEq (.cv a) (synCtfin (.cv x)))
          (.classEq (.cv z) (synCtfin (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCtfin synCif synWo synWa synC0 synCdif synCin synCcompl
          synCnin synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0049
  have p0050 :=
    @gRexbidv (.objEq a z) (.classEq (.cv a) (synCtfin (.cv x)))
      (.classEq (.cv z) (synCtfin (.cv x))) x (synCspfin) dv_cache_0016
      p0050_e00_recanon
  have p0051_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv z))
        (synWb (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))
          (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCspfin, synCint, synCtfin,
          synCif, synWo, synC0, synCdif, synCin, synCcompl, synCnin, synWnan,
          synCvv, synCio, synCuni, synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0050
  have p0051 :=
    @gElab (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x)))) a (.cv z)
      dv_cache_0017 dv_cache_0018 p0048 p0051_e01_recanon
  have p0052 :=
    @gN3imtr4g
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
      (synWa (synWo (synWrex x (synCspfin) (.classEq (.cv w) (synCtfin (.cv x))))
          (.classEq (.cv w) (synCncfin (synCvv)))) (synWsfin (.cv z) (.cv w)))
      (synWrex x (synCspfin) (.classEq (.cv z) (synCtfin (.cv x))))
      (synWa (.classMem (.cv w) (synCun
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCncfin (synCvv))))) (synWsfin (.cv z) (.cv w)))
      (.classMem (.cv z)
        (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
      p0038 p0047 p0051
  have p0053 :=
    @gSsun1 (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCsn (synCncfin (synCvv)))
  have p0054 :=
    @gSseli (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCsn (synCncfin (synCvv))))
      (.cv z) p0053
  have p0055 :=
    @gSyl6 (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
      (synWa (.classMem (.cv w) (synCun
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCncfin (synCvv))))) (synWsfin (.cv z) (.cv w)))
      (.classMem (.cv z)
        (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
      (.classMem (.cv z)
        (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))))
      p0052 p0054
  have p0056 :=
    @gAlrimiv (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv w) (synCspfin)))
      (.imp (synWa (.classMem (.cv w) (synCun
              (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCsn (synCncfin (synCvv))))) (synWsfin (.cv z) (.cv w))) (.classMem (.cv z)
          (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCncfin (synCvv))))))
      z dv_cache_0019 p0055
  have p0057 :=
    @gRalrimiva (.classMem (synCvv) (synCfin))
      (.all z (.imp (synWa (.classMem (.cv w) (synCun
                (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCsn (synCncfin (synCvv))))) (synWsfin (.cv z) (.cv w)))
          (.classMem (.cv z) (synCun
              (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
              (synCsn (synCncfin (synCvv)))))))
      w (synCspfin) dv_cache_0020 p0056
  have p0058 := @gVex a
  have p0059 :=
    @gElimak t
      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif (synCcompl
            (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                          (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                    (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                        (synCpw1 (synCpw1 (synC1c))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                    (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
          (synCxpk (synCsn (synCsn (synC0))) (synCvv))))
      (synCpw1 (synCspfin)) (.cv a) dv_cache_0021 dv_cache_0022 dv_cache_0023 p0058
  have p0060 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCspfin)) (.classMem (synCopk (.cv t) (.cv a))
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))))
  have p0061 := @gElpw1 x (.cv t) (synCspfin) dv_cache_0024 dv_cache_0001
  have p0062 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCspfin)))
      (synWrex x (synCspfin) (.classEq (.cv t) (synCsn (.cv x))))
      (.classMem (synCopk (.cv t) (.cv a))
        (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))
      p0061
  have p0063 :=
    @gR1941v (.classEq (.cv t) (synCsn (.cv x)))
      (.classMem (synCopk (.cv t) (.cv a))
        (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))
      x (synCspfin) dv_cache_0025
  have p0064 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCspfin))) (.classMem (synCopk (.cv t) (.cv a))
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
      (synWa (synWrex x (synCspfin) (.classEq (.cv t) (synCsn (.cv x))))
        (.classMem (synCopk (.cv t) (.cv a))
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
      (synWrex x (synCspfin) (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv a))
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))))
      p0062 p0063
  have p0065 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCspfin))) (.classMem (synCopk (.cv t) (.cv a))
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
      (synWrex x (synCspfin) (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv a))
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))))
      t p0064
  have p0066 :=
    @gRexcom4
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv t) (.cv a))
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
      x t (synCspfin) dv_cache_0026 dv_cache_0027
  have p0067 :=
    @gBitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCspfin)))
          (.classMem (synCopk (.cv t) (.cv a))
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))))
      (synWex t (synWrex x (synCspfin) (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv a))
              (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                (synCimak (synCsymdif (synCins2k
                                      (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                    (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                            (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))))
      (synWrex x (synCspfin) (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv a))
              (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                (synCimak (synCsymdif (synCins2k
                                      (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                    (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                            (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))))
      p0065 p0066
  have p0068 :=
    @gBitri
      (synWrex t (synCpw1 (synCspfin)) (.classMem (synCopk (.cv t) (.cv a))
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCspfin)))
          (.classMem (synCopk (.cv t) (.cv a))
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))))
      (synWrex x (synCspfin) (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv a))
              (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                (synCimak (synCsymdif (synCins2k
                                      (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                    (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                            (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))))
      p0060 p0067
  have p0069 :=
    @gBitri
      (.classMem (.cv a) (synCimak
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv)))) (synCpw1 (synCspfin))))
      (synWrex t (synCpw1 (synCspfin)) (.classMem (synCopk (.cv t) (.cv a))
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
      (synWrex x (synCspfin) (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv a))
              (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                (synCimak (synCsymdif (synCins2k
                                      (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                    (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                            (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))))
      p0059 p0068
  have p0070 := @gSnex (.cv x)
  have p0071 := @gOpkeq1 (.cv t) (synCsn (.cv x)) (.cv a)
  have p0072 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv x))) (synCopk (.cv t) (.cv a))
      (synCopk (synCsn (.cv x)) (.cv a))
      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif (synCcompl
            (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                          (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                    (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                        (synCpw1 (synCpw1 (synC1c))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                    (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
          (synCxpk (synCsn (synCsn (synC0))) (synCvv))))
      p0071
  have p0073 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (.cv a))
        (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))
      (.classMem (synCopk (synCsn (.cv x)) (.cv a))
        (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))
      t (synCsn (.cv x)) dv_cache_0028 dv_cache_0029 p0070 p0072
  have p0074 := @gVex x
  have p0075 := @gEqtfinrelk (.cv x) (.cv a) p0074 p0058
  have p0076 :=
    @gBitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv a))
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))))
      (.classMem (synCopk (synCsn (.cv x)) (.cv a))
        (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))
      (.classEq (.cv a) (synCtfin (.cv x))) p0073 p0075
  have p0077 :=
    @gRexbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv a))
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))))
      (.classEq (.cv a) (synCtfin (.cv x))) x (synCspfin) p0076
  have p0078 :=
    @gBitri
      (.classMem (.cv a) (synCimak
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv)))) (synCpw1 (synCspfin))))
      (synWrex x (synCspfin) (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv a))
              (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                (synCimak (synCsymdif (synCins2k
                                      (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                    (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                            (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))))
      (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))) p0069 p0077
  have p0079 :=
    @gEqabi (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))) a
      (synCimak (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))) (synCpw1 (synCspfin)))
      dv_cache_0030 p0078
  have p0080 := @gTfinrelkex
  have p0081 := @gSpfinex
  have p0082 := @gPw1ex (synCspfin) p0081
  have p0083 :=
    @gImakex
      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif (synCcompl
            (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                          (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                    (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                        (synCpw1 (synCpw1 (synC1c))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                    (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
          (synCxpk (synCsn (synCsn (synC0))) (synCvv))))
      (synCpw1 (synCspfin)) p0080 p0082
  have p0084 :=
    @gEqeltrri
      (synCimak (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))) (synCpw1 (synCspfin)))
      (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))) (synCvv)
      p0079 p0083
  have p0085 := @gSnex (synCncfin (synCvv))
  have p0086 :=
    @gUnex (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCsn (synCncfin (synCvv))) p0084 p0085
  have p0087 :=
    @gSsun2 (synCsn (synCncfin (synCvv)))
      (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
  have p0088 := @gNcfinex (synCvv)
  have p0089 := @gSnid (synCncfin (synCvv)) p0088
  have p0090 :=
    @gSselii (synCsn (synCncfin (synCvv)))
      (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCsn (synCncfin (synCvv))))
      (synCncfin (synCvv)) p0087 p0089
  have p0091 :=
    @gSpfininduct w z
      (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCsn (synCncfin (synCvv))))
      (synCvv) dv_cache_0031 dv_cache_0032 dv_cache_0033
  have p0092 :=
    @gMp3an12
      (.classMem
        (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))) (synCvv))
      (.classMem (synCncfin (synCvv))
        (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))))
      (synWral w (synCspfin) (.all z (.imp (synWa (.classMem (.cv w) (synCun (.cab a
                    (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
                  (synCsn (synCncfin (synCvv))))) (synWsfin (.cv z) (.cv w)))
            (.classMem (.cv z) (synCun
                (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCsn (synCncfin (synCvv))))))))
      (synWss (synCspfin)
        (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))))
      p0086 p0090 p0091
  have p0093 :=
    @gSyl (.classMem (synCvv) (synCfin))
      (synWral w (synCspfin) (.all z (.imp (synWa (.classMem (.cv w) (synCun (.cab a
                    (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
                  (synCsn (synCncfin (synCvv))))) (synWsfin (.cv z) (.cv w)))
            (.classMem (.cv z) (synCun
                (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCsn (synCncfin (synCvv))))))))
      (synWss (synCspfin)
        (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))))
      p0057 p0092
  exact p0093


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part025`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_vfinspclt`. -/
@[expose]
noncomputable def gVfinspclt (X : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem (synCvv) (synCfin)) (.classMem X (synCspfin)))
        (.classMem (synCtfin X) (synCspfin))) :=
  by
  let proofSupport : Finset Var := X.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (h)
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
  have dv_cache_0001 : x ∉ ((synCncfin (synCvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 :
    x ∉ ((Wff.classMem (synCtfin (synCncfin (synCvv))) (synCspfin))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Wff.classMem (synCtfin (.cv y)) (synCspfin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((Wff.classMem (synCtfin (.cv z)) (synCspfin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 :
    z ∉ ((synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv y) (synCspfin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Wff.classMem (synCvv) (synCfin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 :
    y ∉
      ((synCcnvk (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : y ∉ ((synCspfin)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0012 : y ∉ ((synCtfin (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0013 :
    x ∉
      ((synCuni1 (synCimak (synCcnvk
              (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                (synCimak (synCsymdif (synCins2k
                                      (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                    (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                            (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv))))) (synCspfin)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 :
    y ∉ ((Class.cab x (.classMem (synCtfin (.cv x)) (synCspfin)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0015 :
    z ∉ ((Class.cab x (.classMem (synCtfin (.cv x)) (synCspfin)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0016 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0017 : x ∉ (X).fv :=
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
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0018 : x ∉ ((Wff.classMem (synCtfin X) (synCspfin))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          fresh_x_not_X, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gTncveqnc1fin
  have p0001 := @gN1cspfin
  have p0002 :=
    @gEqeltrd (.classMem (synCvv) (synCfin)) (synCtfin (synCncfin (synCvv)))
      (synCncfin (synC1c)) (synCspfin) p0000 p0001
  have p0003 := @gNcfinex (synCvv)
  have p0004 := @gTfineq (.cv x) (synCncfin (synCvv))
  have p0005 :=
    @gEleq1d (.classEq (.cv x) (synCncfin (synCvv))) (synCtfin (.cv x))
      (synCtfin (synCncfin (synCvv))) (synCspfin) p0004
  have p0006 :=
    @gElab (.classMem (synCtfin (.cv x)) (synCspfin))
      (.classMem (synCtfin (synCncfin (synCvv))) (synCspfin)) x (synCncfin (synCvv))
      dv_cache_0001 dv_cache_0002 p0003 p0005
  have p0007 :=
    @gSylibr (.classMem (synCvv) (synCfin))
      (.classMem (synCtfin (synCncfin (synCvv))) (synCspfin))
      (.classMem (synCncfin (synCvv)) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
      p0002 p0006
  have p0008 :=
    @gSimprl (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv y) (synCspfin)))
      (.classMem (synCtfin (.cv y)) (synCspfin)) (synWsfin (.cv z) (.cv y))
  have p0009 := @gSfintfin (.cv z) (.cv y)
  have p0010 :=
    @gAd2antll (synWsfin (.cv z) (.cv y))
      (synWsfin (synCtfin (.cv z)) (synCtfin (.cv y)))
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv y) (synCspfin)))
      (.classMem (synCtfin (.cv y)) (synCspfin)) p0009
  have p0011 := @gSpfinsfincl (synCtfin (.cv y)) (synCtfin (.cv z))
  have p0012 :=
    @gSyl2anc
      (synWa (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv y) (synCspfin)))
        (synWa (.classMem (synCtfin (.cv y)) (synCspfin)) (synWsfin (.cv z) (.cv y))))
      (.classMem (synCtfin (.cv y)) (synCspfin))
      (synWsfin (synCtfin (.cv z)) (synCtfin (.cv y)))
      (.classMem (synCtfin (.cv z)) (synCspfin)) p0008 p0010 p0011
  have p0013 :=
    @gEx (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv y) (synCspfin)))
      (synWa (.classMem (synCtfin (.cv y)) (synCspfin)) (synWsfin (.cv z) (.cv y)))
      (.classMem (synCtfin (.cv z)) (synCspfin)) p0012
  have p0014 := @gVex y
  have p0015 := @gTfineq (.cv x) (.cv y)
  have p0016_e00_recanon :
    Nominal.NPrf (.imp (.objEq x y) (.classEq (synCtfin (.cv x)) (synCtfin (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCtfin synCif synWo synWa synC0 synCdif synCin synCcompl synCnin
          synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @gEleq1d (.objEq x y) (synCtfin (.cv x)) (synCtfin (.cv y)) (synCspfin)
      p0016_e00_recanon
  have p0017_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv y)) (synWb (.classMem (synCtfin (.cv x)) (synCspfin))
          (.classMem (synCtfin (.cv y)) (synCspfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCtfin synCif synWo synWa synC0 synCdif synCin synCcompl
          synCnin synWnan synCvv synCio synCuni synWex synCsn synCspfin synCint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @gElab (.classMem (synCtfin (.cv x)) (synCspfin))
      (.classMem (synCtfin (.cv y)) (synCspfin)) x (.cv y) dv_cache_0003 dv_cache_0004
      p0014 p0017_e01_recanon
  have p0018 :=
    @gAnbi1i (.classMem (.cv y) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
      (.classMem (synCtfin (.cv y)) (synCspfin)) (synWsfin (.cv z) (.cv y)) p0017
  have p0019 := @gVex z
  have p0020 := @gTfineq (.cv x) (.cv z)
  have p0021_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (synCtfin (.cv x)) (synCtfin (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCtfin synCif synWo synWa synC0 synCdif synCin synCcompl synCnin
          synWnan synCvv synCio synCuni synWex synCsn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0020
  have p0021 :=
    @gEleq1d (.objEq x z) (synCtfin (.cv x)) (synCtfin (.cv z)) (synCspfin)
      p0021_e00_recanon
  have p0022_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (synWb (.classMem (synCtfin (.cv x)) (synCspfin))
          (.classMem (synCtfin (.cv z)) (synCspfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCtfin synCif synWo synWa synC0 synCdif synCin synCcompl
          synCnin synWnan synCvv synCio synCuni synWex synCsn synCspfin synCint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0021
  have p0022 :=
    @gElab (.classMem (synCtfin (.cv x)) (synCspfin))
      (.classMem (synCtfin (.cv z)) (synCspfin)) x (.cv z) dv_cache_0005 dv_cache_0006
      p0019 p0022_e01_recanon
  have p0023 :=
    @gN3imtr4g
      (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv y) (synCspfin)))
      (synWa (.classMem (synCtfin (.cv y)) (synCspfin)) (synWsfin (.cv z) (.cv y)))
      (.classMem (synCtfin (.cv z)) (synCspfin))
      (synWa (.classMem (.cv y) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
        (synWsfin (.cv z) (.cv y)))
      (.classMem (.cv z) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin)))) p0013
      p0018 p0022
  have p0024 :=
    @gAlrimiv (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv y) (synCspfin)))
      (.imp (synWa (.classMem (.cv y) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
          (synWsfin (.cv z) (.cv y)))
        (.classMem (.cv z) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin)))))
      z dv_cache_0007 p0023
  have p0025 :=
    @gRalrimiva (.classMem (synCvv) (synCfin))
      (.all z (.imp (synWa
            (.classMem (.cv y) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
            (synWsfin (.cv z) (.cv y)))
          (.classMem (.cv z) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))))
      y (synCspfin) dv_cache_0008 p0024
  have p0026 := @gSnex (.cv x)
  have p0027 :=
    @gElimak y
      (synCcnvk (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))
      (synCspfin) (synCsn (.cv x)) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0026
  have p0028 :=
    @gOpkelcnvk (.cv y) (synCsn (.cv x))
      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif (synCcompl
            (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                          (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                    (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                        (synCpw1 (synCpw1 (synC1c))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                    (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
          (synCxpk (synCsn (synCsn (synC0))) (synCvv))))
      p0014 p0026
  have p0029 := @gVex x
  have p0030 := @gEqtfinrelk (.cv x) (.cv y) p0029 p0014
  have p0031 :=
    @gBitri
      (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcnvk
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
      (.classMem (synCopk (synCsn (.cv x)) (.cv y))
        (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))
      (.classEq (.cv y) (synCtfin (.cv x))) p0028 p0030
  have p0032 :=
    @gRexbii
      (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcnvk
          (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
      (.classEq (.cv y) (synCtfin (.cv x))) y (synCspfin) p0031
  have p0033 :=
    @gBitri
      (.classMem (synCsn (.cv x)) (synCimak (synCcnvk
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv))))) (synCspfin)))
      (synWrex y (synCspfin) (.classMem (synCopk (.cv y) (synCsn (.cv x))) (synCcnvk
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))))
      (synWrex y (synCspfin) (.classEq (.cv y) (synCtfin (.cv x)))) p0027 p0032
  have p0034 :=
    @gEluni1 (.cv x)
      (synCimak (synCcnvk (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
            (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))) (synCspfin))
      p0029
  have p0035 := @gRisset y (synCtfin (.cv x)) (synCspfin) dv_cache_0012 dv_cache_0010
  have p0036 :=
    @gN3bitr4i
      (.classMem (synCsn (.cv x)) (synCimak (synCcnvk
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv))))) (synCspfin)))
      (synWrex y (synCspfin) (.classEq (.cv y) (synCtfin (.cv x))))
      (.classMem (.cv x) (synCuni1 (synCimak (synCcnvk
              (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                (synCimak (synCsymdif (synCins2k
                                      (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                    (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                            (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv))))) (synCspfin))))
      (.classMem (synCtfin (.cv x)) (synCspfin)) p0033 p0034 p0035
  have p0037 :=
    @gEqabi (.classMem (synCtfin (.cv x)) (synCspfin)) x
      (synCuni1 (synCimak (synCcnvk
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv))))) (synCspfin)))
      dv_cache_0013 p0036
  have p0038 := @gTfinrelkex
  have p0039 :=
    @gCnvkex
      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif (synCcompl
            (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                          (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                    (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                        (synCpw1 (synCpw1 (synC1c))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                    (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
          (synCxpk (synCsn (synCsn (synC0))) (synCvv))))
      p0038
  have p0040 := @gSpfinex
  have p0041 :=
    @gImakex
      (synCcnvk (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
                      (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
                            (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
                                  (synCimak (synCin (synCins2k (synCsik (synCssetk)))
                                      (synCins3k (synCimak (synCin (synCins3k (synCsik
        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                      (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))
      (synCspfin) p0039 p0040
  have p0042 :=
    @gUni1ex
      (synCimak (synCcnvk (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
            (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                      (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                            (synCimak (synCsymdif (synCins2k
                                  (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                      (synCin (synCins2k (synCsik (synCssetk))) (synCins3k
        (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c))
        (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
              (synCxpk (synCsn (synCsn (synC0))) (synCvv))))) (synCspfin))
      p0041
  have p0043 :=
    @gEqeltrri
      (synCuni1 (synCimak (synCcnvk
            (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                              (synCimak (synCsymdif (synCins2k
                                    (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
                                        (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                          (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                (synCxpk (synCsn (synCsn (synC0))) (synCvv))))) (synCspfin)))
      (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))) (synCvv) p0037 p0042
  have p0044 :=
    @gSpfininduct y z (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))) (synCvv)
      dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0045 :=
    @gMp3an1 (.classMem (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))) (synCvv))
      (.classMem (synCncfin (synCvv)) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
      (synWral y (synCspfin) (.all z (.imp (synWa
              (.classMem (.cv y) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
              (synWsfin (.cv z) (.cv y)))
            (.classMem (.cv z) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin)))))))
      (synWss (synCspfin) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin)))) p0043
      p0044
  have p0046 :=
    @gSyl2anc (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCvv)) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
      (synWral y (synCspfin) (.all z (.imp (synWa
              (.classMem (.cv y) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
              (synWsfin (.cv z) (.cv y)))
            (.classMem (.cv z) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin)))))))
      (synWss (synCspfin) (.cab x (.classMem (synCtfin (.cv x)) (synCspfin)))) p0007
      p0025 p0045
  have p0047 :=
    @gSselda (.classMem (synCvv) (synCfin)) (synCspfin)
      (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))) X p0046
  have p0048 := @gTfineq (.cv x) X
  have p0049 :=
    @gEleq1d (.classEq (.cv x) X) (synCtfin (.cv x)) (synCtfin X) (synCspfin) p0048
  have p0050 :=
    @gElabg (.classMem (synCtfin (.cv x)) (synCspfin))
      (.classMem (synCtfin X) (synCspfin)) x X (synCspfin) dv_cache_0017 dv_cache_0018
      p0049
  have p0051 :=
    @gAdantl (.classMem X (synCspfin))
      (synWb (.classMem X (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
        (.classMem (synCtfin X) (synCspfin)))
      (.classMem (synCvv) (synCfin)) p0050
  have p0052 :=
    @gMpbid (synWa (.classMem (synCvv) (synCfin)) (.classMem X (synCspfin)))
      (.classMem X (.cab x (.classMem (synCtfin (.cv x)) (synCspfin))))
      (.classMem (synCtfin X) (synCspfin)) p0047 p0051
  exact p0052

/-- Checked nominal proof certificate identified upstream as `g_vfinspeqtncv`. -/
@[expose]
noncomputable def gVfinspeqtncv (x : Var) (a : Var) (dv_a_x : a ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (synCvv) (synCfin)) (.classEq (synCspfin) (synCun
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCncfin (synCvv)))))) :=
  by
  have dv_cache_0001 : a ≠ x := by exact (show a ≠ x from (by exact dv_a_x))
  have dv_cache_0002 : x ∉ ((Wff.classMem (.cv a) (synCspfin))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_a_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : x ∉ ((Wff.classMem (synCvv) (synCfin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : a ∉ ((synCspfin)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0005 : a ∉ ((Wff.classMem (synCvv) (synCfin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cfin, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gVfinspss x a dv_cache_0001
  have p0001 := @gVfinspclt (.cv x)
  have p0002 := @gEleq1 (.cv a) (synCtfin (.cv x)) (synCspfin)
  have p0003 :=
    @gBiimprd (.classEq (.cv a) (synCtfin (.cv x))) (.classMem (.cv a) (synCspfin))
      (.classMem (synCtfin (.cv x)) (synCspfin)) p0002
  have p0004 :=
    @gCom12 (.classEq (.cv a) (synCtfin (.cv x)))
      (.classMem (synCtfin (.cv x)) (synCspfin)) (.classMem (.cv a) (synCspfin)) p0003
  have p0005 :=
    @gSyl (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv x) (synCspfin)))
      (.classMem (synCtfin (.cv x)) (synCspfin))
      (.imp (.classEq (.cv a) (synCtfin (.cv x))) (.classMem (.cv a) (synCspfin))) p0001
      p0004
  have p0006 :=
    @gRexlimdva (.classMem (synCvv) (synCfin)) (.classEq (.cv a) (synCtfin (.cv x)))
      (.classMem (.cv a) (synCspfin)) x (synCspfin) dv_cache_0002 dv_cache_0003 p0005
  have p0007 :=
    @gAbssdv (.classMem (synCvv) (synCfin))
      (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))) a (synCspfin)
      dv_cache_0004 dv_cache_0005 p0006
  have p0008 := @gNcvspfin
  have p0009 := @gNcfinex (synCvv)
  have p0010 := @gSnss (synCncfin (synCvv)) (synCspfin) p0009
  have p0011 :=
    @gMpbi (.classMem (synCncfin (synCvv)) (synCspfin))
      (synWss (synCsn (synCncfin (synCvv))) (synCspfin)) p0008 p0010
  have p0012 :=
    @gJctir (.classMem (synCvv) (synCfin))
      (synWss (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCspfin))
      (synWss (synCsn (synCncfin (synCvv))) (synCspfin)) p0007 p0011
  have p0013 :=
    @gUnss (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCsn (synCncfin (synCvv))) (synCspfin)
  have p0014 :=
    @gSylib (.classMem (synCvv) (synCfin))
      (synWa (synWss (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCspfin)) (synWss (synCsn (synCncfin (synCvv))) (synCspfin)))
      (synWss
        (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))) (synCspfin))
      p0012 p0013
  have p0015 :=
    @gEqssd (.classMem (synCvv) (synCfin)) (synCspfin)
      (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCsn (synCncfin (synCvv))))
      p0000 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end
