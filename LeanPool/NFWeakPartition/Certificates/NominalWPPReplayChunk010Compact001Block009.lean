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

@[expose]
noncomputable def g_vfinspsslem1 (x : Var) (z : Var) (n : Var) (_dv_n_x : n ≠ x)
    (_dv_n_z : n ≠ z) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
          (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
        (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))) :=
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
  have dv_cache_0002 : a ∉ ((syn_ctfin (.cv n))).fv :=
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
  have dv_cache_0004 : p ∉ ((syn_ctfin (syn_cncfin (syn_c1c)))).fv :=
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
  have dv_cache_0005 : a ∉ ((syn_cpw1 (syn_cpw1 (syn_cvv)))).fv :=
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
  have dv_cache_0006 : b ∉ ((syn_cpw1 (syn_cpw1 (syn_cvv)))).fv :=
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
  have dv_cache_0012 : g ∉ ((syn_cpw1 (syn_cvv))).fv :=
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
  have dv_cache_0014 : d ∉ ((syn_cvv)).fv :=
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
  have dv_cache_0015 : d ∉ ((Wff.classEq (.cv a) (syn_cpw1 (.cv g)))).fv :=
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
  have dv_cache_0016 : g ∉ ((syn_cpw1 (.cv d))).fv :=
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
  have dv_cache_0017 : g ∉ ((Wff.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d))))).fv :=
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
      ((syn_wa (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d))))
          (.classMem (syn_cpw (.cv d)) (syn_cncfin (syn_cpw (.cv d)))))).fv :=
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
  have dv_cache_0020 : a ∉ ((syn_cncfin (syn_cpw1 (.cv d)))).fv :=
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
  have dv_cache_0021 : a ∉ ((syn_cncfin (syn_cpw (.cv d)))).fv :=
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
  have dv_cache_0022 : x ∉ ((syn_cncfin (syn_cpw1 (.cv d)))).fv :=
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
  have dv_cache_0023 : x ∉ ((syn_cspfin)).fv :=
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
    x ∉ ((Wff.classEq (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))).fv :=
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
    d ∉ ((syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))).fv :=
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
      ((syn_wa (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
              (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
            (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
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
    a ∉ ((syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))).fv :=
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
    b ∉ ((syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
          (syn_wa (.classMem (.cv n) (syn_cspfin))
            (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
          (syn_wa (.classMem (.cv n) (syn_cspfin))
            (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))).fv :=
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
    p ∉ ((syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
          (syn_wa (.classMem (.cv n) (syn_cspfin))
            (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))).fv :=
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
  have p0000 := @g_simpl (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv n) (syn_cspfin))
  have p0001 := @g_vfinspnn
  have p0002 := @g_difss (syn_cnnc) (syn_csn (syn_c0))
  have p0003 :=
    @g_syl6ss (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin)
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cnnc) p0001 p0002
  have p0004 :=
    @g_sselda (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin) (syn_cnnc) (.cv n) p0003
  have p0006 :=
    @g_sselda (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin)
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (.cv n) p0001
  have p0007 := @g_eldifsn (.cv n) (syn_cnnc) (syn_c0)
  have p0008 :=
    @g_simprbi (.classMem (.cv n) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
      (.classMem (.cv n) (syn_cnnc)) (syn_wne (.cv n) (syn_c0)) p0007
  have p0009 :=
    @g_syl (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv n) (syn_cspfin)))
      (.classMem (.cv n) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
      (syn_wne (.cv n) (syn_c0)) p0006 p0008
  have p0010 := @g_vfintle (.cv n)
  have p0011 :=
    @g_syl3anc (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv n) (syn_cspfin)))
      (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv n) (syn_cnnc))
      (syn_wne (.cv n) (syn_c0))
      (.classMem (syn_copk (syn_ctfin (.cv n)) (syn_cncfin (syn_c1c))) (syn_clefin)) p0000
      p0004 p0009 p0010
  have p0012 :=
    @g_ad2ant2r (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv n) (syn_cspfin))
      (.classMem (syn_copk (syn_ctfin (.cv n)) (syn_cncfin (syn_c1c))) (syn_clefin))
      (.classMem (syn_ctfin (.cv n)) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))
      p0011
  have p0013 := @g_t1csfin1c
  have p0014 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cncfin (syn_c1c)))
      (.classMem (syn_ctfin (.cv n)) (syn_cspfin)) p0013
  have p0015 :=
    @g_simpr (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))
  have p0016 :=
    @g_sfinltfin (.cv z) (syn_ctfin (.cv n)) (syn_ctfin (syn_cncfin (syn_c1c)))
      (syn_cncfin (syn_c1c))
  have p0017 :=
    @g_ex
      (syn_wa (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cncfin (syn_c1c)))
        (syn_wsfin (.cv z) (syn_ctfin (.cv n))))
      (.classMem (syn_copk (syn_ctfin (syn_cncfin (syn_c1c))) (.cv z)) (syn_cltfin))
      (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_ctfin (.cv n))) (syn_cltfin)) p0016
  have p0018 :=
    @g_syl2an
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cncfin (syn_c1c)))
      (syn_wsfin (.cv z) (syn_ctfin (.cv n)))
      (.imp (.classMem (syn_copk (syn_ctfin (syn_cncfin (syn_c1c))) (.cv z)) (syn_cltfin))
        (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_ctfin (.cv n))) (syn_cltfin)))
      (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n))))
      p0014 p0015 p0017
  have p0019 :=
    @g_con3d
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_copk (syn_ctfin (syn_cncfin (syn_c1c))) (.cv z)) (syn_cltfin))
      (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_ctfin (.cv n))) (syn_cltfin)) p0018
  have p0020 :=
    @g_ad2ant2r (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv n) (syn_cspfin))
      (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin))
      (syn_wsfin (.cv z) (syn_ctfin (.cv n))) p0004
  have p0021 := @g_tfincl (.cv n)
  have p0022 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctfin (.cv n)) (syn_cnnc)) p0020
      p0021
  have p0023 := @g_n_1cex
  have p0024 := @g_ncfinprop (syn_c1c) (syn_cvv)
  have p0025 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
        (.classMem (syn_c1c) (syn_cncfin (syn_c1c))))
      p0023 p0024
  have p0026 :=
    @g_ad2antrr (.classMem (syn_cvv) (syn_cfin))
      (syn_wa (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
        (.classMem (syn_c1c) (syn_cncfin (syn_c1c))))
      (.classMem (syn_ctfin (.cv n)) (syn_cspfin))
      (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n))))
      p0025
  have p0027 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
      (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0026
  have p0028 := @g_lenltfin (syn_ctfin (.cv n)) (syn_cncfin (syn_c1c))
  have p0029 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_ctfin (.cv n)) (syn_cnnc))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
      (syn_wb (.classMem (syn_copk (syn_ctfin (.cv n)) (syn_cncfin (syn_c1c))) (syn_clefin))
        (.neg (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_ctfin (.cv n))) (syn_cltfin))))
      p0022 p0027 p0028
  have p0030 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin (.cv z)
      (syn_ctfin (.cv n)) a dv_cache_0001 dv_cache_0002
  have p0031 :=
    @g_simp1bi (syn_wsfin (.cv z) (syn_ctfin (.cv n))) (.classMem (.cv z) (syn_cnnc))
      (.classMem (syn_ctfin (.cv n)) (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (.cv z))
          (.classMem (syn_cpw (.cv a)) (syn_ctfin (.cv n)))))
      p0030
  have p0032 :=
    @g_ad2antll (syn_wsfin (.cv z) (syn_ctfin (.cv n))) (.classMem (.cv z) (syn_cnnc))
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
      (.classMem (.cv n) (syn_cspfin)) p0031
  have p0033 := @g_tfincl (syn_cncfin (syn_c1c))
  have p0034 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
      (.classMem (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cnnc)) p0027 p0033
  have p0035 := @g_lenltfin (.cv z) (syn_ctfin (syn_cncfin (syn_c1c)))
  have p0036 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (.cv z) (syn_cnnc))
      (.classMem (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cnnc))
      (syn_wb (.classMem (syn_copk (.cv z) (syn_ctfin (syn_cncfin (syn_c1c)))) (syn_clefin))
        (.neg (.classMem (syn_copk (syn_ctfin (syn_cncfin (syn_c1c))) (.cv z)) (syn_cltfin))))
      p0032 p0034 p0035
  have p0037 :=
    @g_n_3imtr4d
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.neg (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_ctfin (.cv n))) (syn_cltfin)))
      (.neg (.classMem (syn_copk (syn_ctfin (syn_cncfin (syn_c1c))) (.cv z)) (syn_cltfin)))
      (.classMem (syn_copk (syn_ctfin (.cv n)) (syn_cncfin (syn_c1c))) (syn_clefin))
      (.classMem (syn_copk (.cv z) (syn_ctfin (syn_cncfin (syn_c1c)))) (syn_clefin)) p0019
      p0029 p0036
  have p0038 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_copk (syn_ctfin (.cv n)) (syn_cncfin (syn_c1c))) (syn_clefin))
      (.classMem (syn_copk (.cv z) (syn_ctfin (syn_cncfin (syn_c1c)))) (syn_clefin)) p0012
      p0037
  have p0039 := @g_vex z
  have p0040 := @g_tfinex (syn_cncfin (syn_c1c))
  have p0041 :=
    @g_opklefing p (.cv z) (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cvv) (syn_cvv)
      dv_cache_0003 dv_cache_0004
  have p0042 :=
    @g_mp2an (.classMem (.cv z) (syn_cvv))
      (.classMem (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv z) (syn_ctfin (syn_cncfin (syn_c1c)))) (syn_clefin))
        (syn_wrex p (syn_cnnc)
          (.classEq (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cplc (.cv z) (.cv p)))))
      p0039 p0040 p0041
  have p0043 :=
    @g_sylib
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_copk (.cv z) (syn_ctfin (syn_cncfin (syn_c1c)))) (syn_clefin))
      (syn_wrex p (syn_cnnc)
        (.classEq (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cplc (.cv z) (.cv p))))
      p0038 p0042
  have p0044 := @g_df1c2
  have p0045 := @g_pw1eq (syn_c1c) (syn_cpw1 (syn_cvv))
  have p0046 := Nominal.mp p0044 p0045
  have p0047 := @g_tfinpw1 (syn_c1c) (syn_cncfin (syn_c1c))
  have p0048 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (syn_wa (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
        (.classMem (syn_c1c) (syn_cncfin (syn_c1c))))
      (.classMem (syn_cpw1 (syn_c1c)) (syn_ctfin (syn_cncfin (syn_c1c)))) p0026 p0047
  have p0049 :=
    @g_syl5eqelr
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cpw1 (syn_c1c))
      (syn_ctfin (syn_cncfin (syn_c1c))) p0046 p0048
  have p0050 :=
    @g_eleq2 (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cplc (.cv z) (.cv p))
      (syn_cpw1 (syn_cpw1 (syn_cvv)))
  have p0051 :=
    @g_syl5ibcom
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_ctfin (syn_cncfin (syn_c1c))))
      (.classEq (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cplc (.cv z) (.cv p)))
      (.classMem (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cplc (.cv z) (.cv p))) p0049 p0050
  have p0052 :=
    @g_eladdc (syn_cpw1 (syn_cpw1 (syn_cvv))) (.cv z) (.cv p) a b dv_cache_0005
      dv_cache_0006 dv_cache_0001 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0053 := @g_ssun1 (.cv a) (.cv b)
  have p0054 := @g_sseq2 (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cun (.cv a) (.cv b)) (.cv a)
  have p0055 :=
    @g_mpbiri (.classEq (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cun (.cv a) (.cv b)))
      (syn_wss (.cv a) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wss (.cv a) (syn_cun (.cv a) (.cv b))) p0053 p0054
  have p0056 := @g_vex a
  have p0057 := @g_sspw1 g (.cv a) (syn_cpw1 (syn_cvv)) dv_cache_0011 dv_cache_0012 p0056
  have p0058 := @g_vex g
  have p0059 := @g_sspw1 d (.cv g) (syn_cvv) dv_cache_0013 dv_cache_0014 p0058
  have p0060 := @g_ssv (.cv d)
  have p0061 :=
    @g_biantrur (syn_wss (.cv d) (syn_cvv)) (.classEq (.cv g) (syn_cpw1 (.cv d))) p0060
  have p0062 :=
    @g_exbii (.classEq (.cv g) (syn_cpw1 (.cv d)))
      (syn_wa (syn_wss (.cv d) (syn_cvv)) (.classEq (.cv g) (syn_cpw1 (.cv d)))) d p0061
  have p0063 :=
    @g_bitr4i (syn_wss (.cv g) (syn_cpw1 (syn_cvv)))
      (syn_wex d (syn_wa (syn_wss (.cv d) (syn_cvv)) (.classEq (.cv g) (syn_cpw1 (.cv d)))))
      (syn_wex d (.classEq (.cv g) (syn_cpw1 (.cv d)))) p0059 p0062
  have p0064 :=
    @g_anbi1i (syn_wss (.cv g) (syn_cpw1 (syn_cvv)))
      (syn_wex d (.classEq (.cv g) (syn_cpw1 (.cv d))))
      (.classEq (.cv a) (syn_cpw1 (.cv g))) p0063
  have p0065 :=
    @g_n_19_41v (.classEq (.cv g) (syn_cpw1 (.cv d)))
      (.classEq (.cv a) (syn_cpw1 (.cv g))) d dv_cache_0015
  have p0066 :=
    @g_bitr4i
      (syn_wa (syn_wss (.cv g) (syn_cpw1 (syn_cvv))) (.classEq (.cv a) (syn_cpw1 (.cv g))))
      (syn_wa (syn_wex d (.classEq (.cv g) (syn_cpw1 (.cv d))))
        (.classEq (.cv a) (syn_cpw1 (.cv g))))
      (syn_wex d (syn_wa (.classEq (.cv g) (syn_cpw1 (.cv d)))
          (.classEq (.cv a) (syn_cpw1 (.cv g)))))
      p0064 p0065
  have p0067 :=
    @g_exbii
      (syn_wa (syn_wss (.cv g) (syn_cpw1 (syn_cvv))) (.classEq (.cv a) (syn_cpw1 (.cv g))))
      (syn_wex d (syn_wa (.classEq (.cv g) (syn_cpw1 (.cv d)))
          (.classEq (.cv a) (syn_cpw1 (.cv g)))))
      g p0066
  have p0068 :=
    @g_excom
      (syn_wa (.classEq (.cv g) (syn_cpw1 (.cv d))) (.classEq (.cv a) (syn_cpw1 (.cv g))))
      g d
  have p0069 := @g_vex d
  have p0070 := @g_pw1ex (.cv d) p0069
  have p0071 := @g_pw1eq (.cv g) (syn_cpw1 (.cv d))
  have p0072 :=
    @g_eqeq2d (.classEq (.cv g) (syn_cpw1 (.cv d))) (syn_cpw1 (.cv g))
      (syn_cpw1 (syn_cpw1 (.cv d))) (.cv a) p0071
  have p0073 :=
    @g_ceqsexv (.classEq (.cv a) (syn_cpw1 (.cv g)))
      (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d)))) g (syn_cpw1 (.cv d)) dv_cache_0016
      dv_cache_0017 p0070 p0072
  have p0074 :=
    @g_exbii
      (syn_wex g (syn_wa (.classEq (.cv g) (syn_cpw1 (.cv d)))
          (.classEq (.cv a) (syn_cpw1 (.cv g)))))
      (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d)))) d p0073
  have p0075 :=
    @g_bitri
      (syn_wex g (syn_wex d (syn_wa (.classEq (.cv g) (syn_cpw1 (.cv d)))
            (.classEq (.cv a) (syn_cpw1 (.cv g))))))
      (syn_wex d (syn_wex g (syn_wa (.classEq (.cv g) (syn_cpw1 (.cv d)))
            (.classEq (.cv a) (syn_cpw1 (.cv g))))))
      (syn_wex d (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d))))) p0068 p0074
  have p0076 :=
    @g_n_3bitri (syn_wss (.cv a) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wex g (syn_wa (syn_wss (.cv g) (syn_cpw1 (syn_cvv)))
          (.classEq (.cv a) (syn_cpw1 (.cv g)))))
      (syn_wex g (syn_wex d (syn_wa (.classEq (.cv g) (syn_cpw1 (.cv d)))
            (.classEq (.cv a) (syn_cpw1 (.cv g))))))
      (syn_wex d (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d))))) p0057 p0067 p0075
  have p0077 :=
    @g_sylib (.classEq (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cun (.cv a) (.cv b)))
      (syn_wss (.cv a) (syn_cpw1 (syn_cpw1 (syn_cvv))))
      (syn_wex d (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d))))) p0055 p0076
  have p0078 := @g_eleq1 (.cv a) (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z)
  have p0079_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d))))
        (syn_wb (.objMem a z) (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss
          syn_c1c syn_wex syn_csn syn_wb
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
    @g_biimpac (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d)))) (.objMem a z)
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z)) p0079_e00_recanon
  have p0080 :=
    @g_adantr
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (.cv z) (syn_cnnc)) (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z))
      p0032
  have p0081 := @g_ncfinprop (syn_cpw1 (.cv d)) (syn_cvv)
  have p0082 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cpw1 (.cv d)) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cnnc))
        (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d)))))
      p0070 p0081
  have p0083 :=
    @g_ad2antrr (.classMem (syn_cvv) (syn_cfin))
      (syn_wa (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cnnc))
        (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d)))))
      (.classMem (syn_ctfin (.cv n)) (syn_cspfin))
      (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n))))
      p0082
  have p0084 :=
    @g_simpld
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cnnc))
      (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d)))) p0083
  have p0085 := @g_tfincl (syn_cncfin (syn_cpw1 (.cv d)))
  have p0086 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cnnc))
      (.classMem (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_cnnc)) p0084 p0085
  have p0087 :=
    @g_adantr
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_cnnc))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z)) p0086
  have p0088 :=
    @g_simpr
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z))
  have p0089 := @g_tfinpw1 (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d)))
  have p0090 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (syn_wa (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cnnc))
        (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d)))))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))
      p0083 p0089
  have p0091 :=
    @g_adantr
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z)) p0090
  have p0092 :=
    @g_nnceleq (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z)
      (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d))))
  have p0093 :=
    @g_syl22anc
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
          (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
        (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z)))
      (.classMem (.cv z) (syn_cnnc))
      (.classMem (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_cnnc))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))
      (.classEq (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d))))) p0080 p0087 p0088
      p0091 p0092
  have p0094 :=
    @g_ex
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z))
      (.classEq (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d))))) p0093
  have p0095 :=
    @g_ad2ant2r (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv n) (syn_cspfin))
      (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n))) p0004
  have p0096 := @g_pwex (.cv d) p0069
  have p0097 := @g_ncfinprop (syn_cpw (.cv d)) (syn_cvv)
  have p0098 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cpw (.cv d)) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_cpw (.cv d))) (syn_cnnc))
        (.classMem (syn_cpw (.cv d)) (syn_cncfin (syn_cpw (.cv d)))))
      p0096 p0097
  have p0099 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cpw (.cv d))) (syn_cnnc))
      (.classMem (syn_cpw (.cv d)) (syn_cncfin (syn_cpw (.cv d)))) p0098
  have p0100 :=
    @g_ad2antrr (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cpw (.cv d))) (syn_cnnc))
      (.classMem (syn_ctfin (.cv n)) (syn_cspfin))
      (syn_wa (.classMem (.cv n) (syn_cspfin))
        (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n))))
      p0099
  have p0101 :=
    @g_simprr
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
      (.classMem (.cv n) (syn_cspfin))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))
  have p0102 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cnnc))
      (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d)))) p0082
  have p0103 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cnnc))
      (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d)))) p0082
  have p0104 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cpw (.cv d))) (syn_cnnc))
      (.classMem (syn_cpw (.cv d)) (syn_cncfin (syn_cpw (.cv d)))) p0098
  have p0105 := @g_pw1eq (.cv a) (.cv d)
  have p0106_e00_recanon :
    Nominal.NPrf (.imp (.objEq a d) (.classEq (syn_cpw1 (.cv a)) (syn_cpw1 (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cpw syn_wss
          syn_c1c syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0105
  have p0106 :=
    @g_eleq1d (.objEq a d) (syn_cpw1 (.cv a)) (syn_cpw1 (.cv d))
      (syn_cncfin (syn_cpw1 (.cv d))) p0106_e00_recanon
  have p0107 := @g_pweq (.cv a) (.cv d)
  have p0108_e00_recanon :
    Nominal.NPrf (.imp (.objEq a d) (.classEq (syn_cpw (.cv a)) (syn_cpw (.cv d)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0107
  have p0108 :=
    @g_eleq1d (.objEq a d) (syn_cpw (.cv a)) (syn_cpw (.cv d))
      (syn_cncfin (syn_cpw (.cv d))) p0108_e00_recanon
  have p0109 :=
    @g_anbi12d (.objEq a d) (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_cpw1 (.cv d))))
      (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d))))
      (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cpw (.cv d))))
      (.classMem (syn_cpw (.cv d)) (syn_cncfin (syn_cpw (.cv d)))) p0106 p0108
  have p0110_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv d)) (syn_wb
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_cpw1 (.cv d))))
            (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cpw (.cv d)))))
          (syn_wa (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d))))
            (.classMem (syn_cpw (.cv d)) (syn_cncfin (syn_cpw (.cv d))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wa syn_cpw1 syn_cin syn_ccompl syn_cnin syn_wnan syn_cpw syn_wss
          syn_c1c syn_wex syn_csn syn_cncfin syn_cio syn_cuni
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
    @g_spcev
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_cpw1 (.cv d))))
        (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cpw (.cv d)))))
      (syn_wa (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d))))
        (.classMem (syn_cpw (.cv d)) (syn_cncfin (syn_cpw (.cv d)))))
      a (.cv d) dv_cache_0018 dv_cache_0019 p0069 p0110_e01_recanon
  have p0111 :=
    @g_syl2anc (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cpw1 (.cv d)) (syn_cncfin (syn_cpw1 (.cv d))))
      (.classMem (syn_cpw (.cv d)) (syn_cncfin (syn_cpw (.cv d))))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_cpw1 (.cv d))))
          (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cpw (.cv d))))))
      p0103 p0104 p0110
  have p0112 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin
      (syn_cncfin (syn_cpw1 (.cv d))) (syn_cncfin (syn_cpw (.cv d))) a dv_cache_0020
      dv_cache_0021
  have p0113 :=
    @g_syl3anbrc (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cnnc))
      (.classMem (syn_cncfin (syn_cpw (.cv d))) (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_cpw1 (.cv d))))
          (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cpw (.cv d))))))
      (syn_wsfin (syn_cncfin (syn_cpw1 (.cv d))) (syn_cncfin (syn_cpw (.cv d)))) p0102
      p0099 p0111 p0112
  have p0114 :=
    @g_ad2antrr (.classMem (syn_cvv) (syn_cfin))
      (syn_wsfin (syn_cncfin (syn_cpw1 (.cv d))) (syn_cncfin (syn_cpw (.cv d))))
      (.classMem (syn_ctfin (.cv n)) (syn_cspfin))
      (syn_wa (.classMem (.cv n) (syn_cspfin))
        (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n))))
      p0113
  have p0115 := @g_sfintfin (syn_cncfin (syn_cpw1 (.cv d))) (syn_cncfin (syn_cpw (.cv d)))
  have p0116 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (syn_wa (.classMem (.cv n) (syn_cspfin))
          (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))))
      (syn_wsfin (syn_cncfin (syn_cpw1 (.cv d))) (syn_cncfin (syn_cpw (.cv d))))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d))))
        (syn_ctfin (syn_cncfin (syn_cpw (.cv d)))))
      p0114 p0115
  have p0117 :=
    @g_sfin112 (syn_ctfin (syn_cncfin (syn_cpw (.cv d))))
      (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n))
  have p0118 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (syn_wa (.classMem (.cv n) (syn_cspfin))
          (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d))))
        (syn_ctfin (syn_cncfin (syn_cpw (.cv d)))))
      (.classEq (syn_ctfin (.cv n)) (syn_ctfin (syn_cncfin (syn_cpw (.cv d))))) p0101
      p0116 p0117
  have p0119 := @g_tfin11 (.cv n) (syn_cncfin (syn_cpw (.cv d)))
  have p0120 :=
    @g_syl3anc
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (syn_wa (.classMem (.cv n) (syn_cspfin))
          (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))))
      (.classMem (.cv n) (syn_cnnc)) (.classMem (syn_cncfin (syn_cpw (.cv d))) (syn_cnnc))
      (.classEq (syn_ctfin (.cv n)) (syn_ctfin (syn_cncfin (syn_cpw (.cv d)))))
      (.classEq (.cv n) (syn_cncfin (syn_cpw (.cv d)))) p0095 p0100 p0118 p0119
  have p0121 :=
    @g_simprl
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
      (.classMem (.cv n) (syn_cspfin))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))
  have p0122 :=
    @g_eqeltrrd
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (syn_wa (.classMem (.cv n) (syn_cspfin))
          (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))))
      (.cv n) (syn_cncfin (syn_cpw (.cv d))) (syn_cspfin) p0120 p0121
  have p0123 :=
    @g_spfinsfincl (syn_cncfin (syn_cpw (.cv d))) (syn_cncfin (syn_cpw1 (.cv d)))
  have p0124 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (syn_wa (.classMem (.cv n) (syn_cspfin))
          (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))))
      (.classMem (syn_cncfin (syn_cpw (.cv d))) (syn_cspfin))
      (syn_wsfin (syn_cncfin (syn_cpw1 (.cv d))) (syn_cncfin (syn_cpw (.cv d))))
      (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cspfin)) p0122 p0114 p0123
  have p0125 :=
    @g_risset x (syn_cncfin (syn_cpw1 (.cv d))) (syn_cspfin) dv_cache_0022 dv_cache_0023
  have p0126 := @g_tfineq (.cv x) (syn_cncfin (syn_cpw1 (.cv d)))
  have p0127 :=
    @g_eqcomd (.classEq (.cv x) (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv x))
      (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) p0126
  have p0128 :=
    @g_reximi (.classEq (.cv x) (syn_cncfin (syn_cpw1 (.cv d))))
      (.classEq (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv x))) x
      (syn_cspfin) p0127
  have p0129 :=
    @g_sylbi (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cspfin))
      (syn_wrex x (syn_cspfin) (.classEq (.cv x) (syn_cncfin (syn_cpw1 (.cv d)))))
      (syn_wrex x (syn_cspfin)
        (.classEq (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv x))))
      p0125 p0128
  have p0130 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (syn_wa (.classMem (.cv n) (syn_cspfin))
          (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))))
      (.classMem (syn_cncfin (syn_cpw1 (.cv d))) (syn_cspfin))
      (syn_wrex x (syn_cspfin)
        (.classEq (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv x))))
      p0124 p0129
  have p0131 :=
    @g_sfineq1 (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n))
  have p0132 :=
    @g_anbi2d (.classEq (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))
      (syn_wsfin (.cv z) (syn_ctfin (.cv n)))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))
      (.classMem (.cv n) (syn_cspfin)) p0131
  have p0133 :=
    @g_anbi2d (.classEq (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))
      (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n))))
      (syn_wa (.classMem (.cv n) (syn_cspfin))
        (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n))))
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
      p0132
  have p0134 :=
    @g_eqeq1 (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv x))
  have p0135 :=
    @g_rexbidv (.classEq (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))
      (.classEq (.cv z) (syn_ctfin (.cv x)))
      (.classEq (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv x))) x
      (syn_cspfin) dv_cache_0024 p0134
  have p0136 :=
    @g_imbi12d (.classEq (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (syn_wa (.classMem (.cv n) (syn_cspfin))
          (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))
      (syn_wrex x (syn_cspfin)
        (.classEq (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv x))))
      p0133 p0135
  have p0137 :=
    @g_mpbiri (.classEq (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))
      (.imp (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
          (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
        (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))
      (.imp (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
          (syn_wa (.classMem (.cv n) (syn_cspfin))
            (syn_wsfin (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv n)))))
        (syn_wrex x (syn_cspfin)
          (.classEq (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))) (syn_ctfin (.cv x)))))
      p0130 p0136
  have p0138 :=
    @g_com12 (.classEq (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0137
  have p0139 :=
    @g_syld
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z))
      (.classEq (.cv z) (syn_ctfin (syn_cncfin (syn_cpw1 (.cv d)))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0094 p0138
  have p0140 :=
    @g_syl5 (syn_wa (.objMem a z) (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d)))))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv d))) (.cv z))
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0079 p0139
  have p0141 :=
    @g_expdimp
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.objMem a z) (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0140
  have p0142 :=
    @g_exlimdv
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
          (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
        (.objMem a z))
      (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) d dv_cache_0025
      dv_cache_0026 p0141
  have p0143 :=
    @g_syl5 (.classEq (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cun (.cv a) (.cv b)))
      (syn_wex d (.classEq (.cv a) (syn_cpw1 (syn_cpw1 (.cv d)))))
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
          (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
        (.objMem a z))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0077 p0142
  have p0144 :=
    @g_adantld
      (syn_wa (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
          (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
        (.objMem a z))
      (.classEq (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cun (.cv a) (.cv b)))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0143
  have p0145 :=
    @g_adantrr
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.objMem a z)
      (.imp (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
          (.classEq (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cun (.cv a) (.cv b))))
        (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))
      (.objMem b p) p0144
  have p0146_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
              (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
            (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
          (syn_wa (.classMem (.cv a) (.cv z)) (.classMem (.cv b) (.cv p)))) (.imp
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cun (.cv a) (.cv b))))
          (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_wrex syn_wex syn_cspfin syn_cint syn_ctfin syn_cif syn_wo syn_c0
          syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_csn
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
    @g_rexlimdvva
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
        (.classEq (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cun (.cv a) (.cv b))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) a b (.cv z) (.cv p)
      dv_cache_0007 dv_cache_0027 dv_cache_0028 dv_cache_0029 dv_cache_0030 dv_cache_0010
      p0146_e00_recanon
  have p0147 :=
    @g_syl5bi (.classMem (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cplc (.cv z) (.cv p)))
      (syn_wrex a (.cv z) (syn_wrex b (.cv p)
          (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
            (.classEq (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cun (.cv a) (.cv b))))))
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0052 p0146
  have p0148 :=
    @g_syld
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classEq (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cplc (.cv z) (.cv p)))
      (.classMem (syn_cpw1 (syn_cpw1 (syn_cvv))) (syn_cplc (.cv z) (.cv p)))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0051 p0147
  have p0149 :=
    @g_rexlimdvw
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (.classEq (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cplc (.cv z) (.cv p)))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p (syn_cnnc)
      dv_cache_0031 dv_cache_0032 p0148
  have p0150 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
        (syn_wa (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))))
      (syn_wrex p (syn_cnnc)
        (.classEq (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cplc (.cv z) (.cv p))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0043 p0149
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

@[expose]
noncomputable def g_vfinspss (x : Var) (a : Var) (dv_a_x : a ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (syn_cvv) (syn_cfin)) (syn_wss (syn_cspfin) (syn_cun
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_cncfin (syn_cvv)))))) :=
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
  have dv_cache_0001 : x ∉ ((syn_cspfin)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((syn_cspfin)).fv :=
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
  have dv_cache_0003 : n ∉ ((Wff.classEq (.cv w) (syn_ctfin (.cv x)))).fv :=
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
  have dv_cache_0004 : x ∉ ((Wff.classEq (.cv w) (syn_ctfin (.cv n)))).fv :=
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
      ((Wff.imp (syn_wsfin (.cv z) (.cv w))
          (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))).fv :=
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
    n ∉ ((syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))).fv :=
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
  have dv_cache_0010 : x ∉ ((syn_cncfin (syn_cvv))).fv :=
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
    x ∉ ((Wff.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (syn_cncfin (syn_cvv))))).fv :=
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
  have dv_cache_0012 : x ∉ ((Wff.classEq (syn_cncfin (syn_c1c)) (.cv z))).fv :=
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
    a ∉ ((syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x))))).fv :=
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
    a ∉ ((syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))).fv :=
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
    z ∉ ((syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))).fv :=
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
  have dv_cache_0020 : w ∉ ((Wff.classMem (syn_cvv) (syn_cfin))).fv :=
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
      ((syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl
              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))).fv :=
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
  have dv_cache_0022 : t ∉ ((syn_cpw1 (syn_cspfin))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (.cv a))
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))).fv :=
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
  have dv_cache_0026 : t ∉ ((syn_cspfin)).fv :=
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
  have dv_cache_0028 : t ∉ ((syn_csn (.cv x))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (.cv x)) (.cv a))
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))).fv :=
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
      ((syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))
          (syn_cpw1 (syn_cspfin)))).fv :=
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
      ((syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv))))).fv :=
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
      ((syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv))))).fv :=
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
  have p0000 := @g_tfineq (.cv x) (.cv n)
  have p0001_e00_recanon :
    Nominal.NPrf (.imp (.objEq x n) (.classEq (syn_ctfin (.cv x)) (syn_ctfin (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0000
  have p0001 :=
    @g_eqeq2d (.objEq x n) (syn_ctfin (.cv x)) (syn_ctfin (.cv n)) (.cv w)
      p0001_e00_recanon
  have p0002 :=
    @g_cbvrexv (.classEq (.cv w) (syn_ctfin (.cv x)))
      (.classEq (.cv w) (syn_ctfin (.cv n))) x n (syn_cspfin) dv_cache_0001 dv_cache_0002
      dv_cache_0003 dv_cache_0004 p0001
  have p0003 := @g_vfinspsslem1 x z n dv_cache_0005 dv_cache_0006 dv_cache_0007
  have p0004 :=
    @g_expr
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
      (.classMem (.cv n) (syn_cspfin)) (syn_wsfin (.cv z) (syn_ctfin (.cv n)))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0003
  have p0005 := @g_eleq1 (.cv w) (syn_ctfin (.cv n)) (syn_cspfin)
  have p0006 :=
    @g_anbi2d (.classEq (.cv w) (syn_ctfin (.cv n))) (.classMem (.cv w) (syn_cspfin))
      (.classMem (syn_ctfin (.cv n)) (syn_cspfin)) (.classMem (syn_cvv) (syn_cfin)) p0005
  have p0007 :=
    @g_anbi1d (.classEq (.cv w) (syn_ctfin (.cv n)))
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ctfin (.cv n)) (syn_cspfin)))
      (.classMem (.cv n) (syn_cspfin)) p0006
  have p0008 := @g_sfineq2 (.cv w) (syn_ctfin (.cv n)) (.cv z)
  have p0009 :=
    @g_imbi1d (.classEq (.cv w) (syn_ctfin (.cv n))) (syn_wsfin (.cv z) (.cv w))
      (syn_wsfin (.cv z) (syn_ctfin (.cv n)))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0008
  have p0010 :=
    @g_imbi12d (.classEq (.cv w) (syn_ctfin (.cv n)))
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
        (.classMem (.cv n) (syn_cspfin)))
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
          (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (.classMem (.cv n) (syn_cspfin)))
      (.imp (syn_wsfin (.cv z) (.cv w))
        (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))
      (.imp (syn_wsfin (.cv z) (syn_ctfin (.cv n)))
        (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))
      p0007 p0009
  have p0011 :=
    @g_mpbiri (.classEq (.cv w) (syn_ctfin (.cv n)))
      (.imp (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
          (.classMem (.cv n) (syn_cspfin))) (.imp (syn_wsfin (.cv z) (.cv w))
          (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))))
      (.imp (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin))
            (.classMem (syn_ctfin (.cv n)) (syn_cspfin))) (.classMem (.cv n) (syn_cspfin)))
        (.imp (syn_wsfin (.cv z) (syn_ctfin (.cv n)))
          (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))))
      p0004 p0010
  have p0012 :=
    @g_com12 (.classEq (.cv w) (syn_ctfin (.cv n)))
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
        (.classMem (.cv n) (syn_cspfin)))
      (.imp (syn_wsfin (.cv z) (.cv w))
        (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))
      p0011
  have p0013 :=
    @g_rexlimdva
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
      (.classEq (.cv w) (syn_ctfin (.cv n)))
      (.imp (syn_wsfin (.cv z) (.cv w))
        (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))
      n (syn_cspfin) dv_cache_0008 dv_cache_0009 p0012
  have p0014 :=
    @g_syl5bi (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x))))
      (syn_wrex n (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv n))))
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
      (.imp (syn_wsfin (.cv z) (.cv w))
        (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))
      p0002 p0013
  have p0015 := @g_sfineq2 (.cv w) (syn_cncfin (syn_cvv)) (.cv z)
  have p0016 :=
    @g_biimpa (.classEq (.cv w) (syn_cncfin (syn_cvv))) (syn_wsfin (.cv z) (.cv w))
      (syn_wsfin (.cv z) (syn_cncfin (syn_cvv))) p0015
  have p0017 := @g_n_1cvsfin
  have p0018 := @g_sfin111 (syn_cncfin (syn_cvv)) (syn_cncfin (syn_c1c)) (.cv z)
  have p0019 := @g_tncveqnc1fin
  have p0020 :=
    @g_eqcomd (.classMem (syn_cvv) (syn_cfin)) (syn_ctfin (syn_cncfin (syn_cvv)))
      (syn_cncfin (syn_c1c)) p0019
  have p0021 := @g_ncvspfin
  have p0022 := @g_tfineq (.cv x) (syn_cncfin (syn_cvv))
  have p0023 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cncfin (syn_cvv))) (syn_ctfin (.cv x))
      (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)) p0022
  have p0024 :=
    @g_rspcev (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x)))
      (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (syn_cncfin (syn_cvv)))) x
      (syn_cncfin (syn_cvv)) (syn_cspfin) dv_cache_0010 dv_cache_0001 dv_cache_0011 p0023
  have p0025 :=
    @g_mpan (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin))
      (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (syn_cncfin (syn_cvv))))
      (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x))))
      p0021 p0024
  have p0026 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (syn_cncfin (syn_cvv))))
      (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x))))
      p0020 p0025
  have p0027 := @g_eqeq1 (syn_cncfin (syn_c1c)) (.cv z) (syn_ctfin (.cv x))
  have p0028 :=
    @g_rexbidv (.classEq (syn_cncfin (syn_c1c)) (.cv z))
      (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x)))
      (.classEq (.cv z) (syn_ctfin (.cv x))) x (syn_cspfin) dv_cache_0012 p0027
  have p0029 :=
    @g_biimpd (.classEq (syn_cncfin (syn_c1c)) (.cv z))
      (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0028
  have p0030 :=
    @g_com12 (.classEq (syn_cncfin (syn_c1c)) (.cv z))
      (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0029
  have p0031 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin))
      (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_c1c)) (syn_ctfin (.cv x))))
      (.imp (.classEq (syn_cncfin (syn_c1c)) (.cv z))
        (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))
      p0026 p0030
  have p0032 :=
    @g_syl5
      (syn_wa (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv)))
        (syn_wsfin (.cv z) (syn_cncfin (syn_cvv))))
      (.classEq (syn_cncfin (syn_c1c)) (.cv z)) (.classMem (syn_cvv) (syn_cfin))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0018 p0031
  have p0033 :=
    @g_mpand (.classMem (syn_cvv) (syn_cfin))
      (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv)))
      (syn_wsfin (.cv z) (syn_cncfin (syn_cvv)))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0017 p0032
  have p0034 :=
    @g_syl5 (syn_wa (.classEq (.cv w) (syn_cncfin (syn_cvv))) (syn_wsfin (.cv z) (.cv w)))
      (syn_wsfin (.cv z) (syn_cncfin (syn_cvv))) (.classMem (syn_cvv) (syn_cfin))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0016 p0033
  have p0035 :=
    @g_exp3a (.classMem (syn_cvv) (syn_cfin)) (.classEq (.cv w) (syn_cncfin (syn_cvv)))
      (syn_wsfin (.cv z) (.cv w))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0034
  have p0036 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin))
      (.imp (.classEq (.cv w) (syn_cncfin (syn_cvv))) (.imp (syn_wsfin (.cv z) (.cv w))
          (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))))
      (.classMem (.cv w) (syn_cspfin)) p0035
  have p0037 :=
    @g_jaod (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
      (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x))))
      (.imp (syn_wsfin (.cv z) (.cv w))
        (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))
      (.classEq (.cv w) (syn_cncfin (syn_cvv))) p0014 p0036
  have p0038 :=
    @g_imp3a (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
      (syn_wo (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x))))
        (.classEq (.cv w) (syn_cncfin (syn_cvv))))
      (syn_wsfin (.cv z) (.cv w))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) p0037
  have p0039 :=
    @g_elun (.cv w)
      (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_csn (syn_cncfin (syn_cvv)))
  have p0040 := @g_vex w
  have p0041 := @g_eqeq1 (.cv a) (.cv w) (syn_ctfin (.cv x))
  have p0042_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a w) (syn_wb (.classEq (.cv a) (syn_ctfin (.cv x)))
          (.classEq (.cv w) (syn_ctfin (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl
          syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0041
  have p0042 :=
    @g_rexbidv (.objEq a w) (.classEq (.cv a) (syn_ctfin (.cv x)))
      (.classEq (.cv w) (syn_ctfin (.cv x))) x (syn_cspfin) dv_cache_0013
      p0042_e00_recanon
  have p0043_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv w))
        (syn_wb (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))
          (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cspfin, syn_cint, syn_ctfin,
          syn_cif, syn_wo, syn_c0, syn_cdif, syn_cin, syn_ccompl, syn_cnin, syn_wnan,
          syn_cvv, syn_cio, syn_cuni, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0042
  have p0043 :=
    @g_elab (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x)))) a (.cv w)
      dv_cache_0014 dv_cache_0015 p0040 p0043_e01_recanon
  have p0044 := @g_elsnc (.cv w) (syn_cncfin (syn_cvv)) p0040
  have p0045 :=
    @g_orbi12i
      (.classMem (.cv w)
        (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x))))
      (.classMem (.cv w) (syn_csn (syn_cncfin (syn_cvv))))
      (.classEq (.cv w) (syn_cncfin (syn_cvv))) p0043 p0044
  have p0046 :=
    @g_bitri
      (.classMem (.cv w)
        (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))))
      (syn_wo (.classMem (.cv w)
          (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
        (.classMem (.cv w) (syn_csn (syn_cncfin (syn_cvv)))))
      (syn_wo (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x))))
        (.classEq (.cv w) (syn_cncfin (syn_cvv))))
      p0039 p0045
  have p0047 :=
    @g_anbi1i
      (.classMem (.cv w)
        (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))))
      (syn_wo (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x))))
        (.classEq (.cv w) (syn_cncfin (syn_cvv))))
      (syn_wsfin (.cv z) (.cv w)) p0046
  have p0048 := @g_vex z
  have p0049 := @g_eqeq1 (.cv a) (.cv z) (syn_ctfin (.cv x))
  have p0050_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq a z) (syn_wb (.classEq (.cv a) (syn_ctfin (.cv x)))
          (.classEq (.cv z) (syn_ctfin (.cv x))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl
          syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0049
  have p0050 :=
    @g_rexbidv (.objEq a z) (.classEq (.cv a) (syn_ctfin (.cv x)))
      (.classEq (.cv z) (syn_ctfin (.cv x))) x (syn_cspfin) dv_cache_0016
      p0050_e00_recanon
  have p0051_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (.cv z))
        (syn_wb (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))
          (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cspfin, syn_cint, syn_ctfin,
          syn_cif, syn_wo, syn_c0, syn_cdif, syn_cin, syn_ccompl, syn_cnin, syn_wnan,
          syn_cvv, syn_cio, syn_cuni, syn_csn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0050
  have p0051 :=
    @g_elab (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x)))) a (.cv z)
      dv_cache_0017 dv_cache_0018 p0048 p0051_e01_recanon
  have p0052 :=
    @g_n_3imtr4g
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
      (syn_wa (syn_wo (syn_wrex x (syn_cspfin) (.classEq (.cv w) (syn_ctfin (.cv x))))
          (.classEq (.cv w) (syn_cncfin (syn_cvv)))) (syn_wsfin (.cv z) (.cv w)))
      (syn_wrex x (syn_cspfin) (.classEq (.cv z) (syn_ctfin (.cv x))))
      (syn_wa (.classMem (.cv w) (syn_cun
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w)))
      (.classMem (.cv z)
        (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      p0038 p0047 p0051
  have p0053 :=
    @g_ssun1 (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_csn (syn_cncfin (syn_cvv)))
  have p0054 :=
    @g_sseli (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_csn (syn_cncfin (syn_cvv))))
      (.cv z) p0053
  have p0055 :=
    @g_syl6 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
      (syn_wa (.classMem (.cv w) (syn_cun
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w)))
      (.classMem (.cv z)
        (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      (.classMem (.cv z)
        (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))))
      p0052 p0054
  have p0056 :=
    @g_alrimiv (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv w) (syn_cspfin)))
      (.imp (syn_wa (.classMem (.cv w) (syn_cun
              (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w))) (.classMem (.cv z)
          (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_cncfin (syn_cvv))))))
      z dv_cache_0019 p0055
  have p0057 :=
    @g_ralrimiva (.classMem (syn_cvv) (syn_cfin))
      (.all z (.imp (syn_wa (.classMem (.cv w) (syn_cun
                (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w)))
          (.classMem (.cv z) (syn_cun
              (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
              (syn_csn (syn_cncfin (syn_cvv)))))))
      w (syn_cspfin) dv_cache_0020 p0056
  have p0058 := @g_vex a
  have p0059 :=
    @g_elimak t
      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl
            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                    (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                    (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))
      (syn_cpw1 (syn_cspfin)) (.cv a) dv_cache_0021 dv_cache_0022 dv_cache_0023 p0058
  have p0060 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cspfin)) (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))
  have p0061 := @g_elpw1 x (.cv t) (syn_cspfin) dv_cache_0024 dv_cache_0001
  have p0062 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cspfin)))
      (syn_wrex x (syn_cspfin) (.classEq (.cv t) (syn_csn (.cv x))))
      (.classMem (syn_copk (.cv t) (.cv a))
        (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))
      p0061
  have p0063 :=
    @g_r19_41v (.classEq (.cv t) (syn_csn (.cv x)))
      (.classMem (syn_copk (.cv t) (.cv a))
        (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))
      x (syn_cspfin) dv_cache_0025
  have p0064 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
      (syn_wa (syn_wrex x (syn_cspfin) (.classEq (.cv t) (syn_csn (.cv x))))
        (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
      (syn_wrex x (syn_cspfin) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv a))
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))
      p0062 p0063
  have p0065 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin))) (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
      (syn_wrex x (syn_cspfin) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv a))
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))
      t p0064
  have p0066 :=
    @g_rexcom4
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
      x t (syn_cspfin) dv_cache_0026 dv_cache_0027
  have p0067 :=
    @g_bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin)))
          (.classMem (syn_copk (.cv t) (.cv a))
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))
      (syn_wex t (syn_wrex x (syn_cspfin) (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv a))
              (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                    (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))))
      (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv a))
              (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                    (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))))
      p0065 p0066
  have p0068 :=
    @g_bitri
      (syn_wrex t (syn_cpw1 (syn_cspfin)) (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cspfin)))
          (.classMem (syn_copk (.cv t) (.cv a))
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))
      (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv a))
              (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                    (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))))
      p0060 p0067
  have p0069 :=
    @g_bitri
      (.classMem (.cv a) (syn_cimak
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin))))
      (syn_wrex t (syn_cpw1 (syn_cspfin)) (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
      (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv a))
              (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                    (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))))
      p0059 p0068
  have p0070 := @g_snex (.cv x)
  have p0071 := @g_opkeq1 (.cv t) (syn_csn (.cv x)) (.cv a)
  have p0072 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_copk (.cv t) (.cv a))
      (syn_copk (syn_csn (.cv x)) (.cv a))
      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl
            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                    (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                    (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))
      p0071
  have p0073 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (.cv a))
        (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a))
        (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))
      t (syn_csn (.cv x)) dv_cache_0028 dv_cache_0029 p0070 p0072
  have p0074 := @g_vex x
  have p0075 := @g_eqtfinrelk (.cv x) (.cv a) p0074 p0058
  have p0076 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv a))
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a))
        (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))
      (.classEq (.cv a) (syn_ctfin (.cv x))) p0073 p0075
  have p0077 :=
    @g_rexbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv a))
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))
      (.classEq (.cv a) (syn_ctfin (.cv x))) x (syn_cspfin) p0076
  have p0078 :=
    @g_bitri
      (.classMem (.cv a) (syn_cimak
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin))))
      (syn_wrex x (syn_cspfin) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv a))
              (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                    (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))))
      (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) p0069 p0077
  have p0079 :=
    @g_eqabi (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) a
      (syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)))
      dv_cache_0030 p0078
  have p0080 := @g_tfinrelkex
  have p0081 := @g_spfinex
  have p0082 := @g_pw1ex (syn_cspfin) p0081
  have p0083 :=
    @g_imakex
      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl
            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                    (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                    (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))
      (syn_cpw1 (syn_cspfin)) p0080 p0082
  have p0084 :=
    @g_eqeltrri
      (syn_cimak (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))) (syn_cpw1 (syn_cspfin)))
      (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cvv)
      p0079 p0083
  have p0085 := @g_snex (syn_cncfin (syn_cvv))
  have p0086 :=
    @g_unex (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_csn (syn_cncfin (syn_cvv))) p0084 p0085
  have p0087 :=
    @g_ssun2 (syn_csn (syn_cncfin (syn_cvv)))
      (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
  have p0088 := @g_ncfinex (syn_cvv)
  have p0089 := @g_snid (syn_cncfin (syn_cvv)) p0088
  have p0090 :=
    @g_sselii (syn_csn (syn_cncfin (syn_cvv)))
      (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_csn (syn_cncfin (syn_cvv))))
      (syn_cncfin (syn_cvv)) p0087 p0089
  have p0091 :=
    @g_spfininduct w z
      (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_csn (syn_cncfin (syn_cvv))))
      (syn_cvv) dv_cache_0031 dv_cache_0032 dv_cache_0033
  have p0092 :=
    @g_mp3an12
      (.classMem
        (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))) (syn_cvv))
      (.classMem (syn_cncfin (syn_cvv))
        (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))))
      (syn_wral w (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv w) (syn_cun (.cab a
                    (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                  (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w)))
            (.classMem (.cv z) (syn_cun
                (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_csn (syn_cncfin (syn_cvv))))))))
      (syn_wss (syn_cspfin)
        (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))))
      p0086 p0090 p0091
  have p0093 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin))
      (syn_wral w (syn_cspfin) (.all z (.imp (syn_wa (.classMem (.cv w) (syn_cun (.cab a
                    (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                  (syn_csn (syn_cncfin (syn_cvv))))) (syn_wsfin (.cv z) (.cv w)))
            (.classMem (.cv z) (syn_cun
                (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_csn (syn_cncfin (syn_cvv))))))))
      (syn_wss (syn_cspfin)
        (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))))
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

@[expose]
noncomputable def g_vfinspclt (X : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem X (syn_cspfin)))
        (.classMem (syn_ctfin X) (syn_cspfin))) :=
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
  have dv_cache_0001 : x ∉ ((syn_cncfin (syn_cvv))).fv := by
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
    x ∉ ((Wff.classMem (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cspfin))).fv :=
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
  have dv_cache_0004 : x ∉ ((Wff.classMem (syn_ctfin (.cv y)) (syn_cspfin))).fv :=
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
  have dv_cache_0006 : x ∉ ((Wff.classMem (syn_ctfin (.cv z)) (syn_cspfin))).fv :=
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
    z ∉ ((syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin)))).fv :=
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
  have dv_cache_0008 : y ∉ ((Wff.classMem (syn_cvv) (syn_cfin))).fv :=
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
      ((syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))).fv :=
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
  have dv_cache_0010 : y ∉ ((syn_cspfin)).fv :=
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
  have dv_cache_0011 : y ∉ ((syn_csn (.cv x))).fv :=
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
  have dv_cache_0012 : y ∉ ((syn_ctfin (.cv x))).fv :=
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
      ((syn_cuni1 (syn_cimak (syn_ccnvk
              (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                    (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin)))).fv :=
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
    y ∉ ((Class.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))).fv :=
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
    z ∉ ((Class.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))).fv :=
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
  have dv_cache_0018 : x ∉ ((Wff.classMem (syn_ctfin X) (syn_cspfin))).fv :=
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
  have p0000 := @g_tncveqnc1fin
  have p0001 := @g_n_1cspfin
  have p0002 :=
    @g_eqeltrd (.classMem (syn_cvv) (syn_cfin)) (syn_ctfin (syn_cncfin (syn_cvv)))
      (syn_cncfin (syn_c1c)) (syn_cspfin) p0000 p0001
  have p0003 := @g_ncfinex (syn_cvv)
  have p0004 := @g_tfineq (.cv x) (syn_cncfin (syn_cvv))
  have p0005 :=
    @g_eleq1d (.classEq (.cv x) (syn_cncfin (syn_cvv))) (syn_ctfin (.cv x))
      (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cspfin) p0004
  have p0006 :=
    @g_elab (.classMem (syn_ctfin (.cv x)) (syn_cspfin))
      (.classMem (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cspfin)) x (syn_cncfin (syn_cvv))
      dv_cache_0001 dv_cache_0002 p0003 p0005
  have p0007 :=
    @g_sylibr (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cspfin))
      (.classMem (syn_cncfin (syn_cvv)) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
      p0002 p0006
  have p0008 :=
    @g_simprl (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin)))
      (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (.cv z) (.cv y))
  have p0009 := @g_sfintfin (.cv z) (.cv y)
  have p0010 :=
    @g_ad2antll (syn_wsfin (.cv z) (.cv y))
      (syn_wsfin (syn_ctfin (.cv z)) (syn_ctfin (.cv y)))
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin)))
      (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) p0009
  have p0011 := @g_spfinsfincl (syn_ctfin (.cv y)) (syn_ctfin (.cv z))
  have p0012 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin)))
        (syn_wa (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (.cv z) (.cv y))))
      (.classMem (syn_ctfin (.cv y)) (syn_cspfin))
      (syn_wsfin (syn_ctfin (.cv z)) (syn_ctfin (.cv y)))
      (.classMem (syn_ctfin (.cv z)) (syn_cspfin)) p0008 p0010 p0011
  have p0013 :=
    @g_ex (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin)))
      (syn_wa (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (.cv z) (.cv y)))
      (.classMem (syn_ctfin (.cv z)) (syn_cspfin)) p0012
  have p0014 := @g_vex y
  have p0015 := @g_tfineq (.cv x) (.cv y)
  have p0016_e00_recanon :
    Nominal.NPrf (.imp (.objEq x y) (.classEq (syn_ctfin (.cv x)) (syn_ctfin (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @g_eleq1d (.objEq x y) (syn_ctfin (.cv x)) (syn_ctfin (.cv y)) (syn_cspfin)
      p0016_e00_recanon
  have p0017_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv y)) (syn_wb (.classMem (syn_ctfin (.cv x)) (syn_cspfin))
          (.classMem (syn_ctfin (.cv y)) (syn_cspfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl
          syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn syn_cspfin syn_cint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0017 :=
    @g_elab (.classMem (syn_ctfin (.cv x)) (syn_cspfin))
      (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) x (.cv y) dv_cache_0003 dv_cache_0004
      p0014 p0017_e01_recanon
  have p0018 :=
    @g_anbi1i (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
      (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (.cv z) (.cv y)) p0017
  have p0019 := @g_vex z
  have p0020 := @g_tfineq (.cv x) (.cv z)
  have p0021_e00_recanon :
    Nominal.NPrf (.imp (.objEq x z) (.classEq (syn_ctfin (.cv x)) (syn_ctfin (.cv z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin
          syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0020
  have p0021 :=
    @g_eleq1d (.objEq x z) (syn_ctfin (.cv x)) (syn_ctfin (.cv z)) (syn_cspfin)
      p0021_e00_recanon
  have p0022_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (syn_wb (.classMem (syn_ctfin (.cv x)) (syn_cspfin))
          (.classMem (syn_ctfin (.cv z)) (syn_cspfin)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ctfin syn_cif syn_wo syn_wa syn_c0 syn_cdif syn_cin syn_ccompl
          syn_cnin syn_wnan syn_cvv syn_cio syn_cuni syn_wex syn_csn syn_cspfin syn_cint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0021
  have p0022 :=
    @g_elab (.classMem (syn_ctfin (.cv x)) (syn_cspfin))
      (.classMem (syn_ctfin (.cv z)) (syn_cspfin)) x (.cv z) dv_cache_0005 dv_cache_0006
      p0019 p0022_e01_recanon
  have p0023 :=
    @g_n_3imtr4g
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin)))
      (syn_wa (.classMem (syn_ctfin (.cv y)) (syn_cspfin)) (syn_wsfin (.cv z) (.cv y)))
      (.classMem (syn_ctfin (.cv z)) (syn_cspfin))
      (syn_wa (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
        (syn_wsfin (.cv z) (.cv y)))
      (.classMem (.cv z) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) p0013
      p0018 p0022
  have p0024 :=
    @g_alrimiv (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv y) (syn_cspfin)))
      (.imp (syn_wa (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
          (syn_wsfin (.cv z) (.cv y)))
        (.classMem (.cv z) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))))
      z dv_cache_0007 p0023
  have p0025 :=
    @g_ralrimiva (.classMem (syn_cvv) (syn_cfin))
      (.all z (.imp (syn_wa
            (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
            (syn_wsfin (.cv z) (.cv y)))
          (.classMem (.cv z) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))))
      y (syn_cspfin) dv_cache_0008 p0024
  have p0026 := @g_snex (.cv x)
  have p0027 :=
    @g_elimak y
      (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))
      (syn_cspfin) (syn_csn (.cv x)) dv_cache_0009 dv_cache_0010 dv_cache_0011 p0026
  have p0028 :=
    @g_opkelcnvk (.cv y) (syn_csn (.cv x))
      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl
            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                    (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                    (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))
      p0014 p0026
  have p0029 := @g_vex x
  have p0030 := @g_eqtfinrelk (.cv x) (.cv y) p0029 p0014
  have p0031 :=
    @g_bitri
      (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv y))
        (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))
      (.classEq (.cv y) (syn_ctfin (.cv x))) p0028 p0030
  have p0032 :=
    @g_rexbii
      (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk
          (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
      (.classEq (.cv y) (syn_ctfin (.cv x))) y (syn_cspfin) p0031
  have p0033 :=
    @g_bitri
      (.classMem (syn_csn (.cv x)) (syn_cimak (syn_ccnvk
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin)))
      (syn_wrex y (syn_cspfin) (.classMem (syn_copk (.cv y) (syn_csn (.cv x))) (syn_ccnvk
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))
      (syn_wrex y (syn_cspfin) (.classEq (.cv y) (syn_ctfin (.cv x)))) p0027 p0032
  have p0034 :=
    @g_eluni1 (.cv x)
      (syn_cimak (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
            (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin))
      p0029
  have p0035 := @g_risset y (syn_ctfin (.cv x)) (syn_cspfin) dv_cache_0012 dv_cache_0010
  have p0036 :=
    @g_n_3bitr4i
      (.classMem (syn_csn (.cv x)) (syn_cimak (syn_ccnvk
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin)))
      (syn_wrex y (syn_cspfin) (.classEq (.cv y) (syn_ctfin (.cv x))))
      (.classMem (.cv x) (syn_cuni1 (syn_cimak (syn_ccnvk
              (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                    (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin))))
      (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) p0033 p0034 p0035
  have p0037 :=
    @g_eqabi (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) x
      (syn_cuni1 (syn_cimak (syn_ccnvk
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin)))
      dv_cache_0013 p0036
  have p0038 := @g_tfinrelkex
  have p0039 :=
    @g_cnvkex
      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl
            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                    (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                    (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))
      p0038
  have p0040 := @g_spfinex
  have p0041 :=
    @g_imakex
      (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
                                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
                                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                      (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))
      (syn_cspfin) p0039 p0040
  have p0042 :=
    @g_uni1ex
      (syn_cimak (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
            (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                            (syn_cimak (syn_csymdif (syn_cins2k
                                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                      (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k
        (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c))
        (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin))
      p0041
  have p0043 :=
    @g_eqeltrri
      (syn_cuni1 (syn_cimak (syn_ccnvk
            (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                              (syn_cimak (syn_csymdif (syn_cins2k
                                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
                                        (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                          (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))) (syn_cspfin)))
      (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))) (syn_cvv) p0037 p0042
  have p0044 :=
    @g_spfininduct y z (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))) (syn_cvv)
      dv_cache_0014 dv_cache_0015 dv_cache_0016
  have p0045 :=
    @g_mp3an1 (.classMem (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))) (syn_cvv))
      (.classMem (syn_cncfin (syn_cvv)) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
      (syn_wral y (syn_cspfin) (.all z (.imp (syn_wa
              (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
              (syn_wsfin (.cv z) (.cv y)))
            (.classMem (.cv z) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))))))
      (syn_wss (syn_cspfin) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) p0043
      p0044
  have p0046 :=
    @g_syl2anc (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cvv)) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
      (syn_wral y (syn_cspfin) (.all z (.imp (syn_wa
              (.classMem (.cv y) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
              (syn_wsfin (.cv z) (.cv y)))
            (.classMem (.cv z) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))))))
      (syn_wss (syn_cspfin) (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin)))) p0007
      p0025 p0045
  have p0047 :=
    @g_sselda (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin)
      (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))) X p0046
  have p0048 := @g_tfineq (.cv x) X
  have p0049 :=
    @g_eleq1d (.classEq (.cv x) X) (syn_ctfin (.cv x)) (syn_ctfin X) (syn_cspfin) p0048
  have p0050 :=
    @g_elabg (.classMem (syn_ctfin (.cv x)) (syn_cspfin))
      (.classMem (syn_ctfin X) (syn_cspfin)) x X (syn_cspfin) dv_cache_0017 dv_cache_0018
      p0049
  have p0051 :=
    @g_adantl (.classMem X (syn_cspfin))
      (syn_wb (.classMem X (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
        (.classMem (syn_ctfin X) (syn_cspfin)))
      (.classMem (syn_cvv) (syn_cfin)) p0050
  have p0052 :=
    @g_mpbid (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem X (syn_cspfin)))
      (.classMem X (.cab x (.classMem (syn_ctfin (.cv x)) (syn_cspfin))))
      (.classMem (syn_ctfin X) (syn_cspfin)) p0047 p0051
  exact p0052

@[expose]
noncomputable def g_vfinspeqtncv (x : Var) (a : Var) (dv_a_x : a ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cspfin) (syn_cun
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_cncfin (syn_cvv)))))) :=
  by
  have dv_cache_0001 : a ≠ x := by exact (show a ≠ x from (by exact dv_a_x))
  have dv_cache_0002 : x ∉ ((Wff.classMem (.cv a) (syn_cspfin))).fv :=
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
  have dv_cache_0003 : x ∉ ((Wff.classMem (syn_cvv) (syn_cfin))).fv :=
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
  have dv_cache_0004 : a ∉ ((syn_cspfin)).fv :=
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
  have dv_cache_0005 : a ∉ ((Wff.classMem (syn_cvv) (syn_cfin))).fv :=
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
  have p0000 := @g_vfinspss x a dv_cache_0001
  have p0001 := @g_vfinspclt (.cv x)
  have p0002 := @g_eleq1 (.cv a) (syn_ctfin (.cv x)) (syn_cspfin)
  have p0003 :=
    @g_biimprd (.classEq (.cv a) (syn_ctfin (.cv x))) (.classMem (.cv a) (syn_cspfin))
      (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) p0002
  have p0004 :=
    @g_com12 (.classEq (.cv a) (syn_ctfin (.cv x)))
      (.classMem (syn_ctfin (.cv x)) (syn_cspfin)) (.classMem (.cv a) (syn_cspfin)) p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv x) (syn_cspfin)))
      (.classMem (syn_ctfin (.cv x)) (syn_cspfin))
      (.imp (.classEq (.cv a) (syn_ctfin (.cv x))) (.classMem (.cv a) (syn_cspfin))) p0001
      p0004
  have p0006 :=
    @g_rexlimdva (.classMem (syn_cvv) (syn_cfin)) (.classEq (.cv a) (syn_ctfin (.cv x)))
      (.classMem (.cv a) (syn_cspfin)) x (syn_cspfin) dv_cache_0002 dv_cache_0003 p0005
  have p0007 :=
    @g_abssdv (.classMem (syn_cvv) (syn_cfin))
      (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) a (syn_cspfin)
      dv_cache_0004 dv_cache_0005 p0006
  have p0008 := @g_ncvspfin
  have p0009 := @g_ncfinex (syn_cvv)
  have p0010 := @g_snss (syn_cncfin (syn_cvv)) (syn_cspfin) p0009
  have p0011 :=
    @g_mpbi (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin))
      (syn_wss (syn_csn (syn_cncfin (syn_cvv))) (syn_cspfin)) p0008 p0010
  have p0012 :=
    @g_jctir (.classMem (syn_cvv) (syn_cfin))
      (syn_wss (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_cspfin))
      (syn_wss (syn_csn (syn_cncfin (syn_cvv))) (syn_cspfin)) p0007 p0011
  have p0013 :=
    @g_unss (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_csn (syn_cncfin (syn_cvv))) (syn_cspfin)
  have p0014 :=
    @g_sylib (.classMem (syn_cvv) (syn_cfin))
      (syn_wa (syn_wss (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_cspfin)) (syn_wss (syn_csn (syn_cncfin (syn_cvv))) (syn_cspfin)))
      (syn_wss
        (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))) (syn_cspfin))
      p0012 p0013
  have p0015 :=
    @g_eqssd (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin)
      (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_csn (syn_cncfin (syn_cvv))))
      p0000 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end
