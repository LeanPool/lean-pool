/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block005

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part015`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_sfintfin`. -/
@[expose]
noncomputable def gSfintfin (M : Class) (N : Class) :
    Nominal.NPrf (.imp (synWsfin M N) (synWsfin (synCtfin M) (synCtfin N))) :=
  by
  let proofSupport : Finset Var := M.fv ∪ N.fv
  let a : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let k : Var := freshVar proofSupport 2
  let m : Var := freshVar proofSupport 3
  let p : Var := freshVar proofSupport 4
  let q : Var := freshVar proofSupport 5
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_M : a ∉ M.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (h))
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_N : n ∉ N.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_k : k ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_k_not_M : k ∉ M.fv := by
    intro h
    exact fresh_k (Finset.mem_union_left _ (h))
  have fresh_a_ne_n : a ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_m : a ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_a_ne_p : a ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_a_ne_q : a ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_n_ne_k : n ≠ k :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_k_ne_n : k ≠ n := Ne.symm fresh_n_ne_k
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_n_ne_p : n ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_p_ne_n : p ≠ n := Ne.symm fresh_n_ne_p
  have fresh_n_ne_q : n ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_q_ne_n : q ≠ n := Ne.symm fresh_n_ne_q
  have fresh_k_ne_m : k ≠ m :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_m_ne_k : m ≠ k := Ne.symm fresh_k_ne_m
  have fresh_k_ne_p : k ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_k_ne_q : k ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_m_ne_p : m ≠ p :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_p_ne_m : p ≠ m := Ne.symm fresh_m_ne_p
  have fresh_m_ne_q : m ≠ q :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_q_ne_m : q ≠ m := Ne.symm fresh_m_ne_q
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : a ∉ (M).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_M, not_false_eq_true])
  have dv_cache_0002 : a ∉ (N).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_N, not_false_eq_true])
  have dv_cache_0003 : k ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show k ≠ n from (by exact fresh_k_ne_n))
  have dv_cache_0004 : n ∉ ((Wff.classEq (.cv k) (synC0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_k, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.objEq k m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_m, or_false, not_false_eq_true])
  have dv_cache_0006 :
    p ∉
      ((Wff.imp (synWsfin (.cv m) (.cv n))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_m, fresh_p_ne_n, or_false, not_false_eq_true])
  have dv_cache_0007 :
    n ∉
      ((Wff.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_p, or_false, not_false_eq_true])
  have dv_cache_0008 : n ∉ ((Wff.classEq (.cv k) (synCplc (.cv m) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_k, fresh_n_ne_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((Wff.classEq (.cv k) M)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_k, fresh_n_not_M, or_false, not_false_eq_true])
  have dv_cache_0010 : a ∉ ((synCplc (.cv m) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : a ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_n, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_m, not_false_eq_true])
  have dv_cache_0013 :
    p ∉
      ((Wff.imp (synWsfin (.cv m) (.cv q))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_m, fresh_p_ne_q, or_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((synCplc (.cv q) (.cv q))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_q, or_false, not_false_eq_true])
  have dv_cache_0015 : a ∉ ((synCtfin (.cv m))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_m,
          not_false_eq_true])
  have dv_cache_0016 : a ∉ ((synCtfin (.cv q))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_a_ne_q,
          not_false_eq_true])
  have dv_cache_0017 : k ∉ ((synCtfin (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_k_ne_m,
          not_false_eq_true])
  have dv_cache_0018 :
    k ∉
      ((synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
          (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_k_ne_m, fresh_k_ne_q, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0019 :
    k ∉
      ((synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
              (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                  (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_singleton, fresh_k_ne_m, fresh_k_ne_n, fresh_k_ne_q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 :
    a ∉
      ((synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
          (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_q, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0021 :
    a ∉
      ((synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
              (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                  (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, fresh_a_ne_q,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : a ∉ ((synWne (synCplc (.cv m) (synC1c)) (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0023 : a ∉ ((synWne (synCplc (.cv q) (.cv q)) (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0024 :
    q ∉ ((synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_m, fresh_q_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0025 :
    q ∉
      ((synW3a (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
              (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
          (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_ne_m, fresh_q_ne_n,
          fresh_q_ne_p, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0026 :
    a ∉ ((synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0027 :
    a ∉
      ((synW3a (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
              (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
          (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_w3a,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n,
          fresh_a_ne_p, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0028 :
    n ∉
      ((synWa (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
              (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_p,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0029 : k ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_k_not_M, not_false_eq_true])
  have dv_cache_0030 :
    k ∉
      ((Wff.all p (.imp (synWsfin (.cv m) (.cv p))
            (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_ne_m, fresh_k_ne_p, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0031 :
    m ∉
      ((Wff.all n (.imp (synWsfin (.cv k) (.cv n))
            (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_ne_k, fresh_m_ne_n, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0032 :
    k ∉
      ((Wff.all n (.imp (synWsfin (synC0c) (.cv n))
            (synWsfin (synC0c) (synCtfin (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_ne_n, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0033 :
    k ∉
      ((Wff.all n (.imp (synWsfin M (.cv n))
            (synWsfin (synCtfin M) (synCtfin (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_not_M, fresh_k_ne_n, or_false,
          and_false, not_false_eq_true])
  have dv_cache_0034 :
    k ∉
      ((Wff.all n (.imp (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_ne_m, fresh_k_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0035 : k ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact (show k ≠ m from (by exact fresh_k_ne_m))
  have dv_cache_0036 : n ∉ (N).fv :=
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
        simp only [fresh_n_not_N, not_false_eq_true])
  have dv_cache_0037 :
    n ∉ ((Wff.imp (synWsfin M N) (synWsfin (synCtfin M) (synCtfin N)))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          fresh_n_not_M, fresh_n_not_N, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin M N a
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @gN3simpa (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N)))
  have p0002 :=
    @gSylbi (synWsfin M N)
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (synWex a
          (synWa (.classMem (synCpw1 (.cv a)) M) (.classMem (synCpw (.cv a)) N))))
      (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc))) p0000 p0001
  have p0003 := @gSfintfinlem1 k n dv_cache_0003
  have p0004 := @gSfineq1 (.cv k) (synC0c) (.cv n)
  have p0005 := @gTfineq (.cv k) (synC0c)
  have p0006 := @gTfin0c
  have p0007 :=
    @gSyl6eq (.classEq (.cv k) (synC0c)) (synCtfin (.cv k)) (synCtfin (synC0c))
      (synC0c) p0005 p0006
  have p0008 := @gSfineq1 (synCtfin (.cv k)) (synC0c) (synCtfin (.cv n))
  have p0009 :=
    @gSyl (.classEq (.cv k) (synC0c)) (.classEq (synCtfin (.cv k)) (synC0c))
      (synWb (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))
        (synWsfin (synC0c) (synCtfin (.cv n))))
      p0007 p0008
  have p0010 :=
    @gImbi12d (.classEq (.cv k) (synC0c)) (synWsfin (.cv k) (.cv n))
      (synWsfin (synC0c) (.cv n)) (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))
      (synWsfin (synC0c) (synCtfin (.cv n))) p0004 p0009
  have p0011 :=
    @gAlbidv (.classEq (.cv k) (synC0c))
      (.imp (synWsfin (.cv k) (.cv n)) (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n))))
      (.imp (synWsfin (synC0c) (.cv n)) (synWsfin (synC0c) (synCtfin (.cv n)))) n
      dv_cache_0004 p0010
  have p0012 := @gSfineq1 (.cv k) (.cv m) (.cv n)
  have p0013 := @gTfineq (.cv k) (.cv m)
  have p0014 := @gSfineq1 (synCtfin (.cv k)) (synCtfin (.cv m)) (synCtfin (.cv n))
  have p0015_e00_recanon :
    Nominal.NPrf (.imp (.objEq k m) (.classEq (synCtfin (.cv k)) (synCtfin (.cv m)))) :=
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
      p0013
  have p0015 :=
    @gSyl (.objEq k m) (.classEq (synCtfin (.cv k)) (synCtfin (.cv m)))
      (synWb (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n))))
      p0015_e00_recanon p0014
  have p0016_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq k m) (synWb (synWsfin (.cv k) (.cv n)) (synWsfin (.cv m) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsfin synW3a synWa synCnnc synCint synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0016 :=
    @gImbi12d (.objEq k m) (synWsfin (.cv k) (.cv n)) (synWsfin (.cv m) (.cv n))
      (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n))) p0016_e00_recanon p0015
  have p0017 :=
    @gAlbidv (.objEq k m)
      (.imp (synWsfin (.cv k) (.cv n)) (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n))))
      (.imp (synWsfin (.cv m) (.cv n)) (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n))))
      n dv_cache_0005 p0016
  have p0018 := @gSfineq2 (.cv n) (.cv p) (.cv m)
  have p0019 := @gTfineq (.cv n) (.cv p)
  have p0020 := @gSfineq2 (synCtfin (.cv n)) (synCtfin (.cv p)) (synCtfin (.cv m))
  have p0021_e00_recanon :
    Nominal.NPrf (.imp (.objEq n p) (.classEq (synCtfin (.cv n)) (synCtfin (.cv p)))) :=
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
      p0019
  have p0021 :=
    @gSyl (.objEq n p) (.classEq (synCtfin (.cv n)) (synCtfin (.cv p)))
      (synWb (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n)))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p))))
      p0021_e00_recanon p0020
  have p0022_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n p) (synWb (synWsfin (.cv m) (.cv n)) (synWsfin (.cv m) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsfin synW3a synWa synCnnc synCint synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0022 :=
    @gImbi12d (.objEq n p) (synWsfin (.cv m) (.cv n)) (synWsfin (.cv m) (.cv p))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n)))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p))) p0022_e00_recanon p0021
  have p0023 :=
    @gCbvalv
      (.imp (synWsfin (.cv m) (.cv n)) (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n))))
      (.imp (synWsfin (.cv m) (.cv p)) (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p))))
      n p dv_cache_0006 dv_cache_0007 p0022
  have p0024 :=
    @gSyl6bb (.objEq k m)
      (.all n (.imp (synWsfin (.cv k) (.cv n))
          (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))))
      (.all n (.imp (synWsfin (.cv m) (.cv n))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv n)))))
      (.all p (.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
      p0017 p0023
  have p0025 := @gSfineq1 (.cv k) (synCplc (.cv m) (synC1c)) (.cv n)
  have p0026 := @gTfineq (.cv k) (synCplc (.cv m) (synC1c))
  have p0027 :=
    @gSfineq1 (synCtfin (.cv k)) (synCtfin (synCplc (.cv m) (synC1c)))
      (synCtfin (.cv n))
  have p0028 :=
    @gSyl (.classEq (.cv k) (synCplc (.cv m) (synC1c)))
      (.classEq (synCtfin (.cv k)) (synCtfin (synCplc (.cv m) (synC1c))))
      (synWb (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))
        (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))))
      p0026 p0027
  have p0029 :=
    @gImbi12d (.classEq (.cv k) (synCplc (.cv m) (synC1c))) (synWsfin (.cv k) (.cv n))
      (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0025 p0028
  have p0030 :=
    @gAlbidv (.classEq (.cv k) (synCplc (.cv m) (synC1c)))
      (.imp (synWsfin (.cv k) (.cv n)) (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n))))
      (.imp (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
        (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))))
      n dv_cache_0008 p0029
  have p0031 := @gSfineq1 (.cv k) M (.cv n)
  have p0032 := @gTfineq (.cv k) M
  have p0033 := @gSfineq1 (synCtfin (.cv k)) (synCtfin M) (synCtfin (.cv n))
  have p0034 :=
    @gSyl (.classEq (.cv k) M) (.classEq (synCtfin (.cv k)) (synCtfin M))
      (synWb (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))
        (synWsfin (synCtfin M) (synCtfin (.cv n))))
      p0032 p0033
  have p0035 :=
    @gImbi12d (.classEq (.cv k) M) (synWsfin (.cv k) (.cv n)) (synWsfin M (.cv n))
      (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))
      (synWsfin (synCtfin M) (synCtfin (.cv n))) p0031 p0034
  have p0036 :=
    @gAlbidv (.classEq (.cv k) M)
      (.imp (synWsfin (.cv k) (.cv n)) (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n))))
      (.imp (synWsfin M (.cv n)) (synWsfin (synCtfin M) (synCtfin (.cv n)))) n
      dv_cache_0009 p0035
  have p0037 := @gSfin01
  have p0038 := @gSfin112 (synC1c) (synC0c) (.cv n)
  have p0039 :=
    @gMpan2 (synWsfin (synC0c) (.cv n)) (synWsfin (synC0c) (synC1c))
      (.classEq (.cv n) (synC1c)) p0037 p0038
  have p0041 := @gTfineq (.cv n) (synC1c)
  have p0042 := @gTfin1c
  have p0043 :=
    @gSyl6eq (.classEq (.cv n) (synC1c)) (synCtfin (.cv n)) (synCtfin (synC1c))
      (synC1c) p0041 p0042
  have p0044 := @gSfineq2 (synCtfin (.cv n)) (synC1c) (synC0c)
  have p0045 :=
    @gSyl (.classEq (.cv n) (synC1c)) (.classEq (synCtfin (.cv n)) (synC1c))
      (synWb (synWsfin (synC0c) (synCtfin (.cv n))) (synWsfin (synC0c) (synC1c)))
      p0043 p0044
  have p0046 :=
    @gMpbiri (.classEq (.cv n) (synC1c)) (synWsfin (synC0c) (synCtfin (.cv n)))
      (synWsfin (synC0c) (synC1c)) p0037 p0045
  have p0047 :=
    @gSyl (synWsfin (synC0c) (.cv n)) (.classEq (.cv n) (synC1c))
      (synWsfin (synC0c) (synCtfin (.cv n))) p0039 p0046
  have p0048 := Nominal.gen p0047 n
  have p0049 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin
      (synCplc (.cv m) (synC1c)) (.cv n) a dv_cache_0010 dv_cache_0011
  have p0050 :=
    @gSimp3bi (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
          (.classMem (synCpw (.cv a)) (.cv n))))
      p0049
  have p0051 :=
    @gN3ad2ant3 (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (.classMem (.cv m) (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
          (.classMem (synCpw (.cv a)) (.cv n))))
      (.all p (.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
      p0050
  have p0052 := @gSfindbl (.cv a) q (.cv m) dv_cache_0012
  have p0053 :=
    @gN3ad2antl1 (.classMem (.cv m) (synCnnc))
      (.all p (.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
      (synWrex q (synCnnc) (synWa (synWsfin (.cv m) (.cv q))
          (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))
      (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)) p0052
  have p0054 := @gSfineq2 (.cv p) (.cv q) (.cv m)
  have p0055 := @gTfineq (.cv p) (.cv q)
  have p0056 := @gSfineq2 (synCtfin (.cv p)) (synCtfin (.cv q)) (synCtfin (.cv m))
  have p0057_e00_recanon :
    Nominal.NPrf (.imp (.objEq p q) (.classEq (synCtfin (.cv p)) (synCtfin (.cv q)))) :=
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
      p0055
  have p0057 :=
    @gSyl (.objEq p q) (.classEq (synCtfin (.cv p)) (synCtfin (.cv q)))
      (synWb (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      p0057_e00_recanon p0056
  have p0058_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p q) (synWb (synWsfin (.cv m) (.cv p)) (synWsfin (.cv m) (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsfin synW3a synWa synCnnc synCint synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0054
  have p0058 :=
    @gImbi12d (.objEq p q) (synWsfin (.cv m) (.cv p)) (synWsfin (.cv m) (.cv q))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))) p0058_e00_recanon p0057
  have p0059 :=
    @gSpv
      (.imp (synWsfin (.cv m) (.cv p)) (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p))))
      (.imp (synWsfin (.cv m) (.cv q)) (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      p q dv_cache_0013 p0058
  have p0060 :=
    @gSimprrl (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (.classMem (.cv q) (synCnnc)) (synWsfin (.cv m) (.cv q))
      (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))
  have p0061 :=
    @gAdantl
      (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
        (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
            (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q))))))
      (synWsfin (.cv m) (.cv q)) (.classMem (.cv m) (synCnnc)) p0060
  have p0062 :=
    @gSimplrl (.classMem (.cv m) (synCnnc))
      (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
          (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
  have p0063 :=
    @gSimprrr (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (.classMem (.cv q) (synCnnc)) (synWsfin (.cv m) (.cv q))
      (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))
  have p0064 :=
    @gAd2antlr
      (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
        (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
            (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q))))))
      (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))
      (.classMem (.cv m) (synCnnc)) (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      p0063
  have p0065 := @gSfin112 (synCplc (.cv q) (.cv q)) (synCplc (.cv m) (synC1c)) (.cv n)
  have p0066 :=
    @gSyl2anc
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))
      (.classEq (.cv n) (synCplc (.cv q) (.cv q))) p0062 p0064 p0065
  have p0067 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin
      (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)) a dv_cache_0010
      dv_cache_0014
  have p0068 :=
    @gSimp3bi (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      (.classMem (synCplc (.cv q) (.cv q)) (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
          (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q)))))
      p0067
  have p0069 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
          (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q)))))
      p0064 p0068
  have p0070 :=
    @gSimp2
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
  have p0071 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin
      (synCtfin (.cv m)) (synCtfin (.cv q)) a dv_cache_0015 dv_cache_0016
  have p0072 :=
    @gSimp1bi (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (.classMem (synCtfin (.cv m)) (synCnnc))
      (.classMem (synCtfin (.cv q)) (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCtfin (.cv m)))
          (.classMem (synCpw (.cv a)) (synCtfin (.cv q)))))
      p0071
  have p0073 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
        (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (.classMem (synCtfin (.cv m)) (synCnnc)) p0070 p0072
  have p0074 :=
    @gSimp1l (.classMem (.cv m) (synCnnc))
      (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
        (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
            (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q))))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
  have p0075 := @gPeano2 (.cv m)
  have p0076 :=
    @gSyl
      (synW3a (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
        (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))))
      (.classMem (.cv m) (synCnnc)) (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      p0074 p0075
  have p0077 :=
    @gSimp3
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
  have p0078 := @gTfinpw1 (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))
  have p0079 :=
    @gSyl2anc
      (synW3a (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
        (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
      (.classMem (synCpw1 (synCpw1 (.cv a))) (synCtfin (synCplc (.cv m) (synC1c))))
      p0076 p0077 p0078
  have p0080 := @gNe0i (synCplc (.cv m) (synC1c)) (synCpw1 (.cv a))
  have p0081 :=
    @gN3ad2ant3 (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))) p0080
  have p0082 := @gTfinsuc (.cv m)
  have p0083 :=
    @gSyl2anc
      (synW3a (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
        (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))))
      (.classMem (.cv m) (synCnnc)) (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (.classEq (synCtfin (synCplc (.cv m) (synC1c)))
        (synCplc (synCtfin (.cv m)) (synC1c)))
      p0074 p0081 p0082
  have p0084 :=
    @gEleqtrd
      (synW3a (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
        (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))))
      (synCpw1 (synCpw1 (.cv a))) (synCtfin (synCplc (.cv m) (synC1c)))
      (synCplc (synCtfin (.cv m)) (synC1c)) p0079 p0083
  have p0085 := @gSfindbl (synCpw1 (.cv a)) k (synCtfin (.cv m)) dv_cache_0017
  have p0086 :=
    @gSyl2anc
      (synW3a (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
        (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))))
      (.classMem (synCtfin (.cv m)) (synCnnc))
      (.classMem (synCpw1 (synCpw1 (.cv a))) (synCplc (synCtfin (.cv m)) (synC1c)))
      (synWrex k (synCnnc) (synWa (synWsfin (synCtfin (.cv m)) (.cv k))
          (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k)))))
      p0073 p0084 p0085
  have p0087 :=
    @gSimp2
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (synWa (synWsfin (synCtfin (.cv m)) (.cv k))
        (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k))))
  have p0088 :=
    @gSimp3l
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (synWsfin (synCtfin (.cv m)) (.cv k))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k)))
  have p0089 := @gSfin112 (.cv k) (synCtfin (.cv m)) (synCtfin (.cv q))
  have p0090 :=
    @gSyl2anc
      (synW3a (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
        (synWa (synWsfin (synCtfin (.cv m)) (.cv k))
          (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k)))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (synWsfin (synCtfin (.cv m)) (.cv k)) (.classEq (synCtfin (.cv q)) (.cv k)) p0087
      p0088 p0089
  have p0091 := @gAddceq12 (synCtfin (.cv q)) (synCtfin (.cv q)) (.cv k) (.cv k)
  have p0092 :=
    @gAnidms (.classEq (synCtfin (.cv q)) (.cv k))
      (.classEq (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))) (synCplc (.cv k) (.cv k)))
      p0091
  have p0093 :=
    @gSfineq2 (synCplc (synCtfin (.cv q)) (synCtfin (.cv q)))
      (synCplc (.cv k) (.cv k)) (synCplc (synCtfin (.cv m)) (synC1c))
  have p0094 :=
    @gSyl (.classEq (synCtfin (.cv q)) (.cv k))
      (.classEq (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))) (synCplc (.cv k) (.cv k)))
      (synWb (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
          (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
        (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k))))
      p0092 p0093
  have p0095 :=
    @gBiimprcd (.classEq (synCtfin (.cv q)) (.cv k))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k)))
      p0094
  have p0096 :=
    @gAdantl
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k)))
      (.imp (.classEq (synCtfin (.cv q)) (.cv k))
        (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
          (synCplc (synCtfin (.cv q)) (synCtfin (.cv q)))))
      (synWsfin (synCtfin (.cv m)) (.cv k)) p0095
  have p0097 :=
    @gN3ad2ant3
      (synWa (synWsfin (synCtfin (.cv m)) (.cv k))
        (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k))))
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (.imp (.classEq (synCtfin (.cv q)) (.cv k))
        (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
          (synCplc (synCtfin (.cv q)) (synCtfin (.cv q)))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))) p0096
  have p0098 :=
    @gMpd
      (synW3a (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
        (synWa (synWsfin (synCtfin (.cv m)) (.cv k))
          (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k)))))
      (.classEq (synCtfin (.cv q)) (.cv k))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      p0090 p0097
  have p0099 :=
    @gN3expia
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (synWa (synWsfin (synCtfin (.cv m)) (.cv k))
        (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k))))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      p0098
  have p0100 :=
    @gRexlimdvw
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (synWa (synWsfin (synCtfin (.cv m)) (.cv k))
        (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k))))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      k (synCnnc) dv_cache_0018 dv_cache_0019 p0099
  have p0101 :=
    @gN3adant3
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (.imp (synWrex k (synCnnc) (synWa (synWsfin (synCtfin (.cv m)) (.cv k))
            (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k)))))
        (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
          (synCplc (synCtfin (.cv q)) (synCtfin (.cv q)))))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))) p0100
  have p0102 :=
    @gMpd
      (synW3a (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
        (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))))
      (synWrex k (synCnnc) (synWa (synWsfin (synCtfin (.cv m)) (.cv k))
          (synWsfin (synCplc (synCtfin (.cv m)) (synC1c)) (synCplc (.cv k) (.cv k)))))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      p0086 p0101
  have p0103 :=
    @gN3expia
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      p0102
  have p0104 :=
    @gAdantrd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q))) p0103
  have p0105 :=
    @gExlimdv
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
        (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q))))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      a dv_cache_0020 dv_cache_0021 p0104
  have p0106 :=
    @gMpd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
          (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q)))))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      p0069 p0105
  have p0107 :=
    @gSimpll (.classMem (.cv m) (synCnnc))
      (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
        (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
            (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q))))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
  have p0108 :=
    @gAdantr (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
      (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q))) p0080
  have p0109 :=
    @gExlimiv
      (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
        (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q))))
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) a dv_cache_0022 p0108
  have p0110 :=
    @gN3syl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
          (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q)))))
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) p0064 p0068 p0109
  have p0111 :=
    @gSyl2anc
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (.classMem (.cv m) (synCnnc)) (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (.classEq (synCtfin (synCplc (.cv m) (synC1c)))
        (synCplc (synCtfin (.cv m)) (synC1c)))
      p0107 p0110 p0082
  have p0112 :=
    @gSimprrl (.classMem (.cv m) (synCnnc))
      (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)) (.classMem (.cv q) (synCnnc))
      (synWa (synWsfin (.cv m) (.cv q))
        (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q))))
  have p0113 :=
    @gAdantr
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (.classMem (.cv q) (synCnnc)) (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      p0112
  have p0114 := @gNe0i (synCplc (.cv q) (.cv q)) (synCpw (.cv a))
  have p0115 :=
    @gAdantl (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q)))
      (synWne (synCplc (.cv q) (.cv q)) (synC0))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))) p0114
  have p0116 :=
    @gExlimiv
      (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
        (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q))))
      (synWne (synCplc (.cv q) (.cv q)) (synC0)) a dv_cache_0023 p0115
  have p0117 :=
    @gN3syl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
          (.classMem (synCpw (.cv a)) (synCplc (.cv q) (.cv q)))))
      (synWne (synCplc (.cv q) (.cv q)) (synC0)) p0064 p0068 p0116
  have p0118 := @gTfindi (.cv q) (.cv q)
  have p0119 :=
    @gSyl3anc
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (.classMem (.cv q) (synCnnc)) (.classMem (.cv q) (synCnnc))
      (synWne (synCplc (.cv q) (.cv q)) (synC0))
      (.classEq (synCtfin (synCplc (.cv q) (.cv q)))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      p0113 p0113 p0117 p0118
  have p0120 :=
    @gSfineq1 (synCtfin (synCplc (.cv m) (synC1c)))
      (synCplc (synCtfin (.cv m)) (synC1c)) (synCtfin (synCplc (.cv q) (.cv q)))
  have p0121 :=
    @gSfineq2 (synCtfin (synCplc (.cv q) (.cv q)))
      (synCplc (synCtfin (.cv q)) (synCtfin (.cv q)))
      (synCplc (synCtfin (.cv m)) (synC1c))
  have p0122 :=
    @gSylan9bb
      (.classEq (synCtfin (synCplc (.cv m) (synC1c)))
        (synCplc (synCtfin (.cv m)) (synC1c)))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c)))
        (synCtfin (synCplc (.cv q) (.cv q))))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCtfin (synCplc (.cv q) (.cv q))))
      (.classEq (synCtfin (synCplc (.cv q) (.cv q)))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      p0120 p0121
  have p0123 :=
    @gSyl2anc
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (.classEq (synCtfin (synCplc (.cv m) (synC1c)))
        (synCplc (synCtfin (.cv m)) (synC1c)))
      (.classEq (synCtfin (synCplc (.cv q) (.cv q)))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      (synWb (synWsfin (synCtfin (synCplc (.cv m) (synC1c)))
          (synCtfin (synCplc (.cv q) (.cv q))))
        (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
          (synCplc (synCtfin (.cv q)) (synCtfin (.cv q)))))
      p0111 p0119 p0122
  have p0124 :=
    @gMpbird
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c)))
        (synCtfin (synCplc (.cv q) (.cv q))))
      (synWsfin (synCplc (synCtfin (.cv m)) (synC1c))
        (synCplc (synCtfin (.cv q)) (synCtfin (.cv q))))
      p0106 p0123
  have p0125 := @gTfineq (.cv n) (synCplc (.cv q) (.cv q))
  have p0126 :=
    @gSfineq2 (synCtfin (.cv n)) (synCtfin (synCplc (.cv q) (.cv q)))
      (synCtfin (synCplc (.cv m) (synC1c)))
  have p0127 :=
    @gSyl (.classEq (.cv n) (synCplc (.cv q) (.cv q)))
      (.classEq (synCtfin (.cv n)) (synCtfin (synCplc (.cv q) (.cv q))))
      (synWb (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n)))
        (synWsfin (synCtfin (synCplc (.cv m) (synC1c)))
          (synCtfin (synCplc (.cv q) (.cv q)))))
      p0125 p0126
  have p0128 :=
    @gBiimprcd (.classEq (.cv n) (synCplc (.cv q) (.cv q)))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n)))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c)))
        (synCtfin (synCplc (.cv q) (.cv q))))
      p0127
  have p0129 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c)))
        (synCtfin (synCplc (.cv q) (.cv q))))
      (.imp (.classEq (.cv n) (synCplc (.cv q) (.cv q)))
        (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))))
      p0124 p0128
  have p0130 :=
    @gMpd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
            (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
                (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
        (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (.classEq (.cv n) (synCplc (.cv q) (.cv q)))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0066 p0129
  have p0131 :=
    @gEx
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0130
  have p0132 :=
    @gEmbantd
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWsfin (.cv m) (.cv q)) (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q)))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0061 p0131
  have p0133 :=
    @gSyl5
      (.all p (.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
      (.imp (synWsfin (.cv m) (.cv q)) (synWsfin (synCtfin (.cv m)) (synCtfin (.cv q))))
      (synWa (.classMem (.cv m) (synCnnc))
        (synWa (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
              (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0059 p0132
  have p0134 :=
    @gExp32 (.classMem (.cv m) (synCnnc))
      (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
          (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))
      (.imp (.all p (.imp (synWsfin (.cv m) (.cv p))
            (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
        (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))))
      p0133
  have p0135 :=
    @gCom34 (.classMem (.cv m) (synCnnc))
      (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
          (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))
      (.all p (.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0134
  have p0136 :=
    @gCom23 (.classMem (.cv m) (synCnnc))
      (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (.all p (.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
      (.imp (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
            (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))
        (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))))
      p0135
  have p0137 :=
    @gN3imp (.classMem (.cv m) (synCnnc))
      (.all p (.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
      (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (.imp (synWa (.classMem (.cv q) (synCnnc)) (synWa (synWsfin (.cv m) (.cv q))
            (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))
        (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))))
      p0136
  have p0138 :=
    @gExp3a
      (synW3a (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
            (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
        (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)))
      (.classMem (.cv q) (synCnnc))
      (synWa (synWsfin (.cv m) (.cv q))
        (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q))))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0137
  have p0139 :=
    @gRexlimdv
      (synW3a (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
            (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
        (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)))
      (synWa (synWsfin (.cv m) (.cv q))
        (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q))))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) q
      (synCnnc) dv_cache_0024 dv_cache_0025 p0138
  have p0140 :=
    @gAdantr
      (synW3a (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
            (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
        (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)))
      (.imp (synWrex q (synCnnc) (synWa (synWsfin (.cv m) (.cv q))
            (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))
        (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))) p0139
  have p0141 :=
    @gMpd
      (synWa (synW3a (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
              (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
          (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)))
        (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c))))
      (synWrex q (synCnnc) (synWa (synWsfin (.cv m) (.cv q))
          (synWsfin (synCplc (.cv m) (synC1c)) (synCplc (.cv q) (.cv q)))))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0053 p0140
  have p0142 :=
    @gEx
      (synW3a (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
            (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
        (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0141
  have p0143 :=
    @gAdantrd
      (synW3a (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
            (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
        (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)))
      (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n)))
      (.classMem (synCpw (.cv a)) (.cv n)) p0142
  have p0144 :=
    @gExlimdv
      (synW3a (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
            (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
        (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)))
      (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
        (.classMem (synCpw (.cv a)) (.cv n)))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) a
      dv_cache_0026 dv_cache_0027 p0143
  have p0145 :=
    @gMpd
      (synW3a (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
            (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
        (synWsfin (synCplc (.cv m) (synC1c)) (.cv n)))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCplc (.cv m) (synC1c)))
          (.classMem (synCpw (.cv a)) (.cv n))))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0051 p0144
  have p0146 :=
    @gN3expia (.classMem (.cv m) (synCnnc))
      (.all p (.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
      (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
      (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))) p0145
  have p0147 :=
    @gAlrimiv
      (synWa (.classMem (.cv m) (synCnnc)) (.all p (.imp (synWsfin (.cv m) (.cv p))
            (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p))))))
      (.imp (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
        (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n))))
      n dv_cache_0028 p0146
  have p0148 :=
    @gEx (.classMem (.cv m) (synCnnc))
      (.all p (.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
      (.all n (.imp (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n)))))
      p0147
  have p0149 :=
    @gFinds
      (.all n (.imp (synWsfin (.cv k) (.cv n))
          (synWsfin (synCtfin (.cv k)) (synCtfin (.cv n)))))
      (.all n (.imp (synWsfin (synC0c) (.cv n)) (synWsfin (synC0c) (synCtfin (.cv n)))))
      (.all p (.imp (synWsfin (.cv m) (.cv p))
          (synWsfin (synCtfin (.cv m)) (synCtfin (.cv p)))))
      (.all n (.imp (synWsfin (synCplc (.cv m) (synC1c)) (.cv n))
          (synWsfin (synCtfin (synCplc (.cv m) (synC1c))) (synCtfin (.cv n)))))
      (.all n (.imp (synWsfin M (.cv n)) (synWsfin (synCtfin M) (synCtfin (.cv n)))))
      k m M dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0035 p0003 p0011 p0024 p0030 p0036 p0048 p0148
  have p0150 := @gSfineq2 (.cv n) N M
  have p0151 := @gTfineq (.cv n) N
  have p0152 := @gSfineq2 (synCtfin (.cv n)) (synCtfin N) (synCtfin M)
  have p0153 :=
    @gSyl (.classEq (.cv n) N) (.classEq (synCtfin (.cv n)) (synCtfin N))
      (synWb (synWsfin (synCtfin M) (synCtfin (.cv n)))
        (synWsfin (synCtfin M) (synCtfin N)))
      p0151 p0152
  have p0154 :=
    @gImbi12d (.classEq (.cv n) N) (synWsfin M (.cv n)) (synWsfin M N)
      (synWsfin (synCtfin M) (synCtfin (.cv n)))
      (synWsfin (synCtfin M) (synCtfin N)) p0150 p0153
  have p0155 :=
    @gSpcgv (.imp (synWsfin M (.cv n)) (synWsfin (synCtfin M) (synCtfin (.cv n))))
      (.imp (synWsfin M N) (synWsfin (synCtfin M) (synCtfin N))) n N (synCnnc)
      dv_cache_0036 dv_cache_0037 p0154
  have p0156 :=
    @gMpan9 (.classMem M (synCnnc))
      (.all n (.imp (synWsfin M (.cv n)) (synWsfin (synCtfin M) (synCtfin (.cv n)))))
      (.classMem N (synCnnc))
      (.imp (synWsfin M N) (synWsfin (synCtfin M) (synCtfin N))) p0149 p0155
  have p0157 :=
    @gMpcom (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc))) (synWsfin M N)
      (synWsfin (synCtfin M) (synCtfin N)) p0002 p0156
  exact p0157


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part016`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_tfinnnlem1`. -/
@[expose]
noncomputable def gTfinnnlem1 (x : Var) (y : Var) (n : Var) (a : Var) (_dv_a_n : a ≠ n)
    (dv_a_x : a ≠ x) (dv_a_y : a ≠ y) (_dv_n_x : n ≠ x) (dv_n_y : n ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classMem (.cab n (synWral y (.cv n) (.imp (synWss (.cv y) (synCnnc)) (.classMem
                (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
                (synCtfin (.cv n)))))) (synCvv)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ ({ n } : Finset Var) ∪
      ({ a } : Finset Var)
  let t : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_t_ne_a : t ≠ a := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_t : a ≠ t := Ne.symm fresh_t_ne_a
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
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
  have fresh_z_ne_n : z ≠ n := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_z_ne_a : z ≠ a := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
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
  have fresh_w_ne_a : w ≠ a := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_w : a ≠ w := Ne.symm fresh_w_ne_a
  have fresh_t_ne_z : t ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have fresh_t_ne_w : t ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_t : w ≠ t := Ne.symm fresh_t_ne_w
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have dv_cache_0001 : t ∉ ((synCsn (synCsn (.cv y)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
          not_false_eq_true])
  have dv_cache_0002 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n)))
          (synCin (synCsik (synCssetk))
            (synCdif (synCsik (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv))) (synCimak
                (synCin (synCins2k (synCcnvk
                      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                        (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCimak
                                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                        (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik
                                      (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
        (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
        (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
        (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif
        (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin (synCins2k
        (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif (synCins3k
        (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1
        (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk))) (synCpw1 (synC1c)))))
        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                                        (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c))))))).fv :=
    by
    clear dv_cache_0001
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((synCsn (synCsn (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
          not_false_eq_true])
  have dv_cache_0004 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv z)))
            (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n)))) (synCin (synCins2k
              (synCcnvk (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                  (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCimak (synCdif (synCins3k (synCcnvk (synCssetk)))
                                (synCins2k (synCimak (synCsymdif (synCins2k
                                        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                      (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                              (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k (synCimak
                (synCin (synCins2k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik
                                (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                      (synCun (synCxpk (synCsn (synCsn (synC0)))
        (synCsn (synC0))) (synCdif (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak (synCdif (synCins3k
        (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif (synCins2k (synCin
        (synCxpk (synCnnc) (synCvv)) (synCimak (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw
        (synC1c)) (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCins3k (synCidk))) (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                                  (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_y, fresh_t_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
    t ∉
      ((synCin (synCins2k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCimak
                          (synCin (synCins2k (synCssetk)) (synCins3k (synCun
                                (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                                (synCdif (synCcompl (synCimak
                                      (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
        (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                          (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCssetk)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0007 : t ∉ ((synCopk (.cv z) (synCsn (synCsn (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_y, or_false, not_false_eq_true])
  have dv_cache_0008 : w ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_t, not_false_eq_true])
  have dv_cache_0009 :
    w ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv z) (synCsn (synCsn (.cv y))))) (synCin
            (synCins2k (synCsik (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                      (synCins2k (synCsik (synCimak (synCin (synCins2k (synCssetk))
                              (synCins3k (synCun (synCxpk (synCsn (synCsn (synC0)))
                                    (synCsn (synC0))) (synCdif (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
        (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                            (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_t, fresh_w_ne_z, fresh_w_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((synCsn (synCsn (synCsn (.cv w))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_w,
          not_false_eq_true])
  have dv_cache_0011 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv w))))
            (synCopk (.cv z) (synCsn (synCsn (.cv y))))) (synCin (synCins2k (synCsik
                (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                        (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                (synCun (synCxpk (synCsn (synCsn (synC0)))
                                    (synCsn (synC0))) (synCdif (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCimak (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak
        (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                            (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_z, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 :
    t ∉
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCimak
                (synCin (synCins2k (synCssetk)) (synCins3k
                    (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                      (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCimak
                                  (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                      (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
                                        (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
                            (synCpw1 (synCpw1 (synC1c)))))
                        (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 : t ∉ ((synCopk (.cv w) (synCsn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_y, or_false, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((Class.cv t)).fv :=
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
          fresh_a_ne_t, not_false_eq_true])
  have dv_cache_0015 :
    a ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv w) (synCsn (.cv y))))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCimak
                  (synCin (synCins2k (synCssetk)) (synCins3k
                      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                        (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCimak
                                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                        (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                  (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_t, fresh_a_ne_w, dv_a_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((synCsn (synCsn (synCsn (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_a,
          not_false_eq_true])
  have dv_cache_0017 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv a))))
            (synCopk (.cv w) (synCsn (.cv y)))) (synCsymdif (synCins3k (synCssetk))
            (synCins2k (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                        (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCimak
                                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                        (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                  (synCpw1 (synCpw1 (synC1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_w, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 :
    t ∉
      ((synCin (synCins2k (synCssetk)) (synCins3k
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
                (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : t ∉ ((synCopk (.cv a) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_y, or_false, not_false_eq_true])
  have dv_cache_0020 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0021 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv a) (.cv y)))
          (synCin (synCins2k (synCssetk)) (synCins3k
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
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, (Ne.symm dv_a_x), dv_x_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : t ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0023 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv a) (.cv y)))
          (synCin (synCins2k (synCssetk)) (synCins3k
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
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_a, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 : a ∉ ((Class.cv w)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_w, not_false_eq_true])
  have dv_cache_0025 :
    w ∉ ((Class.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_a,
          fresh_w_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0026 : w ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_z, not_false_eq_true])
  have dv_cache_0027 :
    t ∉
      ((synCin (synCins2k (synCcnvk
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
                  (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k (synCimak
              (synCin (synCins2k (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCimak
                                (synCin (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                                      (synCdif (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak (synCdif
        (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin (synCins2k (synCsik
        (synCssetk))) (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk
        (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCins3k (synCidk))) (synCpw1 (synC1c)))))
        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                                (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0028 : t ∉ ((synCpw1 (synC1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0029 :
    t ∉ ((synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_n, or_false, not_false_eq_true])
  have dv_cache_0030 : z ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0031 :
    z ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n))))
          (synCin (synCins2k (synCcnvk
                (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                    (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                            (synCimak (synCdif (synCins3k (synCcnvk (synCssetk)))
                                (synCins2k (synCimak (synCsymdif (synCins2k
                                        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak
        (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                      (synCins3k (synCidk))) (synCpw1 (synC1c)))))
                              (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k (synCimak
                (synCin (synCins2k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik
                                (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                      (synCun (synCxpk (synCsn (synCsn (synC0)))
        (synCsn (synC0))) (synCdif (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak (synCdif (synCins3k
        (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif (synCins2k (synCin
        (synCxpk (synCnnc) (synCvv)) (synCimak (synCin (synCins2k (synCsik (synCssetk)))
        (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk (synCpw
        (synC1c)) (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
        (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCins3k (synCidk))) (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                                  (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_y, fresh_z_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0032 :
    z ∉ ((Class.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_a,
          fresh_z_ne_x, or_false, and_false, not_false_eq_true])
  have dv_cache_0033 : z ∉ ((synCtfin (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_n,
          not_false_eq_true])
  have dv_cache_0034 :
    t ∉
      ((synCin (synCsik (synCssetk))
          (synCdif (synCsik (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv))) (synCimak
              (synCin (synCins2k (synCcnvk
                    (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                      (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCimak
                                  (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                      (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
                                        (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
                            (synCpw1 (synCpw1 (synC1c)))))
                        (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                  (synCimak (synCin (synCins2k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik
                                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
        (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
        (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
        (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif
        (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin (synCins2k
        (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif (synCins3k
        (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1
        (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk))) (synCpw1 (synC1c)))))
        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0035 : t ∉ ((synCsn (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_n,
          not_false_eq_true])
  have dv_cache_0036 : y ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0037 :
    y ∉
      ((Wff.classMem (synCopk (.cv t) (synCsn (.cv n))) (synCin (synCsik (synCssetk))
            (synCdif (synCsik (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv))) (synCimak
                (synCin (synCins2k (synCcnvk
                      (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0)))
                        (synCdif (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCimak
                                    (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k
                                        (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin
        (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k
        (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif
        (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1
        (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk)))
        (synCpw1 (synC1c))))) (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik
                                      (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
        (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
        (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak
        (synCdif (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif
        (synCins2k (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin (synCins2k
        (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif
        (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif (synCins3k
        (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1
        (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCidk))) (synCpw1 (synC1c)))))
        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
                                        (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c))))))) (synCins3k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c))))))).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, (Ne.symm dv_n_y), compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0038 :
    n ∉
      ((synCuni1 (synCcompl (synCimak (synCin (synCsik (synCssetk))
                (synCdif (synCsik (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv)))
                  (synCimak (synCin (synCins2k (synCcnvk (synCun
                            (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif
                              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCimak
                                        (synCdif (synCins3k (synCcnvk (synCssetk)))
        (synCins2k (synCimak (synCsymdif (synCins2k (synCin (synCxpk (synCnnc) (synCvv))
        (synCimak (synCin (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
        (synCins3k (synCsik (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk)))) (synCpw1
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCins3k (synCidk))) (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCsn (synCsn (synC0))) (synCvv)))))) (synCins3k
                        (synCimak (synCin (synCins2k (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik
        (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCun
        (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) (synCdif (synCcompl
        (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCimak (synCdif
        (synCins3k (synCcnvk (synCssetk))) (synCins2k (synCimak (synCsymdif (synCins2k
        (synCin (synCxpk (synCnnc) (synCvv)) (synCimak (synCin (synCins2k (synCsik
        (synCssetk))) (synCins3k (synCimak (synCin (synCins3k (synCsik (synCdif (synCxpk
        (synCpw (synC1c)) (synCvv)) (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCins3k (synCidk))) (synCpw1 (synC1c)))))
        (synCpw1 (synC1c))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCsn (synCsn (synC0))) (synCvv))))))
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synC1c))))) (synCpw1 (synC1c)))))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cuni1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  let syntaxClass0000 : Class :=
    (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxClass0001 : Class :=
    (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) syntaxClass0000)
  let syntaxClass0002 : Class := (synCsik syntaxClass0001)
  let syntaxClass0003 : Class := (synCins3k syntaxClass0002)
  let syntaxClass0004 : Class := (synCin syntaxClass0003 (synCins2k (synCssetk)))
  let syntaxClass0005 : Class :=
    (synCimak syntaxClass0004 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0006 : Class := (synCins3k syntaxClass0005)
  let syntaxClass0007 : Class :=
    (synCin (synCins2k (synCsik (synCssetk))) syntaxClass0006)
  let syntaxClass0008 : Class :=
    (synCimak syntaxClass0007 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  let syntaxClass0009 : Class := (synCin (synCxpk (synCnnc) (synCvv)) syntaxClass0008)
  let syntaxClass0010 : Class := (synCins2k syntaxClass0009)
  let syntaxClass0011 : Class := (synCsymdif syntaxClass0010 (synCins3k (synCidk)))
  let syntaxClass0012 : Class := (synCimak syntaxClass0011 (synCpw1 (synC1c)))
  let syntaxClass0013 : Class := (synCins2k syntaxClass0012)
  let syntaxClass0014 : Class :=
    (synCdif (synCins3k (synCcnvk (synCssetk))) syntaxClass0013)
  let syntaxClass0015 : Class := (synCimak syntaxClass0014 (synCpw1 (synC1c)))
  let syntaxClass0016 : Class := (synCins3k syntaxClass0015)
  let syntaxClass0017 : Class := (synCsymdif (synCins2k (synCssetk)) syntaxClass0016)
  let syntaxClass0018 : Class :=
    (synCimak syntaxClass0017 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0019 : Class := (synCcompl syntaxClass0018)
  let syntaxClass0020 : Class :=
    (synCdif syntaxClass0019 (synCxpk (synCsn (synCsn (synC0))) (synCvv)))
  let syntaxClass0021 : Class :=
    (synCun (synCxpk (synCsn (synCsn (synC0))) (synCsn (synC0))) syntaxClass0020)
  let syntaxClass0022 : Class := (synCcnvk syntaxClass0021)
  let syntaxClass0023 : Class := (synCins2k syntaxClass0022)
  let syntaxClass0024 : Class := (synCins3k syntaxClass0021)
  let syntaxClass0025 : Class := (synCin (synCins2k (synCssetk)) syntaxClass0024)
  let syntaxClass0026 : Class :=
    (synCimak syntaxClass0025 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0027 : Class := (synCsik syntaxClass0026)
  let syntaxClass0028 : Class := (synCins2k syntaxClass0027)
  let syntaxClass0029 : Class := (synCsymdif (synCins3k (synCssetk)) syntaxClass0028)
  let syntaxClass0030 : Class :=
    (synCimak syntaxClass0029 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0031 : Class := (synCcompl syntaxClass0030)
  let syntaxClass0032 : Class := (synCsik syntaxClass0031)
  let syntaxClass0033 : Class := (synCins2k syntaxClass0032)
  let syntaxClass0034 : Class := (synCin syntaxClass0033 (synCins3k (synCssetk)))
  let syntaxClass0035 : Class :=
    (synCimak syntaxClass0034 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0036 : Class := (synCins3k syntaxClass0035)
  let syntaxClass0037 : Class := (synCin syntaxClass0023 syntaxClass0036)
  let syntaxClass0038 : Class := (synCimak syntaxClass0037 (synCpw1 (synC1c)))
  let syntaxClass0039 : Class :=
    (synCdif (synCsik (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv))) syntaxClass0038)
  let syntaxClass0040 : Class := (synCin (synCsik (synCssetk)) syntaxClass0039)
  let syntaxClass0041 : Class := (synCimak syntaxClass0040 (synCpw1 (synC1c)))
  let syntaxClass0042 : Class := (synCcompl syntaxClass0041)
  let syntaxFormula0043 : Wff :=
    (.classMem (synCopk (.cv t) (synCsn (.cv n))) syntaxClass0040)
  let syntaxFormula0044 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n))) syntaxClass0040)
  let syntaxFormula0045 : Wff :=
    (.classMem (synCopk (synCsn (.cv y)) (.cv n))
      (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv)))
  let syntaxFormula0046 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n)))
      (synCsik (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv))))
  let syntaxClass0047 : Class :=
    (synCopk (synCsn (synCsn (.cv z)))
      (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n))))
  let syntaxFormula0048 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n))))
      syntaxClass0037)
  let syntaxFormula0049 : Wff := (.classMem syntaxClass0047 syntaxClass0037)
  let syntaxFormula0050 : Wff := (.classMem syntaxClass0047 syntaxClass0023)
  let syntaxFormula0051 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv z) (synCsn (synCsn (.cv y)))))
      syntaxClass0034)
  let syntaxFormula0052 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0051)
  let syntaxFormula0053 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv w))))) syntaxFormula0051)
  let syntaxFormula0054 : Wff := (synWex w syntaxFormula0053)
  let syntaxFormula0055 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0051)
  let syntaxFormula0056 : Wff := (synWex t syntaxFormula0053)
  let syntaxFormula0057 : Wff := (synWex w syntaxFormula0056)
  let syntaxClass0058 : Class :=
    (synCopk (synCsn (synCsn (synCsn (.cv w))))
      (synCopk (.cv z) (synCsn (synCsn (.cv y)))))
  let syntaxFormula0059 : Wff := (.classMem syntaxClass0058 syntaxClass0034)
  let syntaxFormula0060 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv w) (synCsn (.cv y)))) syntaxClass0029)
  let syntaxFormula0061 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0060)
  let syntaxFormula0062 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))) syntaxFormula0060)
  let syntaxFormula0063 : Wff := (synWex a syntaxFormula0062)
  let syntaxFormula0064 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0060)
  let syntaxFormula0065 : Wff := (synWex t syntaxFormula0062)
  let syntaxFormula0066 : Wff := (synWex a syntaxFormula0065)
  let syntaxClass0067 : Class :=
    (synCopk (synCsn (synCsn (synCsn (.cv a)))) (synCopk (.cv w) (synCsn (.cv y))))
  let syntaxFormula0068 : Wff := (.classMem syntaxClass0067 syntaxClass0029)
  let syntaxFormula0069 : Wff := (.classMem syntaxClass0067 (synCins3k (synCssetk)))
  let syntaxFormula0070 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv a) (.cv y))) syntaxClass0025)
  let syntaxFormula0071 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0070)
  let syntaxFormula0072 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0070)
  let syntaxFormula0073 : Wff := (synWex x syntaxFormula0072)
  let syntaxFormula0074 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0070)
  let syntaxFormula0075 : Wff := (synWex t syntaxFormula0072)
  let syntaxFormula0076 : Wff := (synWex x syntaxFormula0075)
  let syntaxFormula0077 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv a) (.cv y)))
      syntaxClass0025)
  let syntaxFormula0078 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv a) (.cv y)))
      (synCins2k (synCssetk)))
  let syntaxFormula0079 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv a) (.cv y)))
      syntaxClass0024)
  let syntaxFormula0080 : Wff := (.classMem (synCopk (.cv a) (.cv y)) syntaxClass0026)
  let syntaxFormula0081 : Wff :=
    (.classMem (synCopk (synCsn (.cv a)) (synCsn (.cv y))) syntaxClass0027)
  let syntaxFormula0082 : Wff := (.classMem syntaxClass0067 syntaxClass0028)
  let syntaxFormula0083 : Wff := (synWb syntaxFormula0069 syntaxFormula0082)
  let syntaxFormula0084 : Wff :=
    (.classMem (synCopk (.cv w) (synCsn (.cv y))) syntaxClass0030)
  let syntaxFormula0085 : Wff :=
    (.classEq (.cv w) (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))))
  let syntaxFormula0086 : Wff :=
    (.classMem (synCopk (.cv w) (synCsn (.cv y))) syntaxClass0031)
  let syntaxFormula0087 : Wff := (.classMem syntaxClass0058 syntaxClass0033)
  let syntaxFormula0088 : Wff := (.classMem syntaxClass0058 (synCins3k (synCssetk)))
  let syntaxFormula0089 : Wff :=
    (.classMem (synCopk (.cv z) (synCsn (synCsn (.cv y)))) syntaxClass0035)
  let syntaxFormula0090 : Wff :=
    (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) (.cv z))
  let syntaxFormula0091 : Wff := (.classMem syntaxClass0047 syntaxClass0036)
  let syntaxFormula0092 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z)))) syntaxFormula0048)
  let syntaxFormula0093 : Wff := (synWex t syntaxFormula0092)
  let syntaxFormula0094 : Wff :=
    (synWa (.classEq (.cv z) (synCtfin (.cv n))) syntaxFormula0090)
  let syntaxFormula0095 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0048)
  let syntaxFormula0096 : Wff := (synWex z syntaxFormula0092)
  let syntaxFormula0097 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0048)
  let syntaxFormula0098 : Wff := (synWex z syntaxFormula0093)
  let syntaxFormula0099 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n))) syntaxClass0038)
  let syntaxFormula0100 : Wff :=
    (.classMem (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCtfin (.cv n)))
  let syntaxFormula0101 : Wff := (.neg syntaxFormula0099)
  let syntaxFormula0102 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n))) syntaxClass0039)
  let syntaxFormula0103 : Wff := (.imp (synWss (.cv y) (synCnnc)) syntaxFormula0100)
  let syntaxFormula0104 : Wff := (.neg syntaxFormula0103)
  let syntaxFormula0105 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv y)))) syntaxFormula0043)
  let syntaxFormula0106 : Wff := (synWex t syntaxFormula0105)
  let syntaxFormula0107 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0043)
  let syntaxFormula0108 : Wff := (synWex y syntaxFormula0105)
  let syntaxFormula0109 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0043)
  let syntaxFormula0110 : Wff := (synWex y syntaxFormula0106)
  let syntaxFormula0111 : Wff := (.classMem (synCsn (.cv n)) syntaxClass0041)
  let syntaxFormula0112 : Wff := (synWrex y (.cv n) syntaxFormula0104)
  let syntaxFormula0113 : Wff := (.classMem (synCsn (.cv n)) syntaxClass0042)
  let syntaxFormula0114 : Wff := (synWral y (.cv n) syntaxFormula0103)
  let syntaxClass0115 : Class := (synCuni1 syntaxClass0042)
  have p0000 := @gVex n
  have p0001 := @gEluni1 (.cv n) syntaxClass0042 p0000
  have p0002 := @gSnex (synCsn (.cv y))
  have p0003 := @gOpkeq1 (.cv t) (synCsn (synCsn (.cv y))) (synCsn (.cv n))
  have p0004 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv y))))
      (synCopk (.cv t) (synCsn (.cv n)))
      (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n))) syntaxClass0040 p0003
  have p0005 :=
    @gCeqsexv syntaxFormula0043 syntaxFormula0044 t (synCsn (synCsn (.cv y)))
      dv_cache_0001 dv_cache_0002 p0002 p0004
  have p0006 :=
    @gElin (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n)))
      (synCsik (synCssetk)) syntaxClass0039
  have p0007 := @gSnex (.cv y)
  have p0008 := @gOpksnelsik (synCsn (.cv y)) (.cv n) (synCssetk) p0007 p0000
  have p0009 := @gVex y
  have p0010 := @gElssetk (.cv y) (.cv n) p0009 p0000
  have p0011_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv y)) (.cv n)) (synCssetk)) (.objMem y n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
      p0010
  have p0011 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv y)) (.cv n)) (synCssetk)) (.objMem y n) p0008
      p0011_e01_recanon
  have p0012 :=
    @gEldif (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n)))
      (synCsik (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv))) syntaxClass0038
  have p0013 :=
    @gOpksnelsik (synCsn (.cv y)) (.cv n)
      (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv)) p0007 p0000
  have p0014 :=
    @gOpkelxpk (synCsn (.cv y)) (.cv n) (synCpw1 (synCpw (synCnnc))) (synCvv) p0007
      p0000
  have p0015 :=
    @gMpbiran2 syntaxFormula0045
      (.classMem (synCsn (.cv y)) (synCpw1 (synCpw (synCnnc))))
      (.classMem (.cv n) (synCvv)) p0000 p0014
  have p0016 := @gSnelpw1 (.cv y) (synCpw (synCnnc))
  have p0017 :=
    @gBitri syntaxFormula0045
      (.classMem (synCsn (.cv y)) (synCpw1 (synCpw (synCnnc))))
      (.classMem (.cv y) (synCpw (synCnnc))) p0015 p0016
  have p0018 := @gElpw (.cv y) (synCnnc) p0009
  have p0019 :=
    @gN3bitri syntaxFormula0046 syntaxFormula0045
      (.classMem (.cv y) (synCpw (synCnnc))) (synWss (.cv y) (synCnnc)) p0013 p0017
      p0018
  have p0020 := @gSnex (synCsn (.cv z))
  have p0021 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (.cv z)))
      (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n)))
  have p0022 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv z))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n))))
      syntaxClass0047 syntaxClass0037 p0021
  have p0023 :=
    @gCeqsexv syntaxFormula0048 syntaxFormula0049 t (synCsn (synCsn (.cv z)))
      dv_cache_0003 dv_cache_0004 p0020 p0022
  have p0024 := @gElin syntaxClass0047 syntaxClass0023 syntaxClass0036
  have p0025 := @gVex z
  have p0026 := @gSnex (.cv n)
  have p0027 :=
    @gOtkelins2k (.cv z) (synCsn (synCsn (.cv y))) (synCsn (.cv n)) syntaxClass0022
      p0025 p0002 p0026
  have p0028 := @gOpkelcnvk (.cv z) (synCsn (.cv n)) syntaxClass0021 p0025 p0026
  have p0029 := @gEqtfinrelk (.cv n) (.cv z) p0000 p0025
  have p0030 :=
    @gN3bitri syntaxFormula0050
      (.classMem (synCopk (.cv z) (synCsn (.cv n))) syntaxClass0022)
      (.classMem (synCopk (synCsn (.cv n)) (.cv z)) syntaxClass0021)
      (.classEq (.cv z) (synCtfin (.cv n))) p0027 p0028 p0029
  have p0031 := @gOpkex (.cv z) (synCsn (synCsn (.cv y)))
  have p0032 :=
    @gElimak t syntaxClass0034 (synCpw1 (synCpw1 (synC1c)))
      (synCopk (.cv z) (synCsn (synCsn (.cv y)))) dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0031
  have p0033 := @gElpw121c w (.cv t) dv_cache_0008
  have p0034 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex w (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv w))))))
      syntaxFormula0051 p0033
  have p0035 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv w))))) syntaxFormula0051
      w dv_cache_0009
  have p0036 :=
    @gBitr4i syntaxFormula0052
      (synWa (synWex w (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv w))))))
        syntaxFormula0051)
      syntaxFormula0054 p0034 p0035
  have p0037 := @gExbii syntaxFormula0052 syntaxFormula0054 t p0036
  have p0038 := (Nominal.biimpRefl syntaxFormula0055)
  have p0039 := @gExcom syntaxFormula0053 w t
  have p0040 :=
    @gN3bitr4i (synWex t syntaxFormula0052) (synWex t syntaxFormula0054)
      syntaxFormula0055 syntaxFormula0057 p0037 p0038 p0039
  have p0041 := @gSnex (synCsn (synCsn (.cv w)))
  have p0042 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv w))))
      (synCopk (.cv z) (synCsn (synCsn (.cv y))))
  have p0043 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv w)))))
      (synCopk (.cv t) (synCopk (.cv z) (synCsn (synCsn (.cv y))))) syntaxClass0058
      syntaxClass0034 p0042
  have p0044 :=
    @gCeqsexv syntaxFormula0051 syntaxFormula0059 t (synCsn (synCsn (synCsn (.cv w))))
      dv_cache_0010 dv_cache_0011 p0041 p0043
  have p0045 := @gElin syntaxClass0058 syntaxClass0033 (synCins3k (synCssetk))
  have p0046 := @gSnex (.cv w)
  have p0047 :=
    @gOtkelins2k (synCsn (.cv w)) (.cv z) (synCsn (synCsn (.cv y))) syntaxClass0032
      p0046 p0025 p0002
  have p0048 := @gVex w
  have p0049 := @gOpksnelsik (.cv w) (synCsn (.cv y)) syntaxClass0031 p0048 p0007
  have p0050 := @gOpkex (.cv w) (synCsn (.cv y))
  have p0051 :=
    @gElimak t syntaxClass0029 (synCpw1 (synCpw1 (synC1c)))
      (synCopk (.cv w) (synCsn (.cv y))) dv_cache_0012 dv_cache_0006 dv_cache_0013 p0050
  have p0052 := @gElpw121c a (.cv t) dv_cache_0014
  have p0053 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex a (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))))
      syntaxFormula0060 p0052
  have p0054 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))) syntaxFormula0060
      a dv_cache_0015
  have p0055 :=
    @gBitr4i syntaxFormula0061
      (synWa (synWex a (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))))
        syntaxFormula0060)
      syntaxFormula0063 p0053 p0054
  have p0056 := @gExbii syntaxFormula0061 syntaxFormula0063 t p0055
  have p0057 := (Nominal.biimpRefl syntaxFormula0064)
  have p0058 := @gExcom syntaxFormula0062 a t
  have p0059 :=
    @gN3bitr4i (synWex t syntaxFormula0061) (synWex t syntaxFormula0063)
      syntaxFormula0064 syntaxFormula0066 p0056 p0057 p0058
  have p0060 := @gSnex (synCsn (synCsn (.cv a)))
  have p0061 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv a))))
      (synCopk (.cv w) (synCsn (.cv y)))
  have p0062 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a)))))
      (synCopk (.cv t) (synCopk (.cv w) (synCsn (.cv y)))) syntaxClass0067
      syntaxClass0029 p0061
  have p0063 :=
    @gCeqsexv syntaxFormula0060 syntaxFormula0068 t (synCsn (synCsn (synCsn (.cv a))))
      dv_cache_0016 dv_cache_0017 p0060 p0062
  have p0064 := @gElsymdif syntaxClass0067 (synCins3k (synCssetk)) syntaxClass0028
  have p0065 := @gSnex (.cv a)
  have p0066 :=
    @gOtkelins3k (synCsn (.cv a)) (.cv w) (synCsn (.cv y)) (synCssetk) p0065 p0048
      p0007
  have p0067 := @gVex a
  have p0068 := @gElssetk (.cv a) (.cv w) p0067 p0048
  have p0069_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv a)) (.cv w)) (synCssetk)) (.objMem a w)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
      p0068
  have p0069 :=
    @gBitri syntaxFormula0069
      (.classMem (synCopk (synCsn (.cv a)) (.cv w)) (synCssetk)) (.objMem a w) p0066
      p0069_e01_recanon
  have p0070 :=
    @gOtkelins2k (synCsn (.cv a)) (.cv w) (synCsn (.cv y)) syntaxClass0027 p0065 p0048
      p0007
  have p0071 := @gOpkex (.cv a) (.cv y)
  have p0072 :=
    @gElimak t syntaxClass0025 (synCpw1 (synCpw1 (synC1c))) (synCopk (.cv a) (.cv y))
      dv_cache_0018 dv_cache_0006 dv_cache_0019 p0071
  have p0073 := @gElpw121c x (.cv t) dv_cache_0020
  have p0074 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      syntaxFormula0070 p0073
  have p0075 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))) syntaxFormula0070
      x dv_cache_0021
  have p0076 :=
    @gBitr4i syntaxFormula0071
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        syntaxFormula0070)
      syntaxFormula0073 p0074 p0075
  have p0077 := @gExbii syntaxFormula0071 syntaxFormula0073 t p0076
  have p0078 := (Nominal.biimpRefl syntaxFormula0074)
  have p0079 := @gExcom syntaxFormula0072 x t
  have p0080 :=
    @gN3bitr4i (synWex t syntaxFormula0071) (synWex t syntaxFormula0073)
      syntaxFormula0074 syntaxFormula0076 p0077 p0078 p0079
  have p0081 := @gSnex (synCsn (synCsn (.cv x)))
  have p0082 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv a) (.cv y))
  have p0083 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk (.cv a) (.cv y)))
      (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv a) (.cv y)))
      syntaxClass0025 p0082
  have p0084 :=
    @gCeqsexv syntaxFormula0070 syntaxFormula0077 t (synCsn (synCsn (synCsn (.cv x))))
      dv_cache_0022 dv_cache_0023 p0081 p0083
  have p0085 :=
    @gElin (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk (.cv a) (.cv y)))
      (synCins2k (synCssetk)) syntaxClass0024
  have p0086 := @gSnex (.cv x)
  have p0087 :=
    @gOtkelins2k (synCsn (.cv x)) (.cv a) (.cv y) (synCssetk) p0086 p0067 p0009
  have p0088 := @gVex x
  have p0089 := @gElssetk (.cv x) (.cv y) p0088 p0009
  have p0090_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
      p0089
  have p0090 :=
    @gBitri syntaxFormula0078
      (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y) p0087
      p0090_e01_recanon
  have p0091 :=
    @gOtkelins3k (synCsn (.cv x)) (.cv a) (.cv y) syntaxClass0021 p0086 p0067 p0009
  have p0092 := @gEqtfinrelk (.cv x) (.cv a) p0088 p0067
  have p0093 :=
    @gBitri syntaxFormula0079
      (.classMem (synCopk (synCsn (.cv x)) (.cv a)) syntaxClass0021)
      (.classEq (.cv a) (synCtfin (.cv x))) p0091 p0092
  have p0094 :=
    @gAnbi12i syntaxFormula0078 (.objMem x y) syntaxFormula0079
      (.classEq (.cv a) (synCtfin (.cv x))) p0090 p0093
  have p0095 :=
    @gN3bitri syntaxFormula0075 syntaxFormula0077
      (synWa syntaxFormula0078 syntaxFormula0079)
      (synWa (.objMem x y) (.classEq (.cv a) (synCtfin (.cv x)))) p0084 p0085 p0094
  have p0096 :=
    @gExbii syntaxFormula0075
      (synWa (.objMem x y) (.classEq (.cv a) (synCtfin (.cv x)))) x p0095
  have p0097 :=
    @gN3bitri syntaxFormula0080 syntaxFormula0074 syntaxFormula0076
      (synWex x (synWa (.objMem x y) (.classEq (.cv a) (synCtfin (.cv x))))) p0072
      p0080 p0096
  have p0098 := @gOpksnelsik (.cv a) (.cv y) syntaxClass0026 p0067 p0009
  have p0099 :=
    (Nominal.biimpRefl (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
  have p0100_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))
        (synWex x (synWa (.objMem x y) (.classEq (.cv a) (synCtfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCtfin, synCif, synWo, synC0,
          synCdif, synCin, synCcompl, synCnin, synWnan, synCvv, synCio, synCuni,
          synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0099
  have p0100 :=
    @gN3bitr4i syntaxFormula0080
      (synWex x (synWa (.objMem x y) (.classEq (.cv a) (synCtfin (.cv x)))))
      syntaxFormula0081 (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))) p0097
      p0098 p0100_e02_recanon
  have p0101 :=
    @gBitri syntaxFormula0082 syntaxFormula0081
      (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))) p0070 p0100
  have p0102 :=
    @gBibi12i syntaxFormula0069 (.objMem a w) syntaxFormula0082
      (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))) p0069 p0101
  have p0103 :=
    @gNotbii syntaxFormula0083
      (synWb (.objMem a w) (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
      p0102
  have p0104 :=
    @gN3bitri syntaxFormula0065 syntaxFormula0068 (.neg syntaxFormula0083)
      (.neg (synWb (.objMem a w) (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))))
      p0063 p0064 p0103
  have p0105 :=
    @gExbii syntaxFormula0065
      (.neg (synWb (.objMem a w) (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))))
      a p0104
  have p0106 :=
    @gN3bitri syntaxFormula0084 syntaxFormula0064 syntaxFormula0066
      (synWex a (.neg (synWb (.objMem a w)
            (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))))
      p0051 p0059 p0105
  have p0107 :=
    @gNotbii syntaxFormula0084
      (synWex a (.neg (synWb (.objMem a w)
            (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))))
      p0106
  have p0108 := @gElcompl (synCopk (.cv w) (synCsn (.cv y))) syntaxClass0030 p0050
  have p0109 :=
    @gEqabb (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))) a (.cv w)
      dv_cache_0024
  have p0110 :=
    @gAlex
      (synWb (.objMem a w) (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) a
  have p0111_e00_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0085 (.all a (synWb (.objMem a w)
            (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCtfin, synCif, synWo, synC0,
          synCdif, synCin, synCcompl, synCnin, synWnan, synCvv, synCio, synCuni,
          synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              apply Nominal.RecanonTransportDev.TRecanonWff.imp
              · exact Nominal.RecanonTransportDev.TRecanonWff.same _
              · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0109
  have p0111 :=
    @gBitri syntaxFormula0085
      (.all a (synWb (.objMem a w)
          (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))))
      (.neg (synWex a (.neg (synWb (.objMem a w)
              (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))))))
      p0111_e00_recanon p0110
  have p0112 :=
    @gN3bitr4i (.neg syntaxFormula0084)
      (.neg (synWex a (.neg (synWb (.objMem a w)
              (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))))))
      syntaxFormula0086 syntaxFormula0085 p0107 p0108 p0111
  have p0113 :=
    @gN3bitri syntaxFormula0087
      (.classMem (synCopk (synCsn (.cv w)) (synCsn (synCsn (.cv y)))) syntaxClass0032)
      syntaxFormula0086 syntaxFormula0085 p0047 p0049 p0112
  have p0114 :=
    @gOtkelins3k (synCsn (.cv w)) (.cv z) (synCsn (synCsn (.cv y))) (synCssetk) p0046
      p0025 p0002
  have p0115 := @gElssetk (.cv w) (.cv z) p0048 p0025
  have p0116_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv w)) (.cv z)) (synCssetk)) (.objMem w z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
      p0115
  have p0116 :=
    @gBitri syntaxFormula0088
      (.classMem (synCopk (synCsn (.cv w)) (.cv z)) (synCssetk)) (.objMem w z) p0114
      p0116_e01_recanon
  have p0117 :=
    @gAnbi12i syntaxFormula0087 syntaxFormula0085 syntaxFormula0088 (.objMem w z) p0113
      p0116
  have p0118 :=
    @gN3bitri syntaxFormula0056 syntaxFormula0059
      (synWa syntaxFormula0087 syntaxFormula0088)
      (synWa syntaxFormula0085 (.objMem w z)) p0044 p0045 p0117
  have p0119 :=
    @gExbii syntaxFormula0056 (synWa syntaxFormula0085 (.objMem w z)) w p0118
  have p0120 :=
    @gN3bitri syntaxFormula0089 syntaxFormula0055 syntaxFormula0057
      (synWex w (synWa syntaxFormula0085 (.objMem w z))) p0032 p0040 p0119
  have p0121 :=
    @gOtkelins3k (.cv z) (synCsn (synCsn (.cv y))) (synCsn (.cv n)) syntaxClass0035
      p0025 p0002 p0026
  have p0122 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w
      (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x))))) (.cv z)
      dv_cache_0025 dv_cache_0026)
  have p0123_e02_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0090 (synWex w (synWa syntaxFormula0085 (.objMem w z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCtfin, synCif, synWo, synC0,
          synCdif, synCin, synCcompl, synCnin, synWnan, synCvv, synCio, synCuni,
          synCsn]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq]
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
      p0122
  have p0123 :=
    @gN3bitr4i syntaxFormula0089 (synWex w (synWa syntaxFormula0085 (.objMem w z)))
      syntaxFormula0091 syntaxFormula0090 p0120 p0121 p0123_e02_recanon
  have p0124 :=
    @gAnbi12i syntaxFormula0050 (.classEq (.cv z) (synCtfin (.cv n))) syntaxFormula0091
      syntaxFormula0090 p0030 p0123
  have p0125 :=
    @gN3bitri syntaxFormula0093 syntaxFormula0049
      (synWa syntaxFormula0050 syntaxFormula0091) syntaxFormula0094 p0023 p0024 p0124
  have p0126 := @gExbii syntaxFormula0093 syntaxFormula0094 z p0125
  have p0127 := @gOpkex (synCsn (synCsn (.cv y))) (synCsn (.cv n))
  have p0128 :=
    @gElimak t syntaxClass0037 (synCpw1 (synC1c))
      (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n))) dv_cache_0027 dv_cache_0028
      dv_cache_0029 p0127
  have p0129 := @gElpw11c z (.cv t) dv_cache_0030
  have p0130 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex z (.classEq (.cv t) (synCsn (synCsn (.cv z))))) syntaxFormula0048 p0129
  have p0131 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv z)))) syntaxFormula0048 z
      dv_cache_0031
  have p0132 :=
    @gBitr4i syntaxFormula0095
      (synWa (synWex z (.classEq (.cv t) (synCsn (synCsn (.cv z))))) syntaxFormula0048)
      syntaxFormula0096 p0130 p0131
  have p0133 := @gExbii syntaxFormula0095 syntaxFormula0096 t p0132
  have p0134 := (Nominal.biimpRefl syntaxFormula0097)
  have p0135 := @gExcom syntaxFormula0092 z t
  have p0136 :=
    @gN3bitr4i (synWex t syntaxFormula0095) (synWex t syntaxFormula0096)
      syntaxFormula0097 syntaxFormula0098 p0133 p0134 p0135
  have p0137 := @gBitri syntaxFormula0099 syntaxFormula0097 syntaxFormula0098 p0128 p0136
  have p0138 := @gTfinex (.cv n)
  have p0139 :=
    @gClel3 z (.cab a (synWrex x (.cv y) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCtfin (.cv n)) dv_cache_0032 dv_cache_0033 p0138
  have p0140 :=
    @gN3bitr4i syntaxFormula0098 (synWex z syntaxFormula0094) syntaxFormula0099
      syntaxFormula0100 p0126 p0137 p0139
  have p0141 := @gNotbii syntaxFormula0099 syntaxFormula0100 p0140
  have p0142 :=
    @gAnbi12i syntaxFormula0046 (synWss (.cv y) (synCnnc)) syntaxFormula0101
      (.neg syntaxFormula0100) p0019 p0141
  have p0143 := @gAnnim (synWss (.cv y) (synCnnc)) syntaxFormula0100
  have p0144 :=
    @gN3bitri syntaxFormula0102 (synWa syntaxFormula0046 syntaxFormula0101)
      (synWa (synWss (.cv y) (synCnnc)) (.neg syntaxFormula0100)) syntaxFormula0104
      p0012 p0142 p0143
  have p0145 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n)))
        (synCsik (synCssetk)))
      (.objMem y n) syntaxFormula0102 syntaxFormula0104 p0011 p0144
  have p0146 :=
    @gN3bitri syntaxFormula0106 syntaxFormula0044
      (synWa (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCsn (.cv n)))
          (synCsik (synCssetk))) syntaxFormula0102)
      (synWa (.objMem y n) syntaxFormula0104) p0005 p0006 p0145
  have p0147 :=
    @gExbii syntaxFormula0106 (synWa (.objMem y n) syntaxFormula0104) y p0146
  have p0148 :=
    @gElimak t syntaxClass0040 (synCpw1 (synC1c)) (synCsn (.cv n)) dv_cache_0034
      dv_cache_0028 dv_cache_0035 p0026
  have p0149 := @gElpw11c y (.cv t) dv_cache_0036
  have p0150 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex y (.classEq (.cv t) (synCsn (synCsn (.cv y))))) syntaxFormula0043 p0149
  have p0151 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv y)))) syntaxFormula0043 y
      dv_cache_0037
  have p0152 :=
    @gBitr4i syntaxFormula0107
      (synWa (synWex y (.classEq (.cv t) (synCsn (synCsn (.cv y))))) syntaxFormula0043)
      syntaxFormula0108 p0150 p0151
  have p0153 := @gExbii syntaxFormula0107 syntaxFormula0108 t p0152
  have p0154 := (Nominal.biimpRefl syntaxFormula0109)
  have p0155 := @gExcom syntaxFormula0105 y t
  have p0156 :=
    @gN3bitr4i (synWex t syntaxFormula0107) (synWex t syntaxFormula0108)
      syntaxFormula0109 syntaxFormula0110 p0153 p0154 p0155
  have p0157 := @gBitri syntaxFormula0111 syntaxFormula0109 syntaxFormula0110 p0148 p0156
  have p0158 := (Nominal.biimpRefl syntaxFormula0112)
  have p0159_e02_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0112 (synWex y (synWa (.objMem y n) syntaxFormula0104))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWex, synWa]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0158
  have p0159 :=
    @gN3bitr4i syntaxFormula0110 (synWex y (synWa (.objMem y n) syntaxFormula0104))
      syntaxFormula0111 syntaxFormula0112 p0147 p0157 p0159_e02_recanon
  have p0160 := @gNotbii syntaxFormula0111 syntaxFormula0112 p0159
  have p0161 := @gElcompl (synCsn (.cv n)) syntaxClass0041 p0026
  have p0162 := @gDfral2 syntaxFormula0103 y (.cv n)
  have p0163 :=
    @gN3bitr4i (.neg syntaxFormula0111) (.neg syntaxFormula0112) syntaxFormula0113
      syntaxFormula0114 p0160 p0161 p0162
  have p0164 :=
    @gBitri (.classMem (.cv n) syntaxClass0115) syntaxFormula0113 syntaxFormula0114 p0001
      p0163
  have p0165 := @gEqabi syntaxFormula0114 n syntaxClass0115 dv_cache_0038 p0164
  have p0166 := @gSsetkex
  have p0167 := @gSikex (synCssetk) p0166
  have p0168 := @gNncex
  have p0169 := @gPwex (synCnnc) p0168
  have p0170 := @gPw1ex (synCpw (synCnnc)) p0169
  have p0171 := @gVvex
  have p0172 := @gXpkex (synCpw1 (synCpw (synCnnc))) (synCvv) p0170 p0171
  have p0173 := @gSikex (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv)) p0172
  have p0174 := @gTfinrelkex
  have p0175 := @gCnvkex syntaxClass0021 p0174
  have p0176 := @gIns2kex syntaxClass0022 p0175
  have p0178 := @gIns3kex (synCssetk) p0166
  have p0180 := @gIns2kex (synCssetk) p0166
  have p0182 := @gIns3kex syntaxClass0021 p0174
  have p0183 := @gInex (synCins2k (synCssetk)) syntaxClass0024 p0180 p0182
  have p0184 := @gN1cex
  have p0185 := @gPw1ex (synC1c) p0184
  have p0186 := @gPw1ex (synCpw1 (synC1c)) p0185
  have p0187 := @gImakex syntaxClass0025 (synCpw1 (synCpw1 (synC1c))) p0183 p0186
  have p0188 := @gSikex syntaxClass0026 p0187
  have p0189 := @gIns2kex syntaxClass0027 p0188
  have p0190 := @gSymdifex (synCins3k (synCssetk)) syntaxClass0028 p0178 p0189
  have p0191 := @gImakex syntaxClass0029 (synCpw1 (synCpw1 (synC1c))) p0190 p0186
  have p0192 := @gComplex syntaxClass0030 p0191
  have p0193 := @gSikex syntaxClass0031 p0192
  have p0194 := @gIns2kex syntaxClass0032 p0193
  have p0195 := @gInex syntaxClass0033 (synCins3k (synCssetk)) p0194 p0178
  have p0196 := @gImakex syntaxClass0034 (synCpw1 (synCpw1 (synC1c))) p0195 p0186
  have p0197 := @gIns3kex syntaxClass0035 p0196
  have p0198 := @gInex syntaxClass0023 syntaxClass0036 p0176 p0197
  have p0199 := @gImakex syntaxClass0037 (synCpw1 (synC1c)) p0198 p0185
  have p0200 :=
    @gDifex (synCsik (synCxpk (synCpw1 (synCpw (synCnnc))) (synCvv)))
      syntaxClass0038 p0173 p0199
  have p0201 := @gInex (synCsik (synCssetk)) syntaxClass0039 p0167 p0200
  have p0202 := @gImakex syntaxClass0040 (synCpw1 (synC1c)) p0201 p0185
  have p0203 := @gComplex syntaxClass0041 p0202
  have p0204 := @gUni1ex syntaxClass0042 p0203
  have p0205 :=
    @gEqeltrri syntaxClass0115 (.cab n syntaxFormula0114) (synCvv) p0165 p0204
  exact p0205


end NFChoice.DirectNominalPrf.WPPReplay

end
