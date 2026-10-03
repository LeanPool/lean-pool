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

@[expose]
noncomputable def g_sfintfin (M : Class) (N : Class) :
    Nominal.NPrf (.imp (syn_wsfin M N) (syn_wsfin (syn_ctfin M) (syn_ctfin N))) :=
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
  have dv_cache_0004 : n ∉ ((Wff.classEq (.cv k) (syn_c0c))).fv :=
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
      ((Wff.imp (syn_wsfin (.cv m) (.cv n))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))))).fv :=
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
      ((Wff.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))).fv :=
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
  have dv_cache_0008 : n ∉ ((Wff.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c)))).fv :=
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
  have dv_cache_0010 : a ∉ ((syn_cplc (.cv m) (syn_c1c))).fv :=
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
      ((Wff.imp (syn_wsfin (.cv m) (.cv q))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))).fv :=
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
  have dv_cache_0014 : a ∉ ((syn_cplc (.cv q) (.cv q))).fv :=
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
  have dv_cache_0015 : a ∉ ((syn_ctfin (.cv m))).fv :=
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
  have dv_cache_0016 : a ∉ ((syn_ctfin (.cv q))).fv :=
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
  have dv_cache_0017 : k ∉ ((syn_ctfin (.cv m))).fv :=
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
      ((syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
          (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
            (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
              (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                  (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))).fv :=
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
      ((syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
          (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))).fv :=
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
      ((syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
            (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
              (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                  (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))).fv :=
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
  have dv_cache_0022 : a ∉ ((syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))).fv :=
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
  have dv_cache_0023 : a ∉ ((syn_wne (syn_cplc (.cv q) (.cv q)) (syn_c0))).fv :=
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
    q ∉ ((syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))).fv :=
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
      ((syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
              (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
          (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv :=
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
    a ∉ ((syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))).fv :=
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
      ((syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
              (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
          (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))).fv :=
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
      ((syn_wa (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
              (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))))).fv :=
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
      ((Wff.all p (.imp (syn_wsfin (.cv m) (.cv p))
            (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))).fv :=
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
      ((Wff.all n (.imp (syn_wsfin (.cv k) (.cv n))
            (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))))).fv :=
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
      ((Wff.all n (.imp (syn_wsfin (syn_c0c) (.cv n))
            (syn_wsfin (syn_c0c) (syn_ctfin (.cv n)))))).fv :=
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
      ((Wff.all n (.imp (syn_wsfin M (.cv n))
            (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n)))))).fv :=
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
      ((Wff.all n (.imp (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))))).fv :=
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
    n ∉ ((Wff.imp (syn_wsfin M N) (syn_wsfin (syn_ctfin M) (syn_ctfin N)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin M N a
      dv_cache_0001 dv_cache_0002
  have p0001 :=
    @g_n_3simpa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N)))
  have p0002 :=
    @g_sylbi (syn_wsfin M N)
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (syn_wex a
          (syn_wa (.classMem (syn_cpw1 (.cv a)) M) (.classMem (syn_cpw (.cv a)) N))))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) p0000 p0001
  have p0003 := @g_sfintfinlem1 k n dv_cache_0003
  have p0004 := @g_sfineq1 (.cv k) (syn_c0c) (.cv n)
  have p0005 := @g_tfineq (.cv k) (syn_c0c)
  have p0006 := @g_tfin0c
  have p0007 :=
    @g_syl6eq (.classEq (.cv k) (syn_c0c)) (syn_ctfin (.cv k)) (syn_ctfin (syn_c0c))
      (syn_c0c) p0005 p0006
  have p0008 := @g_sfineq1 (syn_ctfin (.cv k)) (syn_c0c) (syn_ctfin (.cv n))
  have p0009 :=
    @g_syl (.classEq (.cv k) (syn_c0c)) (.classEq (syn_ctfin (.cv k)) (syn_c0c))
      (syn_wb (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))
        (syn_wsfin (syn_c0c) (syn_ctfin (.cv n))))
      p0007 p0008
  have p0010 :=
    @g_imbi12d (.classEq (.cv k) (syn_c0c)) (syn_wsfin (.cv k) (.cv n))
      (syn_wsfin (syn_c0c) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))
      (syn_wsfin (syn_c0c) (syn_ctfin (.cv n))) p0004 p0009
  have p0011 :=
    @g_albidv (.classEq (.cv k) (syn_c0c))
      (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))))
      (.imp (syn_wsfin (syn_c0c) (.cv n)) (syn_wsfin (syn_c0c) (syn_ctfin (.cv n)))) n
      dv_cache_0004 p0010
  have p0012 := @g_sfineq1 (.cv k) (.cv m) (.cv n)
  have p0013 := @g_tfineq (.cv k) (.cv m)
  have p0014 := @g_sfineq1 (syn_ctfin (.cv k)) (syn_ctfin (.cv m)) (syn_ctfin (.cv n))
  have p0015_e00_recanon :
    Nominal.NPrf (.imp (.objEq k m) (.classEq (syn_ctfin (.cv k)) (syn_ctfin (.cv m)))) :=
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
      p0013
  have p0015 :=
    @g_syl (.objEq k m) (.classEq (syn_ctfin (.cv k)) (syn_ctfin (.cv m)))
      (syn_wb (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))))
      p0015_e00_recanon p0014
  have p0016_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq k m) (syn_wb (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (.cv m) (.cv n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0016 :=
    @g_imbi12d (.objEq k m) (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (.cv m) (.cv n))
      (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))) p0016_e00_recanon p0015
  have p0017 :=
    @g_albidv (.objEq k m)
      (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))))
      (.imp (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))))
      n dv_cache_0005 p0016
  have p0018 := @g_sfineq2 (.cv n) (.cv p) (.cv m)
  have p0019 := @g_tfineq (.cv n) (.cv p)
  have p0020 := @g_sfineq2 (syn_ctfin (.cv n)) (syn_ctfin (.cv p)) (syn_ctfin (.cv m))
  have p0021_e00_recanon :
    Nominal.NPrf (.imp (.objEq n p) (.classEq (syn_ctfin (.cv n)) (syn_ctfin (.cv p)))) :=
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
      p0019
  have p0021 :=
    @g_syl (.objEq n p) (.classEq (syn_ctfin (.cv n)) (syn_ctfin (.cv p)))
      (syn_wb (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))
      p0021_e00_recanon p0020
  have p0022_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq n p) (syn_wb (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (.cv m) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0018
  have p0022 :=
    @g_imbi12d (.objEq n p) (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (.cv m) (.cv p))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))) p0022_e00_recanon p0021
  have p0023 :=
    @g_cbvalv
      (.imp (syn_wsfin (.cv m) (.cv n)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n))))
      (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))
      n p dv_cache_0006 dv_cache_0007 p0022
  have p0024 :=
    @g_syl6bb (.objEq k m)
      (.all n (.imp (syn_wsfin (.cv k) (.cv n))
          (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))))
      (.all n (.imp (syn_wsfin (.cv m) (.cv n))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv n)))))
      (.all p (.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
      p0017 p0023
  have p0025 := @g_sfineq1 (.cv k) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0026 := @g_tfineq (.cv k) (syn_cplc (.cv m) (syn_c1c))
  have p0027 :=
    @g_sfineq1 (syn_ctfin (.cv k)) (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
      (syn_ctfin (.cv n))
  have p0028 :=
    @g_syl (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c)))
      (.classEq (syn_ctfin (.cv k)) (syn_ctfin (syn_cplc (.cv m) (syn_c1c))))
      (syn_wb (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))
        (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))))
      p0026 p0027
  have p0029 :=
    @g_imbi12d (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c))) (syn_wsfin (.cv k) (.cv n))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0025 p0028
  have p0030 :=
    @g_albidv (.classEq (.cv k) (syn_cplc (.cv m) (syn_c1c)))
      (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))))
      (.imp (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))))
      n dv_cache_0008 p0029
  have p0031 := @g_sfineq1 (.cv k) M (.cv n)
  have p0032 := @g_tfineq (.cv k) M
  have p0033 := @g_sfineq1 (syn_ctfin (.cv k)) (syn_ctfin M) (syn_ctfin (.cv n))
  have p0034 :=
    @g_syl (.classEq (.cv k) M) (.classEq (syn_ctfin (.cv k)) (syn_ctfin M))
      (syn_wb (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))
        (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n))))
      p0032 p0033
  have p0035 :=
    @g_imbi12d (.classEq (.cv k) M) (syn_wsfin (.cv k) (.cv n)) (syn_wsfin M (.cv n))
      (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))
      (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n))) p0031 p0034
  have p0036 :=
    @g_albidv (.classEq (.cv k) M)
      (.imp (syn_wsfin (.cv k) (.cv n)) (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n))))
      (.imp (syn_wsfin M (.cv n)) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n)))) n
      dv_cache_0009 p0035
  have p0037 := @g_sfin01
  have p0038 := @g_sfin112 (syn_c1c) (syn_c0c) (.cv n)
  have p0039 :=
    @g_mpan2 (syn_wsfin (syn_c0c) (.cv n)) (syn_wsfin (syn_c0c) (syn_c1c))
      (.classEq (.cv n) (syn_c1c)) p0037 p0038
  have p0041 := @g_tfineq (.cv n) (syn_c1c)
  have p0042 := @g_tfin1c
  have p0043 :=
    @g_syl6eq (.classEq (.cv n) (syn_c1c)) (syn_ctfin (.cv n)) (syn_ctfin (syn_c1c))
      (syn_c1c) p0041 p0042
  have p0044 := @g_sfineq2 (syn_ctfin (.cv n)) (syn_c1c) (syn_c0c)
  have p0045 :=
    @g_syl (.classEq (.cv n) (syn_c1c)) (.classEq (syn_ctfin (.cv n)) (syn_c1c))
      (syn_wb (syn_wsfin (syn_c0c) (syn_ctfin (.cv n))) (syn_wsfin (syn_c0c) (syn_c1c)))
      p0043 p0044
  have p0046 :=
    @g_mpbiri (.classEq (.cv n) (syn_c1c)) (syn_wsfin (syn_c0c) (syn_ctfin (.cv n)))
      (syn_wsfin (syn_c0c) (syn_c1c)) p0037 p0045
  have p0047 :=
    @g_syl (syn_wsfin (syn_c0c) (.cv n)) (.classEq (.cv n) (syn_c1c))
      (syn_wsfin (syn_c0c) (syn_ctfin (.cv n))) p0039 p0046
  have p0048 := Nominal.gen p0047 n
  have p0049 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin
      (syn_cplc (.cv m) (syn_c1c)) (.cv n) a dv_cache_0010 dv_cache_0011
  have p0050 :=
    @g_simp3bi (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (.cv n))))
      p0049
  have p0051 :=
    @g_n_3ad2ant3 (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (.classMem (.cv m) (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (.cv n))))
      (.all p (.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
      p0050
  have p0052 := @g_sfindbl (.cv a) q (.cv m) dv_cache_0012
  have p0053 :=
    @g_n_3ad2antl1 (.classMem (.cv m) (syn_cnnc))
      (.all p (.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wrex q (syn_cnnc) (syn_wa (syn_wsfin (.cv m) (.cv q))
          (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) p0052
  have p0054 := @g_sfineq2 (.cv p) (.cv q) (.cv m)
  have p0055 := @g_tfineq (.cv p) (.cv q)
  have p0056 := @g_sfineq2 (syn_ctfin (.cv p)) (syn_ctfin (.cv q)) (syn_ctfin (.cv m))
  have p0057_e00_recanon :
    Nominal.NPrf (.imp (.objEq p q) (.classEq (syn_ctfin (.cv p)) (syn_ctfin (.cv q)))) :=
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
      p0055
  have p0057 :=
    @g_syl (.objEq p q) (.classEq (syn_ctfin (.cv p)) (syn_ctfin (.cv q)))
      (syn_wb (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      p0057_e00_recanon p0056
  have p0058_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p q) (syn_wb (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (.cv m) (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0054
  have p0058 :=
    @g_imbi12d (.objEq p q) (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (.cv m) (.cv q))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) p0058_e00_recanon p0057
  have p0059 :=
    @g_spv
      (.imp (syn_wsfin (.cv m) (.cv p)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))
      (.imp (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      p q dv_cache_0013 p0058
  have p0060 :=
    @g_simprrl (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (.classMem (.cv q) (syn_cnnc)) (syn_wsfin (.cv m) (.cv q))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))
  have p0061 :=
    @g_adantl
      (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
            (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))
      (syn_wsfin (.cv m) (.cv q)) (.classMem (.cv m) (syn_cnnc)) p0060
  have p0062 :=
    @g_simplrl (.classMem (.cv m) (syn_cnnc))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
          (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
  have p0063 :=
    @g_simprrr (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (.classMem (.cv q) (syn_cnnc)) (syn_wsfin (.cv m) (.cv q))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))
  have p0064 :=
    @g_ad2antlr
      (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
            (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))
      (.classMem (.cv m) (syn_cnnc)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      p0063
  have p0065 := @g_sfin112 (syn_cplc (.cv q) (.cv q)) (syn_cplc (.cv m) (syn_c1c)) (.cv n)
  have p0066 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))
      (.classEq (.cv n) (syn_cplc (.cv q) (.cv q))) p0062 p0064 p0065
  have p0067 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin
      (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)) a dv_cache_0010
      dv_cache_0014
  have p0068 :=
    @g_simp3bi (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc (.cv q) (.cv q)) (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q)))))
      p0067
  have p0069 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q)))))
      p0064 p0068
  have p0070 :=
    @g_simp2
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
  have p0071 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin
      (syn_ctfin (.cv m)) (syn_ctfin (.cv q)) a dv_cache_0015 dv_cache_0016
  have p0072 :=
    @g_simp1bi (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (.classMem (syn_ctfin (.cv m)) (syn_cnnc))
      (.classMem (syn_ctfin (.cv q)) (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_ctfin (.cv m)))
          (.classMem (syn_cpw (.cv a)) (syn_ctfin (.cv q)))))
      p0071
  have p0073 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
        (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (.classMem (syn_ctfin (.cv m)) (syn_cnnc)) p0070 p0072
  have p0074 :=
    @g_simp1l (.classMem (.cv m) (syn_cnnc))
      (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
            (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
  have p0075 := @g_peano2 (.cv m)
  have p0076 :=
    @g_syl
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
        (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))))
      (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      p0074 p0075
  have p0077 :=
    @g_simp3
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
  have p0078 := @g_tfinpw1 (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))
  have p0079 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
        (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv a))) (syn_ctfin (syn_cplc (.cv m) (syn_c1c))))
      p0076 p0077 p0078
  have p0080 := @g_ne0i (syn_cplc (.cv m) (syn_c1c)) (syn_cpw1 (.cv a))
  have p0081 :=
    @g_n_3ad2ant3 (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) p0080
  have p0082 := @g_tfinsuc (.cv m)
  have p0083 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
        (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))))
      (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (.classEq (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)))
      p0074 p0081 p0082
  have p0084 :=
    @g_eleqtrd
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
        (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))))
      (syn_cpw1 (syn_cpw1 (.cv a))) (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
      (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) p0079 p0083
  have p0085 := @g_sfindbl (syn_cpw1 (.cv a)) k (syn_ctfin (.cv m)) dv_cache_0017
  have p0086 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
        (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))))
      (.classMem (syn_ctfin (.cv m)) (syn_cnnc))
      (.classMem (syn_cpw1 (syn_cpw1 (.cv a))) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)))
      (syn_wrex k (syn_cnnc) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k))
          (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))))
      p0073 p0084 p0085
  have p0087 :=
    @g_simp2
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k))
        (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))
  have p0088 :=
    @g_simp3l
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (syn_wsfin (syn_ctfin (.cv m)) (.cv k))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))
  have p0089 := @g_sfin112 (.cv k) (syn_ctfin (.cv m)) (syn_ctfin (.cv q))
  have p0090 :=
    @g_syl2anc
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
        (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k))
          (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) (.classEq (syn_ctfin (.cv q)) (.cv k)) p0087
      p0088 p0089
  have p0091 := @g_addceq12 (syn_ctfin (.cv q)) (syn_ctfin (.cv q)) (.cv k) (.cv k)
  have p0092 :=
    @g_anidms (.classEq (syn_ctfin (.cv q)) (.cv k))
      (.classEq (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))) (syn_cplc (.cv k) (.cv k)))
      p0091
  have p0093 :=
    @g_sfineq2 (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))
      (syn_cplc (.cv k) (.cv k)) (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
  have p0094 :=
    @g_syl (.classEq (syn_ctfin (.cv q)) (.cv k))
      (.classEq (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))) (syn_cplc (.cv k) (.cv k)))
      (syn_wb (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
          (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
        (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))
      p0092 p0093
  have p0095 :=
    @g_biimprcd (.classEq (syn_ctfin (.cv q)) (.cv k))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))
      p0094
  have p0096 :=
    @g_adantl
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))
      (.imp (.classEq (syn_ctfin (.cv q)) (.cv k))
        (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
          (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))))
      (syn_wsfin (syn_ctfin (.cv m)) (.cv k)) p0095
  have p0097 :=
    @g_n_3ad2ant3
      (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k))
        (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (.imp (.classEq (syn_ctfin (.cv q)) (.cv k))
        (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
          (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))) p0096
  have p0098 :=
    @g_mpd
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
        (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k))
          (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))))
      (.classEq (syn_ctfin (.cv q)) (.cv k))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      p0090 p0097
  have p0099 :=
    @g_n_3expia
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k))
        (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      p0098
  have p0100 :=
    @g_rexlimdvw
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k))
        (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k))))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      k (syn_cnnc) dv_cache_0018 dv_cache_0019 p0099
  have p0101 :=
    @g_n_3adant3
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (.imp (syn_wrex k (syn_cnnc) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k))
            (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))))
        (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
          (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) p0100
  have p0102 :=
    @g_mpd
      (syn_w3a (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
        (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))))
      (syn_wrex k (syn_cnnc) (syn_wa (syn_wsfin (syn_ctfin (.cv m)) (.cv k))
          (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_cplc (.cv k) (.cv k)))))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      p0086 p0101
  have p0103 :=
    @g_n_3expia
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      p0102
  have p0104 :=
    @g_adantrd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))) p0103
  have p0105 :=
    @g_exlimdv
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
        (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      a dv_cache_0020 dv_cache_0021 p0104
  have p0106 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q)))))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      p0069 p0105
  have p0107 :=
    @g_simpll (.classMem (.cv m) (syn_cnnc))
      (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
            (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
  have p0108 :=
    @g_adantr (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))) p0080
  have p0109 :=
    @g_exlimiv
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
        (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) a dv_cache_0022 p0108
  have p0110 :=
    @g_n_3syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q)))))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0064 p0068 p0109
  have p0111 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (.classEq (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)))
      p0107 p0110 p0082
  have p0112 :=
    @g_simprrl (.classMem (.cv m) (syn_cnnc))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)) (.classMem (.cv q) (syn_cnnc))
      (syn_wa (syn_wsfin (.cv m) (.cv q))
        (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))
  have p0113 :=
    @g_adantr
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (.classMem (.cv q) (syn_cnnc)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      p0112
  have p0114 := @g_ne0i (syn_cplc (.cv q) (.cv q)) (syn_cpw (.cv a))
  have p0115 :=
    @g_adantl (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q)))
      (syn_wne (syn_cplc (.cv q) (.cv q)) (syn_c0))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) p0114
  have p0116 :=
    @g_exlimiv
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
        (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q))))
      (syn_wne (syn_cplc (.cv q) (.cv q)) (syn_c0)) a dv_cache_0023 p0115
  have p0117 :=
    @g_n_3syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (syn_cplc (.cv q) (.cv q)))))
      (syn_wne (syn_cplc (.cv q) (.cv q)) (syn_c0)) p0064 p0068 p0116
  have p0118 := @g_tfindi (.cv q) (.cv q)
  have p0119 :=
    @g_syl3anc
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (.classMem (.cv q) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc))
      (syn_wne (syn_cplc (.cv q) (.cv q)) (syn_c0))
      (.classEq (syn_ctfin (syn_cplc (.cv q) (.cv q)))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      p0113 p0113 p0117 p0118
  have p0120 :=
    @g_sfineq1 (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
      (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)) (syn_ctfin (syn_cplc (.cv q) (.cv q)))
  have p0121 :=
    @g_sfineq2 (syn_ctfin (syn_cplc (.cv q) (.cv q)))
      (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))
      (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
  have p0122 :=
    @g_sylan9bb
      (.classEq (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
        (syn_ctfin (syn_cplc (.cv q) (.cv q))))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_ctfin (syn_cplc (.cv q) (.cv q))))
      (.classEq (syn_ctfin (syn_cplc (.cv q) (.cv q)))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      p0120 p0121
  have p0123 :=
    @g_syl2anc
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (.classEq (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (syn_ctfin (.cv m)) (syn_c1c)))
      (.classEq (syn_ctfin (syn_cplc (.cv q) (.cv q)))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      (syn_wb (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
          (syn_ctfin (syn_cplc (.cv q) (.cv q))))
        (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
          (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q)))))
      p0111 p0119 p0122
  have p0124 :=
    @g_mpbird
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
        (syn_ctfin (syn_cplc (.cv q) (.cv q))))
      (syn_wsfin (syn_cplc (syn_ctfin (.cv m)) (syn_c1c))
        (syn_cplc (syn_ctfin (.cv q)) (syn_ctfin (.cv q))))
      p0106 p0123
  have p0125 := @g_tfineq (.cv n) (syn_cplc (.cv q) (.cv q))
  have p0126 :=
    @g_sfineq2 (syn_ctfin (.cv n)) (syn_ctfin (syn_cplc (.cv q) (.cv q)))
      (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
  have p0127 :=
    @g_syl (.classEq (.cv n) (syn_cplc (.cv q) (.cv q)))
      (.classEq (syn_ctfin (.cv n)) (syn_ctfin (syn_cplc (.cv q) (.cv q))))
      (syn_wb (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))
        (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
          (syn_ctfin (syn_cplc (.cv q) (.cv q)))))
      p0125 p0126
  have p0128 :=
    @g_biimprcd (.classEq (.cv n) (syn_cplc (.cv q) (.cv q)))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
        (syn_ctfin (syn_cplc (.cv q) (.cv q))))
      p0127
  have p0129 :=
    @g_syl
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c)))
        (syn_ctfin (syn_cplc (.cv q) (.cv q))))
      (.imp (.classEq (.cv n) (syn_cplc (.cv q) (.cv q)))
        (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))))
      p0124 p0128
  have p0130 :=
    @g_mpd
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc))
          (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
            (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
                (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
        (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (.classEq (.cv n) (syn_cplc (.cv q) (.cv q)))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0066 p0129
  have p0131 :=
    @g_ex
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0130
  have p0132 :=
    @g_embantd
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q)))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0061 p0131
  have p0133 :=
    @g_syl5
      (.all p (.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
      (.imp (syn_wsfin (.cv m) (.cv q)) (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv q))))
      (syn_wa (.classMem (.cv m) (syn_cnnc))
        (syn_wa (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
              (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0059 p0132
  have p0134 :=
    @g_exp32 (.classMem (.cv m) (syn_cnnc))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
          (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))
      (.imp (.all p (.imp (syn_wsfin (.cv m) (.cv p))
            (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
        (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))))
      p0133
  have p0135 :=
    @g_com34 (.classMem (.cv m) (syn_cnnc))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
          (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))
      (.all p (.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0134
  have p0136 :=
    @g_com23 (.classMem (.cv m) (syn_cnnc))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (.all p (.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
      (.imp (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
            (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))
        (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))))
      p0135
  have p0137 :=
    @g_n_3imp (.classMem (.cv m) (syn_cnnc))
      (.all p (.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (.imp (syn_wa (.classMem (.cv q) (syn_cnnc)) (syn_wa (syn_wsfin (.cv m) (.cv q))
            (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))
        (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))))
      p0136
  have p0138 :=
    @g_exp3a
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
            (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
        (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (.classMem (.cv q) (syn_cnnc))
      (syn_wa (syn_wsfin (.cv m) (.cv q))
        (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0137
  have p0139 :=
    @g_rexlimdv
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
            (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
        (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (syn_wa (syn_wsfin (.cv m) (.cv q))
        (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q))))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) q
      (syn_cnnc) dv_cache_0024 dv_cache_0025 p0138
  have p0140 :=
    @g_adantr
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
            (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
        (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (.imp (syn_wrex q (syn_cnnc) (syn_wa (syn_wsfin (.cv m) (.cv q))
            (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))
        (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))) p0139
  have p0141 :=
    @g_mpd
      (syn_wa (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
              (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
          (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
        (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c))))
      (syn_wrex q (syn_cnnc) (syn_wa (syn_wsfin (.cv m) (.cv q))
          (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv q) (.cv q)))))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0053 p0140
  have p0142 :=
    @g_ex
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
            (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
        (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0141
  have p0143 :=
    @g_adantrd
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
            (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
        (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))
      (.classMem (syn_cpw (.cv a)) (.cv n)) p0142
  have p0144 :=
    @g_exlimdv
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
            (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
        (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
        (.classMem (syn_cpw (.cv a)) (.cv n)))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) a
      dv_cache_0026 dv_cache_0027 p0143
  have p0145 :=
    @g_mpd
      (syn_w3a (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
            (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
        (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n)))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cplc (.cv m) (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (.cv n))))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0051 p0144
  have p0146 :=
    @g_n_3expia (.classMem (.cv m) (syn_cnnc))
      (.all p (.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
      (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
      (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))) p0145
  have p0147 :=
    @g_alrimiv
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.all p (.imp (syn_wsfin (.cv m) (.cv p))
            (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p))))))
      (.imp (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
        (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n))))
      n dv_cache_0028 p0146
  have p0148 :=
    @g_ex (.classMem (.cv m) (syn_cnnc))
      (.all p (.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
      (.all n (.imp (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))))
      p0147
  have p0149 :=
    @g_finds
      (.all n (.imp (syn_wsfin (.cv k) (.cv n))
          (syn_wsfin (syn_ctfin (.cv k)) (syn_ctfin (.cv n)))))
      (.all n (.imp (syn_wsfin (syn_c0c) (.cv n)) (syn_wsfin (syn_c0c) (syn_ctfin (.cv n)))))
      (.all p (.imp (syn_wsfin (.cv m) (.cv p))
          (syn_wsfin (syn_ctfin (.cv m)) (syn_ctfin (.cv p)))))
      (.all n (.imp (syn_wsfin (syn_cplc (.cv m) (syn_c1c)) (.cv n))
          (syn_wsfin (syn_ctfin (syn_cplc (.cv m) (syn_c1c))) (syn_ctfin (.cv n)))))
      (.all n (.imp (syn_wsfin M (.cv n)) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n)))))
      k m M dv_cache_0029 dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0035 p0003 p0011 p0024 p0030 p0036 p0048 p0148
  have p0150 := @g_sfineq2 (.cv n) N M
  have p0151 := @g_tfineq (.cv n) N
  have p0152 := @g_sfineq2 (syn_ctfin (.cv n)) (syn_ctfin N) (syn_ctfin M)
  have p0153 :=
    @g_syl (.classEq (.cv n) N) (.classEq (syn_ctfin (.cv n)) (syn_ctfin N))
      (syn_wb (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n)))
        (syn_wsfin (syn_ctfin M) (syn_ctfin N)))
      p0151 p0152
  have p0154 :=
    @g_imbi12d (.classEq (.cv n) N) (syn_wsfin M (.cv n)) (syn_wsfin M N)
      (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n)))
      (syn_wsfin (syn_ctfin M) (syn_ctfin N)) p0150 p0153
  have p0155 :=
    @g_spcgv (.imp (syn_wsfin M (.cv n)) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n))))
      (.imp (syn_wsfin M N) (syn_wsfin (syn_ctfin M) (syn_ctfin N))) n N (syn_cnnc)
      dv_cache_0036 dv_cache_0037 p0154
  have p0156 :=
    @g_mpan9 (.classMem M (syn_cnnc))
      (.all n (.imp (syn_wsfin M (.cv n)) (syn_wsfin (syn_ctfin M) (syn_ctfin (.cv n)))))
      (.classMem N (syn_cnnc))
      (.imp (syn_wsfin M N) (syn_wsfin (syn_ctfin M) (syn_ctfin N))) p0149 p0155
  have p0157 :=
    @g_mpcom (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))) (syn_wsfin M N)
      (syn_wsfin (syn_ctfin M) (syn_ctfin N)) p0002 p0156
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

@[expose]
noncomputable def g_tfinnnlem1 (x : Var) (y : Var) (n : Var) (a : Var) (_dv_a_n : a ≠ n)
    (dv_a_x : a ≠ x) (dv_a_y : a ≠ y) (_dv_n_x : n ≠ x) (dv_n_y : n ≠ y)
    (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classMem (.cab n (syn_wral y (.cv n) (.imp (syn_wss (.cv y) (syn_cnnc)) (.classMem
                (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
                (syn_ctfin (.cv n)))))) (syn_cvv)) :=
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
  have dv_cache_0001 : t ∉ ((syn_csn (syn_csn (.cv y)))).fv := by
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)))
          (syn_cin (syn_csik (syn_cssetk))
            (syn_cdif (syn_csik (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv))) (syn_cimak
                (syn_cin (syn_cins2k (syn_ccnvk
                      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                        (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cimak
                                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                        (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik
                                      (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
        (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k
        (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k
        (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c))))))).fv :=
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
  have dv_cache_0003 : t ∉ ((syn_csn (syn_csn (.cv z)))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv z)))
            (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)))) (syn_cin (syn_cins2k
              (syn_ccnvk (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                  (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk)))
                                (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k
                                        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                      (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                              (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k (syn_cimak
                (syn_cin (syn_cins2k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik
                                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0)))
        (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin
        (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw
        (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
      ((syn_cin (syn_cins2k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cimak
                          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                                (syn_cdif (syn_ccompl (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cssetk)))).fv :=
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
  have dv_cache_0006 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
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
  have dv_cache_0007 : t ∉ ((syn_copk (.cv z) (syn_csn (syn_csn (.cv y))))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv z) (syn_csn (syn_csn (.cv y))))) (syn_cin
            (syn_cins2k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                      (syn_cins2k (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0)))
                                    (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cssetk))))).fv :=
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
  have dv_cache_0010 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv w))))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv w))))
            (syn_copk (.cv z) (syn_csn (syn_csn (.cv y))))) (syn_cin (syn_cins2k (syn_csik
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                        (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0)))
                                    (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cssetk))))).fv :=
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
      ((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                    (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                      (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_cimak
                                  (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                      (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
                                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
  have dv_cache_0013 : t ∉ ((syn_copk (.cv w) (syn_csn (.cv y)))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv w) (syn_csn (.cv y))))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cimak
                  (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                        (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cimak
                                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                        (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
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
  have dv_cache_0016 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv a))))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
            (syn_copk (.cv w) (syn_csn (.cv y)))) (syn_csymdif (syn_cins3k (syn_cssetk))
            (syn_cins2k (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                        (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cimak
                                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                        (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
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
      ((syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))).fv :=
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
  have dv_cache_0019 : t ∉ ((syn_copk (.cv a) (.cv y))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv a) (.cv y)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))).fv :=
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
  have dv_cache_0022 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv a) (.cv y)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))))).fv :=
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
    w ∉ ((Class.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))).fv :=
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
      ((syn_cin (syn_cins2k (syn_ccnvk
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
                  (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k (syn_cimak
              (syn_cin (syn_cins2k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cimak
                                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                                      (syn_cdif (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik
        (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk
        (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
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
  have dv_cache_0028 : t ∉ ((syn_cpw1 (syn_c1c))).fv :=
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
    t ∉ ((syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))))
          (syn_cin (syn_cins2k (syn_ccnvk
                (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                    (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_cimak (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk)))
                                (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k
                                        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak
        (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                      (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
                              (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k (syn_cimak
                (syn_cin (syn_cins2k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik
                                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0)))
        (syn_csn (syn_c0))) (syn_cdif (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin
        (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk)))
        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw
        (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
    z ∉ ((Class.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))).fv :=
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
  have dv_cache_0033 : z ∉ ((syn_ctfin (.cv n))).fv :=
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
      ((syn_cin (syn_csik (syn_cssetk))
          (syn_cdif (syn_csik (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv))) (syn_cimak
              (syn_cin (syn_cins2k (syn_ccnvk
                    (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                      (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_cimak
                                  (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                      (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
                                        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                  (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik
                                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
        (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k
        (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k
        (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c)))))).fv :=
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
  have dv_cache_0035 : t ∉ ((syn_csn (.cv n))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_csn (.cv n))) (syn_cin (syn_csik (syn_cssetk))
            (syn_cdif (syn_csik (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv))) (syn_cimak
                (syn_cin (syn_cins2k (syn_ccnvk
                      (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0)))
                        (syn_cdif (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cimak
                                    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k
                                        (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin
        (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k
        (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk)))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik
                                      (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
        (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k
        (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif
        (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k
        (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c))))))).fv :=
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
      ((syn_cuni1 (syn_ccompl (syn_cimak (syn_cin (syn_csik (syn_cssetk))
                (syn_cdif (syn_csik (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv)))
                  (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_cun
                            (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif
                              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk)))
        (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv))
        (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
        (syn_cins3k (syn_csik (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))))) (syn_cins3k
                        (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik
        (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) (syn_cdif (syn_ccompl
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccnvk (syn_cssetk))) (syn_cins2k (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) (syn_cimak (syn_cin (syn_cins2k (syn_csik
        (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_cdif (syn_cxpk
        (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cins3k (syn_cidk))) (syn_cpw1 (syn_c1c)))))
        (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_c1c))))) (syn_cpw1 (syn_c1c)))))).fv :=
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
    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  let syntaxClass0001 : Class :=
    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) syntaxClass0000)
  let syntaxClass0002 : Class := (syn_csik syntaxClass0001)
  let syntaxClass0003 : Class := (syn_cins3k syntaxClass0002)
  let syntaxClass0004 : Class := (syn_cin syntaxClass0003 (syn_cins2k (syn_cssetk)))
  let syntaxClass0005 : Class :=
    (syn_cimak syntaxClass0004 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0006 : Class := (syn_cins3k syntaxClass0005)
  let syntaxClass0007 : Class :=
    (syn_cin (syn_cins2k (syn_csik (syn_cssetk))) syntaxClass0006)
  let syntaxClass0008 : Class :=
    (syn_cimak syntaxClass0007 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  let syntaxClass0009 : Class := (syn_cin (syn_cxpk (syn_cnnc) (syn_cvv)) syntaxClass0008)
  let syntaxClass0010 : Class := (syn_cins2k syntaxClass0009)
  let syntaxClass0011 : Class := (syn_csymdif syntaxClass0010 (syn_cins3k (syn_cidk)))
  let syntaxClass0012 : Class := (syn_cimak syntaxClass0011 (syn_cpw1 (syn_c1c)))
  let syntaxClass0013 : Class := (syn_cins2k syntaxClass0012)
  let syntaxClass0014 : Class :=
    (syn_cdif (syn_cins3k (syn_ccnvk (syn_cssetk))) syntaxClass0013)
  let syntaxClass0015 : Class := (syn_cimak syntaxClass0014 (syn_cpw1 (syn_c1c)))
  let syntaxClass0016 : Class := (syn_cins3k syntaxClass0015)
  let syntaxClass0017 : Class := (syn_csymdif (syn_cins2k (syn_cssetk)) syntaxClass0016)
  let syntaxClass0018 : Class :=
    (syn_cimak syntaxClass0017 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0019 : Class := (syn_ccompl syntaxClass0018)
  let syntaxClass0020 : Class :=
    (syn_cdif syntaxClass0019 (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_cvv)))
  let syntaxClass0021 : Class :=
    (syn_cun (syn_cxpk (syn_csn (syn_csn (syn_c0))) (syn_csn (syn_c0))) syntaxClass0020)
  let syntaxClass0022 : Class := (syn_ccnvk syntaxClass0021)
  let syntaxClass0023 : Class := (syn_cins2k syntaxClass0022)
  let syntaxClass0024 : Class := (syn_cins3k syntaxClass0021)
  let syntaxClass0025 : Class := (syn_cin (syn_cins2k (syn_cssetk)) syntaxClass0024)
  let syntaxClass0026 : Class :=
    (syn_cimak syntaxClass0025 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0027 : Class := (syn_csik syntaxClass0026)
  let syntaxClass0028 : Class := (syn_cins2k syntaxClass0027)
  let syntaxClass0029 : Class := (syn_csymdif (syn_cins3k (syn_cssetk)) syntaxClass0028)
  let syntaxClass0030 : Class :=
    (syn_cimak syntaxClass0029 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0031 : Class := (syn_ccompl syntaxClass0030)
  let syntaxClass0032 : Class := (syn_csik syntaxClass0031)
  let syntaxClass0033 : Class := (syn_cins2k syntaxClass0032)
  let syntaxClass0034 : Class := (syn_cin syntaxClass0033 (syn_cins3k (syn_cssetk)))
  let syntaxClass0035 : Class :=
    (syn_cimak syntaxClass0034 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0036 : Class := (syn_cins3k syntaxClass0035)
  let syntaxClass0037 : Class := (syn_cin syntaxClass0023 syntaxClass0036)
  let syntaxClass0038 : Class := (syn_cimak syntaxClass0037 (syn_cpw1 (syn_c1c)))
  let syntaxClass0039 : Class :=
    (syn_cdif (syn_csik (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv))) syntaxClass0038)
  let syntaxClass0040 : Class := (syn_cin (syn_csik (syn_cssetk)) syntaxClass0039)
  let syntaxClass0041 : Class := (syn_cimak syntaxClass0040 (syn_cpw1 (syn_c1c)))
  let syntaxClass0042 : Class := (syn_ccompl syntaxClass0041)
  let syntaxFormula0043 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_csn (.cv n))) syntaxClass0040)
  let syntaxFormula0044 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))) syntaxClass0040)
  let syntaxFormula0045 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv y)) (.cv n))
      (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv)))
  let syntaxFormula0046 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)))
      (syn_csik (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv))))
  let syntaxClass0047 : Class :=
    (syn_copk (syn_csn (syn_csn (.cv z)))
      (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))))
  let syntaxFormula0048 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))))
      syntaxClass0037)
  let syntaxFormula0049 : Wff := (.classMem syntaxClass0047 syntaxClass0037)
  let syntaxFormula0050 : Wff := (.classMem syntaxClass0047 syntaxClass0023)
  let syntaxFormula0051 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv z) (syn_csn (syn_csn (.cv y)))))
      syntaxClass0034)
  let syntaxFormula0052 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0051)
  let syntaxFormula0053 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv w))))) syntaxFormula0051)
  let syntaxFormula0054 : Wff := (syn_wex w syntaxFormula0053)
  let syntaxFormula0055 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0051)
  let syntaxFormula0056 : Wff := (syn_wex t syntaxFormula0053)
  let syntaxFormula0057 : Wff := (syn_wex w syntaxFormula0056)
  let syntaxClass0058 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (.cv w))))
      (syn_copk (.cv z) (syn_csn (syn_csn (.cv y)))))
  let syntaxFormula0059 : Wff := (.classMem syntaxClass0058 syntaxClass0034)
  let syntaxFormula0060 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv w) (syn_csn (.cv y)))) syntaxClass0029)
  let syntaxFormula0061 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0060)
  let syntaxFormula0062 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))) syntaxFormula0060)
  let syntaxFormula0063 : Wff := (syn_wex a syntaxFormula0062)
  let syntaxFormula0064 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0060)
  let syntaxFormula0065 : Wff := (syn_wex t syntaxFormula0062)
  let syntaxFormula0066 : Wff := (syn_wex a syntaxFormula0065)
  let syntaxClass0067 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (.cv w) (syn_csn (.cv y))))
  let syntaxFormula0068 : Wff := (.classMem syntaxClass0067 syntaxClass0029)
  let syntaxFormula0069 : Wff := (.classMem syntaxClass0067 (syn_cins3k (syn_cssetk)))
  let syntaxFormula0070 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv a) (.cv y))) syntaxClass0025)
  let syntaxFormula0071 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0070)
  let syntaxFormula0072 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) syntaxFormula0070)
  let syntaxFormula0073 : Wff := (syn_wex x syntaxFormula0072)
  let syntaxFormula0074 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0070)
  let syntaxFormula0075 : Wff := (syn_wex t syntaxFormula0072)
  let syntaxFormula0076 : Wff := (syn_wex x syntaxFormula0075)
  let syntaxFormula0077 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv a) (.cv y)))
      syntaxClass0025)
  let syntaxFormula0078 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv a) (.cv y)))
      (syn_cins2k (syn_cssetk)))
  let syntaxFormula0079 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv a) (.cv y)))
      syntaxClass0024)
  let syntaxFormula0080 : Wff := (.classMem (syn_copk (.cv a) (.cv y)) syntaxClass0026)
  let syntaxFormula0081 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv a)) (syn_csn (.cv y))) syntaxClass0027)
  let syntaxFormula0082 : Wff := (.classMem syntaxClass0067 syntaxClass0028)
  let syntaxFormula0083 : Wff := (syn_wb syntaxFormula0069 syntaxFormula0082)
  let syntaxFormula0084 : Wff :=
    (.classMem (syn_copk (.cv w) (syn_csn (.cv y))) syntaxClass0030)
  let syntaxFormula0085 : Wff :=
    (.classEq (.cv w) (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))))
  let syntaxFormula0086 : Wff :=
    (.classMem (syn_copk (.cv w) (syn_csn (.cv y))) syntaxClass0031)
  let syntaxFormula0087 : Wff := (.classMem syntaxClass0058 syntaxClass0033)
  let syntaxFormula0088 : Wff := (.classMem syntaxClass0058 (syn_cins3k (syn_cssetk)))
  let syntaxFormula0089 : Wff :=
    (.classMem (syn_copk (.cv z) (syn_csn (syn_csn (.cv y)))) syntaxClass0035)
  let syntaxFormula0090 : Wff :=
    (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) (.cv z))
  let syntaxFormula0091 : Wff := (.classMem syntaxClass0047 syntaxClass0036)
  let syntaxFormula0092 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z)))) syntaxFormula0048)
  let syntaxFormula0093 : Wff := (syn_wex t syntaxFormula0092)
  let syntaxFormula0094 : Wff :=
    (syn_wa (.classEq (.cv z) (syn_ctfin (.cv n))) syntaxFormula0090)
  let syntaxFormula0095 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) syntaxFormula0048)
  let syntaxFormula0096 : Wff := (syn_wex z syntaxFormula0092)
  let syntaxFormula0097 : Wff := (syn_wrex t (syn_cpw1 (syn_c1c)) syntaxFormula0048)
  let syntaxFormula0098 : Wff := (syn_wex z syntaxFormula0093)
  let syntaxFormula0099 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))) syntaxClass0038)
  let syntaxFormula0100 : Wff :=
    (.classMem (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_ctfin (.cv n)))
  let syntaxFormula0101 : Wff := (.neg syntaxFormula0099)
  let syntaxFormula0102 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))) syntaxClass0039)
  let syntaxFormula0103 : Wff := (.imp (syn_wss (.cv y) (syn_cnnc)) syntaxFormula0100)
  let syntaxFormula0104 : Wff := (.neg syntaxFormula0103)
  let syntaxFormula0105 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv y)))) syntaxFormula0043)
  let syntaxFormula0106 : Wff := (syn_wex t syntaxFormula0105)
  let syntaxFormula0107 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) syntaxFormula0043)
  let syntaxFormula0108 : Wff := (syn_wex y syntaxFormula0105)
  let syntaxFormula0109 : Wff := (syn_wrex t (syn_cpw1 (syn_c1c)) syntaxFormula0043)
  let syntaxFormula0110 : Wff := (syn_wex y syntaxFormula0106)
  let syntaxFormula0111 : Wff := (.classMem (syn_csn (.cv n)) syntaxClass0041)
  let syntaxFormula0112 : Wff := (syn_wrex y (.cv n) syntaxFormula0104)
  let syntaxFormula0113 : Wff := (.classMem (syn_csn (.cv n)) syntaxClass0042)
  let syntaxFormula0114 : Wff := (syn_wral y (.cv n) syntaxFormula0103)
  let syntaxClass0115 : Class := (syn_cuni1 syntaxClass0042)
  have p0000 := @g_vex n
  have p0001 := @g_eluni1 (.cv n) syntaxClass0042 p0000
  have p0002 := @g_snex (syn_csn (.cv y))
  have p0003 := @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))
  have p0004 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))
      (syn_copk (.cv t) (syn_csn (.cv n)))
      (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))) syntaxClass0040 p0003
  have p0005 :=
    @g_ceqsexv syntaxFormula0043 syntaxFormula0044 t (syn_csn (syn_csn (.cv y)))
      dv_cache_0001 dv_cache_0002 p0002 p0004
  have p0006 :=
    @g_elin (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)))
      (syn_csik (syn_cssetk)) syntaxClass0039
  have p0007 := @g_snex (.cv y)
  have p0008 := @g_opksnelsik (syn_csn (.cv y)) (.cv n) (syn_cssetk) p0007 p0000
  have p0009 := @g_vex y
  have p0010 := @g_elssetk (.cv y) (.cv n) p0009 p0000
  have p0011_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv y)) (.cv n)) (syn_cssetk)) (.objMem y n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv n)) (syn_cssetk)) (.objMem y n) p0008
      p0011_e01_recanon
  have p0012 :=
    @g_eldif (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)))
      (syn_csik (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv))) syntaxClass0038
  have p0013 :=
    @g_opksnelsik (syn_csn (.cv y)) (.cv n)
      (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv)) p0007 p0000
  have p0014 :=
    @g_opkelxpk (syn_csn (.cv y)) (.cv n) (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv) p0007
      p0000
  have p0015 :=
    @g_mpbiran2 syntaxFormula0045
      (.classMem (syn_csn (.cv y)) (syn_cpw1 (syn_cpw (syn_cnnc))))
      (.classMem (.cv n) (syn_cvv)) p0000 p0014
  have p0016 := @g_snelpw1 (.cv y) (syn_cpw (syn_cnnc))
  have p0017 :=
    @g_bitri syntaxFormula0045
      (.classMem (syn_csn (.cv y)) (syn_cpw1 (syn_cpw (syn_cnnc))))
      (.classMem (.cv y) (syn_cpw (syn_cnnc))) p0015 p0016
  have p0018 := @g_elpw (.cv y) (syn_cnnc) p0009
  have p0019 :=
    @g_n_3bitri syntaxFormula0046 syntaxFormula0045
      (.classMem (.cv y) (syn_cpw (syn_cnnc))) (syn_wss (.cv y) (syn_cnnc)) p0013 p0017
      p0018
  have p0020 := @g_snex (syn_csn (.cv z))
  have p0021 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv z)))
      (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)))
  have p0022 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
      (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))))
      syntaxClass0047 syntaxClass0037 p0021
  have p0023 :=
    @g_ceqsexv syntaxFormula0048 syntaxFormula0049 t (syn_csn (syn_csn (.cv z)))
      dv_cache_0003 dv_cache_0004 p0020 p0022
  have p0024 := @g_elin syntaxClass0047 syntaxClass0023 syntaxClass0036
  have p0025 := @g_vex z
  have p0026 := @g_snex (.cv n)
  have p0027 :=
    @g_otkelins2k (.cv z) (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)) syntaxClass0022
      p0025 p0002 p0026
  have p0028 := @g_opkelcnvk (.cv z) (syn_csn (.cv n)) syntaxClass0021 p0025 p0026
  have p0029 := @g_eqtfinrelk (.cv n) (.cv z) p0000 p0025
  have p0030 :=
    @g_n_3bitri syntaxFormula0050
      (.classMem (syn_copk (.cv z) (syn_csn (.cv n))) syntaxClass0022)
      (.classMem (syn_copk (syn_csn (.cv n)) (.cv z)) syntaxClass0021)
      (.classEq (.cv z) (syn_ctfin (.cv n))) p0027 p0028 p0029
  have p0031 := @g_opkex (.cv z) (syn_csn (syn_csn (.cv y)))
  have p0032 :=
    @g_elimak t syntaxClass0034 (syn_cpw1 (syn_cpw1 (syn_c1c)))
      (syn_copk (.cv z) (syn_csn (syn_csn (.cv y)))) dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0031
  have p0033 := @g_elpw121c w (.cv t) dv_cache_0008
  have p0034 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex w (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv w))))))
      syntaxFormula0051 p0033
  have p0035 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv w))))) syntaxFormula0051
      w dv_cache_0009
  have p0036 :=
    @g_bitr4i syntaxFormula0052
      (syn_wa (syn_wex w (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv w))))))
        syntaxFormula0051)
      syntaxFormula0054 p0034 p0035
  have p0037 := @g_exbii syntaxFormula0052 syntaxFormula0054 t p0036
  have p0038 := (Nominal.biimpRefl syntaxFormula0055)
  have p0039 := @g_excom syntaxFormula0053 w t
  have p0040 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0052) (syn_wex t syntaxFormula0054)
      syntaxFormula0055 syntaxFormula0057 p0037 p0038 p0039
  have p0041 := @g_snex (syn_csn (syn_csn (.cv w)))
  have p0042 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv w))))
      (syn_copk (.cv z) (syn_csn (syn_csn (.cv y))))
  have p0043 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv w)))))
      (syn_copk (.cv t) (syn_copk (.cv z) (syn_csn (syn_csn (.cv y))))) syntaxClass0058
      syntaxClass0034 p0042
  have p0044 :=
    @g_ceqsexv syntaxFormula0051 syntaxFormula0059 t (syn_csn (syn_csn (syn_csn (.cv w))))
      dv_cache_0010 dv_cache_0011 p0041 p0043
  have p0045 := @g_elin syntaxClass0058 syntaxClass0033 (syn_cins3k (syn_cssetk))
  have p0046 := @g_snex (.cv w)
  have p0047 :=
    @g_otkelins2k (syn_csn (.cv w)) (.cv z) (syn_csn (syn_csn (.cv y))) syntaxClass0032
      p0046 p0025 p0002
  have p0048 := @g_vex w
  have p0049 := @g_opksnelsik (.cv w) (syn_csn (.cv y)) syntaxClass0031 p0048 p0007
  have p0050 := @g_opkex (.cv w) (syn_csn (.cv y))
  have p0051 :=
    @g_elimak t syntaxClass0029 (syn_cpw1 (syn_cpw1 (syn_c1c)))
      (syn_copk (.cv w) (syn_csn (.cv y))) dv_cache_0012 dv_cache_0006 dv_cache_0013 p0050
  have p0052 := @g_elpw121c a (.cv t) dv_cache_0014
  have p0053 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))))
      syntaxFormula0060 p0052
  have p0054 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))) syntaxFormula0060
      a dv_cache_0015
  have p0055 :=
    @g_bitr4i syntaxFormula0061
      (syn_wa (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))))
        syntaxFormula0060)
      syntaxFormula0063 p0053 p0054
  have p0056 := @g_exbii syntaxFormula0061 syntaxFormula0063 t p0055
  have p0057 := (Nominal.biimpRefl syntaxFormula0064)
  have p0058 := @g_excom syntaxFormula0062 a t
  have p0059 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0061) (syn_wex t syntaxFormula0063)
      syntaxFormula0064 syntaxFormula0066 p0056 p0057 p0058
  have p0060 := @g_snex (syn_csn (syn_csn (.cv a)))
  have p0061 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))
      (syn_copk (.cv w) (syn_csn (.cv y)))
  have p0062 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a)))))
      (syn_copk (.cv t) (syn_copk (.cv w) (syn_csn (.cv y)))) syntaxClass0067
      syntaxClass0029 p0061
  have p0063 :=
    @g_ceqsexv syntaxFormula0060 syntaxFormula0068 t (syn_csn (syn_csn (syn_csn (.cv a))))
      dv_cache_0016 dv_cache_0017 p0060 p0062
  have p0064 := @g_elsymdif syntaxClass0067 (syn_cins3k (syn_cssetk)) syntaxClass0028
  have p0065 := @g_snex (.cv a)
  have p0066 :=
    @g_otkelins3k (syn_csn (.cv a)) (.cv w) (syn_csn (.cv y)) (syn_cssetk) p0065 p0048
      p0007
  have p0067 := @g_vex a
  have p0068 := @g_elssetk (.cv a) (.cv w) p0067 p0048
  have p0069_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv a)) (.cv w)) (syn_cssetk)) (.objMem a w)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
    @g_bitri syntaxFormula0069
      (.classMem (syn_copk (syn_csn (.cv a)) (.cv w)) (syn_cssetk)) (.objMem a w) p0066
      p0069_e01_recanon
  have p0070 :=
    @g_otkelins2k (syn_csn (.cv a)) (.cv w) (syn_csn (.cv y)) syntaxClass0027 p0065 p0048
      p0007
  have p0071 := @g_opkex (.cv a) (.cv y)
  have p0072 :=
    @g_elimak t syntaxClass0025 (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv a) (.cv y))
      dv_cache_0018 dv_cache_0006 dv_cache_0019 p0071
  have p0073 := @g_elpw121c x (.cv t) dv_cache_0020
  have p0074 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
      syntaxFormula0070 p0073
  have p0075 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))) syntaxFormula0070
      x dv_cache_0021
  have p0076 :=
    @g_bitr4i syntaxFormula0071
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
        syntaxFormula0070)
      syntaxFormula0073 p0074 p0075
  have p0077 := @g_exbii syntaxFormula0071 syntaxFormula0073 t p0076
  have p0078 := (Nominal.biimpRefl syntaxFormula0074)
  have p0079 := @g_excom syntaxFormula0072 x t
  have p0080 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0071) (syn_wex t syntaxFormula0073)
      syntaxFormula0074 syntaxFormula0076 p0077 p0078 p0079
  have p0081 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0082 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv a) (.cv y))
  have p0083 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (.cv t) (syn_copk (.cv a) (.cv y)))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv a) (.cv y)))
      syntaxClass0025 p0082
  have p0084 :=
    @g_ceqsexv syntaxFormula0070 syntaxFormula0077 t (syn_csn (syn_csn (syn_csn (.cv x))))
      dv_cache_0022 dv_cache_0023 p0081 p0083
  have p0085 :=
    @g_elin (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (.cv a) (.cv y)))
      (syn_cins2k (syn_cssetk)) syntaxClass0024
  have p0086 := @g_snex (.cv x)
  have p0087 :=
    @g_otkelins2k (syn_csn (.cv x)) (.cv a) (.cv y) (syn_cssetk) p0086 p0067 p0009
  have p0088 := @g_vex x
  have p0089 := @g_elssetk (.cv x) (.cv y) p0088 p0009
  have p0090_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
    @g_bitri syntaxFormula0078
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y) p0087
      p0090_e01_recanon
  have p0091 :=
    @g_otkelins3k (syn_csn (.cv x)) (.cv a) (.cv y) syntaxClass0021 p0086 p0067 p0009
  have p0092 := @g_eqtfinrelk (.cv x) (.cv a) p0088 p0067
  have p0093 :=
    @g_bitri syntaxFormula0079
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) syntaxClass0021)
      (.classEq (.cv a) (syn_ctfin (.cv x))) p0091 p0092
  have p0094 :=
    @g_anbi12i syntaxFormula0078 (.objMem x y) syntaxFormula0079
      (.classEq (.cv a) (syn_ctfin (.cv x))) p0090 p0093
  have p0095 :=
    @g_n_3bitri syntaxFormula0075 syntaxFormula0077
      (syn_wa syntaxFormula0078 syntaxFormula0079)
      (syn_wa (.objMem x y) (.classEq (.cv a) (syn_ctfin (.cv x)))) p0084 p0085 p0094
  have p0096 :=
    @g_exbii syntaxFormula0075
      (syn_wa (.objMem x y) (.classEq (.cv a) (syn_ctfin (.cv x)))) x p0095
  have p0097 :=
    @g_n_3bitri syntaxFormula0080 syntaxFormula0074 syntaxFormula0076
      (syn_wex x (syn_wa (.objMem x y) (.classEq (.cv a) (syn_ctfin (.cv x))))) p0072
      p0080 p0096
  have p0098 := @g_opksnelsik (.cv a) (.cv y) syntaxClass0026 p0067 p0009
  have p0099 :=
    (Nominal.biimpRefl (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
  have p0100_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))
        (syn_wex x (syn_wa (.objMem x y) (.classEq (.cv a) (syn_ctfin (.cv x)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_ctfin, syn_cif, syn_wo, syn_c0,
          syn_cdif, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_cvv, syn_cio, syn_cuni,
          syn_csn]
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
    @g_n_3bitr4i syntaxFormula0080
      (syn_wex x (syn_wa (.objMem x y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      syntaxFormula0081 (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))) p0097
      p0098 p0100_e02_recanon
  have p0101 :=
    @g_bitri syntaxFormula0082 syntaxFormula0081
      (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))) p0070 p0100
  have p0102 :=
    @g_bibi12i syntaxFormula0069 (.objMem a w) syntaxFormula0082
      (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))) p0069 p0101
  have p0103 :=
    @g_notbii syntaxFormula0083
      (syn_wb (.objMem a w) (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      p0102
  have p0104 :=
    @g_n_3bitri syntaxFormula0065 syntaxFormula0068 (.neg syntaxFormula0083)
      (.neg (syn_wb (.objMem a w) (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      p0063 p0064 p0103
  have p0105 :=
    @g_exbii syntaxFormula0065
      (.neg (syn_wb (.objMem a w) (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      a p0104
  have p0106 :=
    @g_n_3bitri syntaxFormula0084 syntaxFormula0064 syntaxFormula0066
      (syn_wex a (.neg (syn_wb (.objMem a w)
            (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      p0051 p0059 p0105
  have p0107 :=
    @g_notbii syntaxFormula0084
      (syn_wex a (.neg (syn_wb (.objMem a w)
            (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      p0106
  have p0108 := @g_elcompl (syn_copk (.cv w) (syn_csn (.cv y))) syntaxClass0030 p0050
  have p0109 :=
    @g_eqabb (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))) a (.cv w)
      dv_cache_0024
  have p0110 :=
    @g_alex
      (syn_wb (.objMem a w) (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) a
  have p0111_e00_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0085 (.all a (syn_wb (.objMem a w)
            (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_ctfin, syn_cif, syn_wo, syn_c0,
          syn_cdif, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_cvv, syn_cio, syn_cuni,
          syn_csn]
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
    @g_bitri syntaxFormula0085
      (.all a (syn_wb (.objMem a w)
          (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      (.neg (syn_wex a (.neg (syn_wb (.objMem a w)
              (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))))))
      p0111_e00_recanon p0110
  have p0112 :=
    @g_n_3bitr4i (.neg syntaxFormula0084)
      (.neg (syn_wex a (.neg (syn_wb (.objMem a w)
              (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))))))
      syntaxFormula0086 syntaxFormula0085 p0107 p0108 p0111
  have p0113 :=
    @g_n_3bitri syntaxFormula0087
      (.classMem (syn_copk (syn_csn (.cv w)) (syn_csn (syn_csn (.cv y)))) syntaxClass0032)
      syntaxFormula0086 syntaxFormula0085 p0047 p0049 p0112
  have p0114 :=
    @g_otkelins3k (syn_csn (.cv w)) (.cv z) (syn_csn (syn_csn (.cv y))) (syn_cssetk) p0046
      p0025 p0002
  have p0115 := @g_elssetk (.cv w) (.cv z) p0048 p0025
  have p0116_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv w)) (.cv z)) (syn_cssetk)) (.objMem w z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin, syn_wnan, syn_wa,
          syn_ccompl, syn_csn, syn_cssetk, syn_wex]
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
    @g_bitri syntaxFormula0088
      (.classMem (syn_copk (syn_csn (.cv w)) (.cv z)) (syn_cssetk)) (.objMem w z) p0114
      p0116_e01_recanon
  have p0117 :=
    @g_anbi12i syntaxFormula0087 syntaxFormula0085 syntaxFormula0088 (.objMem w z) p0113
      p0116
  have p0118 :=
    @g_n_3bitri syntaxFormula0056 syntaxFormula0059
      (syn_wa syntaxFormula0087 syntaxFormula0088)
      (syn_wa syntaxFormula0085 (.objMem w z)) p0044 p0045 p0117
  have p0119 :=
    @g_exbii syntaxFormula0056 (syn_wa syntaxFormula0085 (.objMem w z)) w p0118
  have p0120 :=
    @g_n_3bitri syntaxFormula0089 syntaxFormula0055 syntaxFormula0057
      (syn_wex w (syn_wa syntaxFormula0085 (.objMem w z))) p0032 p0040 p0119
  have p0121 :=
    @g_otkelins3k (.cv z) (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)) syntaxClass0035
      p0025 p0002 p0026
  have p0122 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV w
      (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x))))) (.cv z)
      dv_cache_0025 dv_cache_0026)
  have p0123_e02_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0090 (syn_wex w (syn_wa syntaxFormula0085 (.objMem w z)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_ctfin, syn_cif, syn_wo, syn_c0,
          syn_cdif, syn_cin, syn_ccompl, syn_cnin, syn_wnan, syn_cvv, syn_cio, syn_cuni,
          syn_csn]
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
    @g_n_3bitr4i syntaxFormula0089 (syn_wex w (syn_wa syntaxFormula0085 (.objMem w z)))
      syntaxFormula0091 syntaxFormula0090 p0120 p0121 p0123_e02_recanon
  have p0124 :=
    @g_anbi12i syntaxFormula0050 (.classEq (.cv z) (syn_ctfin (.cv n))) syntaxFormula0091
      syntaxFormula0090 p0030 p0123
  have p0125 :=
    @g_n_3bitri syntaxFormula0093 syntaxFormula0049
      (syn_wa syntaxFormula0050 syntaxFormula0091) syntaxFormula0094 p0023 p0024 p0124
  have p0126 := @g_exbii syntaxFormula0093 syntaxFormula0094 z p0125
  have p0127 := @g_opkex (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))
  have p0128 :=
    @g_elimak t syntaxClass0037 (syn_cpw1 (syn_c1c))
      (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n))) dv_cache_0027 dv_cache_0028
      dv_cache_0029 p0127
  have p0129 := @g_elpw11c z (.cv t) dv_cache_0030
  have p0130 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))) syntaxFormula0048 p0129
  have p0131 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv z)))) syntaxFormula0048 z
      dv_cache_0031
  have p0132 :=
    @g_bitr4i syntaxFormula0095
      (syn_wa (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))) syntaxFormula0048)
      syntaxFormula0096 p0130 p0131
  have p0133 := @g_exbii syntaxFormula0095 syntaxFormula0096 t p0132
  have p0134 := (Nominal.biimpRefl syntaxFormula0097)
  have p0135 := @g_excom syntaxFormula0092 z t
  have p0136 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0095) (syn_wex t syntaxFormula0096)
      syntaxFormula0097 syntaxFormula0098 p0133 p0134 p0135
  have p0137 := @g_bitri syntaxFormula0099 syntaxFormula0097 syntaxFormula0098 p0128 p0136
  have p0138 := @g_tfinex (.cv n)
  have p0139 :=
    @g_clel3 z (.cab a (syn_wrex x (.cv y) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_ctfin (.cv n)) dv_cache_0032 dv_cache_0033 p0138
  have p0140 :=
    @g_n_3bitr4i syntaxFormula0098 (syn_wex z syntaxFormula0094) syntaxFormula0099
      syntaxFormula0100 p0126 p0137 p0139
  have p0141 := @g_notbii syntaxFormula0099 syntaxFormula0100 p0140
  have p0142 :=
    @g_anbi12i syntaxFormula0046 (syn_wss (.cv y) (syn_cnnc)) syntaxFormula0101
      (.neg syntaxFormula0100) p0019 p0141
  have p0143 := @g_annim (syn_wss (.cv y) (syn_cnnc)) syntaxFormula0100
  have p0144 :=
    @g_n_3bitri syntaxFormula0102 (syn_wa syntaxFormula0046 syntaxFormula0101)
      (syn_wa (syn_wss (.cv y) (syn_cnnc)) (.neg syntaxFormula0100)) syntaxFormula0104
      p0012 p0142 p0143
  have p0145 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)))
        (syn_csik (syn_cssetk)))
      (.objMem y n) syntaxFormula0102 syntaxFormula0104 p0011 p0144
  have p0146 :=
    @g_n_3bitri syntaxFormula0106 syntaxFormula0044
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_csn (.cv n)))
          (syn_csik (syn_cssetk))) syntaxFormula0102)
      (syn_wa (.objMem y n) syntaxFormula0104) p0005 p0006 p0145
  have p0147 :=
    @g_exbii syntaxFormula0106 (syn_wa (.objMem y n) syntaxFormula0104) y p0146
  have p0148 :=
    @g_elimak t syntaxClass0040 (syn_cpw1 (syn_c1c)) (syn_csn (.cv n)) dv_cache_0034
      dv_cache_0028 dv_cache_0035 p0026
  have p0149 := @g_elpw11c y (.cv t) dv_cache_0036
  have p0150 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))) syntaxFormula0043 p0149
  have p0151 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv y)))) syntaxFormula0043 y
      dv_cache_0037
  have p0152 :=
    @g_bitr4i syntaxFormula0107
      (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))) syntaxFormula0043)
      syntaxFormula0108 p0150 p0151
  have p0153 := @g_exbii syntaxFormula0107 syntaxFormula0108 t p0152
  have p0154 := (Nominal.biimpRefl syntaxFormula0109)
  have p0155 := @g_excom syntaxFormula0105 y t
  have p0156 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0107) (syn_wex t syntaxFormula0108)
      syntaxFormula0109 syntaxFormula0110 p0153 p0154 p0155
  have p0157 := @g_bitri syntaxFormula0111 syntaxFormula0109 syntaxFormula0110 p0148 p0156
  have p0158 := (Nominal.biimpRefl syntaxFormula0112)
  have p0159_e02_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0112 (syn_wex y (syn_wa (.objMem y n) syntaxFormula0104))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wex, syn_wa]
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
    @g_n_3bitr4i syntaxFormula0110 (syn_wex y (syn_wa (.objMem y n) syntaxFormula0104))
      syntaxFormula0111 syntaxFormula0112 p0147 p0157 p0159_e02_recanon
  have p0160 := @g_notbii syntaxFormula0111 syntaxFormula0112 p0159
  have p0161 := @g_elcompl (syn_csn (.cv n)) syntaxClass0041 p0026
  have p0162 := @g_dfral2 syntaxFormula0103 y (.cv n)
  have p0163 :=
    @g_n_3bitr4i (.neg syntaxFormula0111) (.neg syntaxFormula0112) syntaxFormula0113
      syntaxFormula0114 p0160 p0161 p0162
  have p0164 :=
    @g_bitri (.classMem (.cv n) syntaxClass0115) syntaxFormula0113 syntaxFormula0114 p0001
      p0163
  have p0165 := @g_eqabi syntaxFormula0114 n syntaxClass0115 dv_cache_0038 p0164
  have p0166 := @g_ssetkex
  have p0167 := @g_sikex (syn_cssetk) p0166
  have p0168 := @g_nncex
  have p0169 := @g_pwex (syn_cnnc) p0168
  have p0170 := @g_pw1ex (syn_cpw (syn_cnnc)) p0169
  have p0171 := @g_vvex
  have p0172 := @g_xpkex (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv) p0170 p0171
  have p0173 := @g_sikex (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv)) p0172
  have p0174 := @g_tfinrelkex
  have p0175 := @g_cnvkex syntaxClass0021 p0174
  have p0176 := @g_ins2kex syntaxClass0022 p0175
  have p0178 := @g_ins3kex (syn_cssetk) p0166
  have p0180 := @g_ins2kex (syn_cssetk) p0166
  have p0182 := @g_ins3kex syntaxClass0021 p0174
  have p0183 := @g_inex (syn_cins2k (syn_cssetk)) syntaxClass0024 p0180 p0182
  have p0184 := @g_n_1cex
  have p0185 := @g_pw1ex (syn_c1c) p0184
  have p0186 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0185
  have p0187 := @g_imakex syntaxClass0025 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0183 p0186
  have p0188 := @g_sikex syntaxClass0026 p0187
  have p0189 := @g_ins2kex syntaxClass0027 p0188
  have p0190 := @g_symdifex (syn_cins3k (syn_cssetk)) syntaxClass0028 p0178 p0189
  have p0191 := @g_imakex syntaxClass0029 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0190 p0186
  have p0192 := @g_complex syntaxClass0030 p0191
  have p0193 := @g_sikex syntaxClass0031 p0192
  have p0194 := @g_ins2kex syntaxClass0032 p0193
  have p0195 := @g_inex syntaxClass0033 (syn_cins3k (syn_cssetk)) p0194 p0178
  have p0196 := @g_imakex syntaxClass0034 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0195 p0186
  have p0197 := @g_ins3kex syntaxClass0035 p0196
  have p0198 := @g_inex syntaxClass0023 syntaxClass0036 p0176 p0197
  have p0199 := @g_imakex syntaxClass0037 (syn_cpw1 (syn_c1c)) p0198 p0185
  have p0200 :=
    @g_difex (syn_csik (syn_cxpk (syn_cpw1 (syn_cpw (syn_cnnc))) (syn_cvv)))
      syntaxClass0038 p0173 p0199
  have p0201 := @g_inex (syn_csik (syn_cssetk)) syntaxClass0039 p0167 p0200
  have p0202 := @g_imakex syntaxClass0040 (syn_cpw1 (syn_c1c)) p0201 p0185
  have p0203 := @g_complex syntaxClass0041 p0202
  have p0204 := @g_uni1ex syntaxClass0042 p0203
  have p0205 :=
    @g_eqeltrri syntaxClass0115 (.cab n syntaxFormula0114) (syn_cvv) p0165 p0204
  exact p0205


end NFChoice.DirectNominalPrf.WPPReplay

end
