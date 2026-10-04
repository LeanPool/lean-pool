/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk010Compact001Part003

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part004`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_evenodddisj`. -/
@[expose]
noncomputable def gEvenodddisj :
    Nominal.NPrf (.classEq (synCin (synCevenfin) (synCoddfin)) (synC0)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let k : Var := freshVar proofSupport 1
  let n : Var := freshVar proofSupport 2
  let j : Var := freshVar proofSupport 3
  let m : Var := freshVar proofSupport 4
  let p : Var := freshVar proofSupport 5
  let q : Var := freshVar proofSupport 6
  have fresh_x_ne_k : x ≠ k :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_k_ne_x : k ≠ x := Ne.symm fresh_x_ne_k
  have fresh_x_ne_n : x ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_n_ne_x : n ≠ x := Ne.symm fresh_x_ne_n
  have fresh_k_ne_n : k ≠ n :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_n_ne_k : n ≠ k := Ne.symm fresh_k_ne_n
  have fresh_k_ne_j : k ≠ j :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_j_ne_k : j ≠ k := Ne.symm fresh_k_ne_j
  have fresh_n_ne_j : n ≠ j :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_j_ne_n : j ≠ n := Ne.symm fresh_n_ne_j
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_n_ne_p : n ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_p_ne_n : p ≠ n := Ne.symm fresh_n_ne_p
  have fresh_n_ne_q : n ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_q_ne_n : q ≠ n := Ne.symm fresh_n_ne_q
  have fresh_j_ne_m : j ≠ m :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_m_ne_j : m ≠ j := Ne.symm fresh_j_ne_m
  have fresh_j_ne_p : j ≠ p :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_m_ne_p : m ≠ p :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_p_ne_m : p ≠ m := Ne.symm fresh_m_ne_p
  have fresh_m_ne_q : m ≠ q :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 4) (j := 6) (by decide)
  have fresh_q_ne_m : q ≠ m := Ne.symm fresh_m_ne_q
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have dv_cache_0001 : k ≠ x := by exact (show k ≠ x from (by exact fresh_k_ne_x))
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : j ≠ n :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show j ≠ n from (by exact fresh_j_ne_n))
  have dv_cache_0004 : n ∉ ((Wff.classEq (.cv j) (synC0c))).fv :=
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
          Finset.mem_singleton, fresh_n_ne_j, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : n ∉ ((Wff.objEq j m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_j, fresh_n_ne_m, or_false, not_false_eq_true])
  have dv_cache_0006 : n ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 : p ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 :
    p ∉
      ((Wff.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m))
            (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_n, fresh_p_ne_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0009 :
    n ∉
      ((Wff.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m))
            (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_p, fresh_n_ne_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0010 : n ∉ ((Wff.classEq (.cv j) (synCplc (.cv m) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
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
          Finset.mem_singleton, fresh_n_ne_j, fresh_n_ne_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0011 : n ∉ ((Wff.objEq j k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_j, fresh_n_ne_k, or_false, not_false_eq_true])
  have dv_cache_0012 : q ∉ ((Class.cv n)).fv :=
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
          fresh_q_ne_n, not_false_eq_true])
  have dv_cache_0013 : p ∉ ((Class.cv q)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_q, not_false_eq_true])
  have dv_cache_0014 :
    p ∉
      ((Wff.imp (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m))
            (synCplc (synCplc (.cv q) (.cv q)) (synC1c))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_q, fresh_p_ne_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0015 :
    q ∉
      ((Wff.imp (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWne
                  (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
                  (synC0))) (synWral p (synCnnc)
                (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
                  (synWne (synCplc (.cv m) (.cv m))
                    (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
          (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
            (synCplc (.cv n) (.cv n))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_ne_m, fresh_q_ne_p,
          fresh_q_ne_n, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0016 :
    n ∉
      ((synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_p, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0017 : j ∉ ((Class.cv k)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_j_ne_k, not_false_eq_true])
  have dv_cache_0018 :
    j ∉
      ((Wff.imp (synWne (synCplc (.cv m) (.cv m)) (synC0)) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_j_ne_m, fresh_j_ne_p,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0019 :
    m ∉
      ((Wff.imp (synWne (synCplc (.cv j) (.cv j)) (synC0)) (synWral n (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
              (synWne (synCplc (.cv j) (.cv j))
                (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_ne_j, fresh_m_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0020 :
    j ∉
      ((Wff.imp (synWne (synC0c) (synC0)) (synWral n (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
              (synWne (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_j_ne_n, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0021 :
    j ∉
      ((Wff.imp (synWne (synCplc (.cv k) (.cv k)) (synC0)) (synWral n (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
              (synWne (synCplc (.cv k) (.cv k))
                (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_j_ne_k, fresh_j_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0022 :
    j ∉
      ((Wff.imp (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0)) (synWral n (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) (synWne
                (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
                (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_j_ne_m, fresh_j_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0023 : j ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact (show j ≠ m from (by exact fresh_j_ne_m))
  have dv_cache_0024 : n ∉ ((Wff.classEq (.cv x) (synCplc (.cv k) (.cv k)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_x, fresh_n_ne_k, or_false, not_false_eq_true])
  have dv_cache_0025 :
    k ∉
      ((Wff.neg (synWrex n (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
              (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : k ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_k_ne_x, fresh_k_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @gDfevenfin2 x k dv_cache_0001
  have p0001 := @gDfoddfin2 x n dv_cache_0002
  have p0002 :=
    @gIneq12i (synCevenfin)
      (.cab x (synWrex k (synCnnc) (synWa (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
            (synWne (synCplc (.cv k) (.cv k)) (synC0)))))
      (synCoddfin)
      (.cab x (synWrex n (synCnnc)
          (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))
      p0000 p0001
  have p0003 :=
    @gInab
      (synWrex k (synCnnc) (synWa (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
          (synWne (synCplc (.cv k) (.cv k)) (synC0))))
      (synWrex n (synCnnc)
        (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      x
  have p0004 :=
    @gEqtri (synCin (synCevenfin) (synCoddfin))
      (synCin (.cab x (synWrex k (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
              (synWne (synCplc (.cv k) (.cv k)) (synC0))))) (.cab x (synWrex n (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
              (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))))
      (.cab x (synWa (synWrex k (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
              (synWne (synCplc (.cv k) (.cv k)) (synC0)))) (synWrex n (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
              (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))))
      p0002 p0003
  have p0005 := @gEvenodddisjlem1 j n dv_cache_0003
  have p0006 := @gAddceq12 (.cv j) (.cv j) (synC0c) (synC0c)
  have p0007 :=
    @gAnidms (.classEq (.cv j) (synC0c))
      (.classEq (synCplc (.cv j) (.cv j)) (synCplc (synC0c) (synC0c))) p0006
  have p0008 := @gAddcid2 (synC0c)
  have p0009 :=
    @gSyl6eq (.classEq (.cv j) (synC0c)) (synCplc (.cv j) (.cv j))
      (synCplc (synC0c) (synC0c)) (synC0c) p0007 p0008
  have p0010 :=
    @gNeeq1d (.classEq (.cv j) (synC0c)) (synCplc (.cv j) (.cv j)) (synC0c) (synC0)
      p0009
  have p0011 :=
    @gNeeq1d (.classEq (.cv j) (synC0c)) (synCplc (.cv j) (.cv j)) (synC0c)
      (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) p0009
  have p0012 :=
    @gImbi2d (.classEq (.cv j) (synC0c))
      (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) p0011
  have p0013 :=
    @gRalbidv (.classEq (.cv j) (synC0c))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      n (synCnnc) dv_cache_0004 p0012
  have p0014 :=
    @gImbi12d (.classEq (.cv j) (synC0c)) (synWne (synCplc (.cv j) (.cv j)) (synC0))
      (synWne (synC0c) (synC0))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      p0010 p0013
  have p0015 := @gAddceq12 (.cv j) (.cv j) (.cv m) (.cv m)
  have p0016_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq j m) (.objEq j m))
        (.classEq (synCplc (.cv j) (.cv j)) (synCplc (.cv m) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCplc synWrex synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0015
  have p0016 :=
    @gAnidms (.objEq j m)
      (.classEq (synCplc (.cv j) (.cv j)) (synCplc (.cv m) (.cv m))) p0016_e00_recanon
  have p0017 :=
    @gNeeq1d (.objEq j m) (synCplc (.cv j) (.cv j)) (synCplc (.cv m) (.cv m)) (synC0)
      p0016
  have p0018 :=
    @gNeeq1d (.objEq j m) (synCplc (.cv j) (.cv j)) (synCplc (.cv m) (.cv m))
      (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) p0016
  have p0019 :=
    @gImbi2d (.objEq j m)
      (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) p0018
  have p0020 :=
    @gRalbidv (.objEq j m)
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      n (synCnnc) dv_cache_0005 p0019
  have p0021 := @gAddceq12 (.cv n) (.cv n) (.cv p) (.cv p)
  have p0022_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq n p) (.objEq n p))
        (.classEq (synCplc (.cv n) (.cv n)) (synCplc (.cv p) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCplc synWrex synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0021
  have p0022 :=
    @gAnidms (.objEq n p)
      (.classEq (synCplc (.cv n) (.cv n)) (synCplc (.cv p) (.cv p))) p0022_e00_recanon
  have p0023 :=
    @gAddceq1d (.objEq n p) (synCplc (.cv n) (.cv n)) (synCplc (.cv p) (.cv p))
      (synC1c) p0022
  have p0024 :=
    @gNeeq1d (.objEq n p) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
      (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0) p0023
  have p0025 :=
    @gNeeq2d (.objEq n p) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
      (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synCplc (.cv m) (.cv m)) p0023
  have p0026 :=
    @gImbi12d (.objEq n p)
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
      (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))
      p0024 p0025
  have p0027 :=
    @gCbvralv
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
        (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))
      n p (synCnnc) dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 p0026
  have p0028 :=
    @gSyl6bb (.objEq j m)
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (synWral p (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
      p0020 p0027
  have p0029 :=
    @gImbi12d (.objEq j m) (synWne (synCplc (.cv j) (.cv j)) (synC0))
      (synWne (synCplc (.cv m) (.cv m)) (synC0))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (synWral p (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
      p0017 p0028
  have p0030 :=
    @gAddceq12 (.cv j) (.cv j) (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))
  have p0031 :=
    @gAnidms (.classEq (.cv j) (synCplc (.cv m) (synC1c)))
      (.classEq (synCplc (.cv j) (.cv j))
        (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))))
      p0030
  have p0032 := @gAddcass (synCplc (.cv m) (synC1c)) (.cv m) (synC1c)
  have p0033 := @gAddc32 (.cv m) (synC1c) (.cv m)
  have p0034 :=
    @gAddceq1i (synCplc (synCplc (.cv m) (synC1c)) (.cv m))
      (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c) p0033
  have p0035 :=
    @gEqtr3i (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (synC1c))
      (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
      (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) p0032 p0034
  have p0036 :=
    @gSyl6eq (.classEq (.cv j) (synCplc (.cv m) (synC1c))) (synCplc (.cv j) (.cv j))
      (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
      (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) p0031 p0035
  have p0037 :=
    @gNeeq1d (.classEq (.cv j) (synCplc (.cv m) (synC1c))) (synCplc (.cv j) (.cv j))
      (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0) p0036
  have p0038 :=
    @gNeeq1d (.classEq (.cv j) (synCplc (.cv m) (synC1c))) (synCplc (.cv j) (.cv j))
      (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
      (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) p0036
  have p0039 :=
    @gImbi2d (.classEq (.cv j) (synCplc (.cv m) (synC1c)))
      (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) p0038
  have p0040 :=
    @gRalbidv (.classEq (.cv j) (synCplc (.cv m) (synC1c)))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      n (synCnnc) dv_cache_0010 p0039
  have p0041 :=
    @gImbi12d (.classEq (.cv j) (synCplc (.cv m) (synC1c)))
      (synWne (synCplc (.cv j) (.cv j)) (synC0))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      p0037 p0040
  have p0042 := @gAddceq12 (.cv j) (.cv j) (.cv k) (.cv k)
  have p0043_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq j k) (.objEq j k))
        (.classEq (synCplc (.cv j) (.cv j)) (synCplc (.cv k) (.cv k)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCplc synWrex synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0042
  have p0043 :=
    @gAnidms (.objEq j k)
      (.classEq (synCplc (.cv j) (.cv j)) (synCplc (.cv k) (.cv k))) p0043_e00_recanon
  have p0044 :=
    @gNeeq1d (.objEq j k) (synCplc (.cv j) (.cv j)) (synCplc (.cv k) (.cv k)) (synC0)
      p0043
  have p0045 :=
    @gNeeq1d (.objEq j k) (synCplc (.cv j) (.cv j)) (synCplc (.cv k) (.cv k))
      (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) p0043
  have p0046 :=
    @gImbi2d (.objEq j k)
      (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) p0045
  have p0047 :=
    @gRalbidv (.objEq j k)
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      n (synCnnc) dv_cache_0011 p0046
  have p0048 :=
    @gImbi12d (.objEq j k) (synWne (synCplc (.cv j) (.cv j)) (synC0))
      (synWne (synCplc (.cv k) (.cv k)) (synC0))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      p0044 p0047
  have p0049 := @gN0cnsuc (synCplc (.cv n) (.cv n))
  have p0050 := @gNecomi (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0c) p0049
  have p0051 :=
    @gA1i (synWne (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) p0050
  have p0052 :=
    @gRgenw
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      n (synCnnc) p0051
  have p0053 :=
    @gA1i
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (synWne (synC0c) (synC0)) p0052
  have p0054 := @gAddcass (synCplc (.cv m) (.cv m)) (synC1c) (synC1c)
  have p0055 :=
    @gNeeq1i (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
      (synCplc (synCplc (.cv m) (.cv m)) (synCplc (synC1c) (synC1c))) (synC0) p0054
  have p0056 := @gAddcnnul (synCplc (.cv m) (.cv m)) (synCplc (synC1c) (synC1c))
  have p0057 :=
    @gSimpld
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synCplc (synC1c) (synC1c))) (synC0))
      (synWne (synCplc (.cv m) (.cv m)) (synC0))
      (synWne (synCplc (synC1c) (synC1c)) (synC0)) p0056
  have p0058 :=
    @gSylbi
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synCplc (synC1c) (synC1c))) (synC0))
      (synWne (synCplc (.cv m) (.cv m)) (synC0)) p0055 p0057
  have p0059 :=
    @gAdantl
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (synWne (synCplc (.cv m) (.cv m)) (synC0)) (.classMem (.cv m) (synCnnc)) p0058
  have p0060 :=
    @gSimprl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
      (.classMem (.cv n) (synCnnc))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
  have p0061 := @gNnc0suc q (.cv n) dv_cache_0012
  have p0062 :=
    @gSylib
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWa (.classMem (.cv n) (synCnnc))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (.classMem (.cv n) (synCnnc))
      (synWo (.classEq (.cv n) (synC0c))
        (synWrex q (synCnnc) (.classEq (.cv n) (synCplc (.cv q) (synC1c)))))
      p0060 p0061
  have p0063 := @gN0cnsuc (synCplc (.cv m) (.cv m))
  have p0064 := @gAddceq12 (.cv n) (.cv n) (synC0c) (synC0c)
  have p0065 :=
    @gAnidms (.classEq (.cv n) (synC0c))
      (.classEq (synCplc (.cv n) (.cv n)) (synCplc (synC0c) (synC0c))) p0064
  have p0066 :=
    @gSyl6eq (.classEq (.cv n) (synC0c)) (synCplc (.cv n) (.cv n))
      (synCplc (synC0c) (synC0c)) (synC0c) p0065 p0008
  have p0067 :=
    @gNeeq2d (.classEq (.cv n) (synC0c)) (synCplc (.cv n) (.cv n)) (synC0c)
      (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) p0066
  have p0068 :=
    @gMpbiri (.classEq (.cv n) (synC0c))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n)))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC0c)) p0063 p0067
  have p0069 :=
    @gA1i
      (.imp (.classEq (.cv n) (synC0c))
        (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n))))
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWa (.classMem (.cv n) (synCnnc))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      p0068
  have p0070 :=
    @gSimpr
      (synWne (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synC1c)) (synC0))
      (.classMem (.cv q) (synCnnc))
  have p0071 :=
    @gAdantl
      (synWa (synWne
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc)))
      (.classMem (.cv q) (synCnnc))
      (synWa (.classMem (.cv m) (synCnnc))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
      p0070
  have p0072 := @gAddceq12 (.cv p) (.cv p) (.cv q) (.cv q)
  have p0073_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq p q) (.objEq p q))
        (.classEq (synCplc (.cv p) (.cv p)) (synCplc (.cv q) (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCplc synWrex synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0072
  have p0073 :=
    @gAnidms (.objEq p q)
      (.classEq (synCplc (.cv p) (.cv p)) (synCplc (.cv q) (.cv q))) p0073_e00_recanon
  have p0074 :=
    @gAddceq1d (.objEq p q) (synCplc (.cv p) (.cv p)) (synCplc (.cv q) (.cv q))
      (synC1c) p0073
  have p0075 :=
    @gNeeq1d (.objEq p q) (synCplc (synCplc (.cv p) (.cv p)) (synC1c))
      (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0) p0074
  have p0076 :=
    @gNeeq2d (.objEq p q) (synCplc (synCplc (.cv p) (.cv p)) (synC1c))
      (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synCplc (.cv m) (.cv m)) p0074
  have p0077 :=
    @gImbi12d (.objEq p q)
      (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
      (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0))
      (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))
      (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv q) (.cv q)) (synC1c)))
      p0075 p0076
  have p0078_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv p) (.cv q)) (synWb
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))
          (.imp (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv q) (.cv q)) (synC1c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne synCplc synWrex synWex synWa synC1c synC0 synCdif
          synCin synCcompl synCnin synWnan synCvv
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0077
  have p0078 :=
    @gRspcv
      (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
        (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))
      (.imp (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0))
        (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv q) (.cv q)) (synC1c))))
      p (.cv q) (synCnnc) dv_cache_0013 dv_cache_0007 dv_cache_0014 p0078_e00_recanon
  have p0079 :=
    @gSyl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWa (synWne
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc))))
      (.classMem (.cv q) (synCnnc))
      (.imp (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
        (.imp (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv q) (.cv q)) (synC1c)))))
      p0071 p0078
  have p0080 := @gAddc4 (.cv q) (synC1c) (.cv q) (synC1c)
  have p0081 :=
    @gAddceq1i (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
      (synCplc (synCplc (.cv q) (.cv q)) (synCplc (synC1c) (synC1c))) (synC1c) p0080
  have p0082 :=
    @gAddc32 (synCplc (.cv q) (.cv q)) (synCplc (synC1c) (synC1c)) (synC1c)
  have p0083 :=
    @gEqtri
      (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))) (synC1c))
      (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synCplc (synC1c) (synC1c))) (synC1c))
      (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synCplc (synC1c) (synC1c)))
      p0081 p0082
  have p0084 :=
    @gNeeq1i
      (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))) (synC1c))
      (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synCplc (synC1c) (synC1c)))
      (synC0) p0083
  have p0085 :=
    @gAddcnnul (synCplc (synCplc (.cv q) (.cv q)) (synC1c))
      (synCplc (synC1c) (synC1c))
  have p0086 :=
    @gSimpld
      (synWne (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c))
          (synCplc (synC1c) (synC1c))) (synC0))
      (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0))
      (synWne (synCplc (synC1c) (synC1c)) (synC0)) p0085
  have p0087 :=
    @gSylbi
      (synWne (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synC1c)) (synC0))
      (synWne (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c))
          (synCplc (synC1c) (synC1c))) (synC0))
      (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0)) p0084 p0086
  have p0088 :=
    @gAdantr
      (synWne (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synC1c)) (synC0))
      (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0))
      (.classMem (.cv q) (synCnnc)) p0087
  have p0089 :=
    @gAdantl
      (synWa (synWne
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc)))
      (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0))
      (synWa (.classMem (.cv m) (synCnnc))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
      p0088
  have p0090 := @gAddc32 (.cv q) (.cv q) (synC1c)
  have p0091 :=
    @gAddceq1i (synCplc (synCplc (.cv q) (.cv q)) (synC1c))
      (synCplc (synCplc (.cv q) (synC1c)) (.cv q)) (synC1c) p0090
  have p0092 := @gAddcass (synCplc (.cv q) (synC1c)) (.cv q) (synC1c)
  have p0093 :=
    @gEqtri (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c))
      (synCplc (synCplc (synCplc (.cv q) (synC1c)) (.cv q)) (synC1c))
      (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))) p0091 p0092
  have p0094 :=
    @gEqeq2i (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c))
      (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
      (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) p0093
  have p0095 :=
    @gSimplll (.classMem (.cv m) (synCnnc))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (synWa (synWne
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc)))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c)))
  have p0096 := @gNncaddccl (.cv m) (.cv m)
  have p0097 :=
    @gAnidms (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (.cv m) (.cv m)) (synCnnc)) p0096
  have p0098 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWa (synWne (synCplc
                (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))) (synC1c))
              (synC0)) (.classMem (.cv q) (synCnnc))))
        (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
          (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c))))
      (.classMem (.cv m) (synCnnc)) (.classMem (synCplc (.cv m) (.cv m)) (synCnnc))
      p0095 p0097
  have p0099 :=
    @gSimplrr
      (synWa (.classMem (.cv m) (synCnnc))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
      (synWne (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synC1c)) (synC0))
      (.classMem (.cv q) (synCnnc))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c)))
  have p0100 := @gNncaddccl (.cv q) (.cv q)
  have p0101 :=
    @gAnidms (.classMem (.cv q) (synCnnc))
      (.classMem (synCplc (.cv q) (.cv q)) (synCnnc)) p0100
  have p0102 := @gPeano2 (synCplc (.cv q) (.cv q))
  have p0103 :=
    @gN3syl
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWa (synWne (synCplc
                (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))) (synC1c))
              (synC0)) (.classMem (.cv q) (synCnnc))))
        (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
          (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c))))
      (.classMem (.cv q) (synCnnc)) (.classMem (synCplc (.cv q) (.cv q)) (synCnnc))
      (.classMem (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synCnnc)) p0099 p0101
      p0102
  have p0104 :=
    @gSimpr
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWa (synWne
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc))))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c)))
  have p0105 :=
    @gSimpllr (.classMem (.cv m) (synCnnc))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (synWa (synWne
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc)))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c)))
  have p0106 := @gAddcnnul (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)
  have p0107 :=
    @gSimpld
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC0))
      (synWne (synC1c) (synC0)) p0106
  have p0108 :=
    @gSyl
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWa (synWne (synCplc
                (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))) (synC1c))
              (synC0)) (.classMem (.cv q) (synCnnc))))
        (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
          (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c))))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC0)) p0105 p0107
  have p0109 :=
    @gPrepeano4 (synCplc (.cv m) (.cv m))
      (synCplc (synCplc (.cv q) (.cv q)) (synC1c))
  have p0110 :=
    @gSyl22anc
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWa (synWne (synCplc
                (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))) (synC1c))
              (synC0)) (.classMem (.cv q) (synCnnc))))
        (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
          (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c))))
      (.classMem (synCplc (.cv m) (.cv m)) (synCnnc))
      (.classMem (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synCnnc))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c)))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC0))
      (.classEq (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv q) (.cv q)) (synC1c)))
      p0098 p0103 p0104 p0108 p0109
  have p0111 :=
    @gEx
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWa (synWne
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc))))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c)))
      (.classEq (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv q) (.cv q)) (synC1c)))
      p0110
  have p0112 :=
    @gSyl5bir
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC1c)))
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWa (synWne
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc))))
      (.classEq (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv q) (.cv q)) (synC1c)))
      p0094 p0111
  have p0113 :=
    @gNecon3d
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWa (synWne
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc))))
      (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
      (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
      (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) p0112
  have p0114 :=
    @gEmbantd
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWa (synWne
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc))))
      (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0))
      (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv q) (.cv q)) (synC1c)))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))))
      p0089 p0113
  have p0115 :=
    @gSyld
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWa (synWne
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synC1c)) (synC0)) (.classMem (.cv q) (synCnnc))))
      (synWral p (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
      (.imp (synWne (synCplc (synCplc (.cv q) (.cv q)) (synC1c)) (synC0))
        (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv q) (.cv q)) (synC1c))))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))))
      p0079 p0114
  have p0116 :=
    @gExpr
      (synWa (.classMem (.cv m) (synCnnc))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
      (synWne (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synC1c)) (synC0))
      (.classMem (.cv q) (synCnnc))
      (.imp (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
        (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
          (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))))
      p0115
  have p0117 :=
    @gCom23
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWne
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synC1c)) (synC0)))
      (.classMem (.cv q) (synCnnc))
      (synWral p (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))))
      p0116
  have p0118 :=
    @gEx
      (synWa (.classMem (.cv m) (synCnnc))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
      (synWne (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synC1c)) (synC0))
      (.imp (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
        (.imp (.classMem (.cv q) (synCnnc))
          (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
            (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))))))
      p0117
  have p0119 :=
    @gCom23
      (synWa (.classMem (.cv m) (synCnnc))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
      (synWne (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synC1c)) (synC0))
      (synWral p (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
      (.imp (.classMem (.cv q) (synCnnc))
        (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
          (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))))
      p0118
  have p0120 :=
    @gImp31
      (synWa (.classMem (.cv m) (synCnnc))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
      (synWral p (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
      (synWne (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synC1c)) (synC0))
      (.imp (.classMem (.cv q) (synCnnc))
        (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
          (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))))
      p0119
  have p0121 :=
    @gCom12
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))) (synWne
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synC1c)) (synC0)))
      (.classMem (.cv q) (synCnnc))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))))
      p0120
  have p0122 :=
    @gAddceq12 (.cv n) (.cv n) (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))
  have p0123 :=
    @gAnidms (.classEq (.cv n) (synCplc (.cv q) (synC1c)))
      (.classEq (synCplc (.cv n) (.cv n))
        (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))))
      p0122
  have p0124 :=
    @gAddceq1d (.classEq (.cv n) (synCplc (.cv q) (synC1c))) (synCplc (.cv n) (.cv n))
      (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))) (synC1c) p0123
  have p0125 :=
    @gNeeq1d (.classEq (.cv n) (synCplc (.cv q) (synC1c)))
      (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
      (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))) (synC1c))
      (synC0) p0124
  have p0126 :=
    @gAnbi2d (.classEq (.cv n) (synCplc (.cv q) (synC1c)))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (synWne (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synC1c)) (synC0))
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
      p0125
  have p0127 :=
    @gNeeq2d (.classEq (.cv n) (synCplc (.cv q) (synC1c))) (synCplc (.cv n) (.cv n))
      (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
      (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) p0123
  have p0128 :=
    @gImbi12d (.classEq (.cv n) (synCplc (.cv q) (synC1c)))
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))) (synWne
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synC1c)) (synC0)))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n)))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))))
      p0126 p0127
  have p0129 :=
    @gSyl5ibrcom (.classMem (.cv q) (synCnnc))
      (.imp (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWne
                (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
            (synWral p (synCnnc)
              (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
                (synWne (synCplc (.cv m) (.cv m))
                  (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
        (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n))))
      (.classEq (.cv n) (synCplc (.cv q) (synC1c)))
      (.imp (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWne
                (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
            (synWral p (synCnnc)
              (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
                (synWne (synCplc (.cv m) (.cv m))
                  (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))) (synWne
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synC1c)) (synC0))) (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
          (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))))
      p0121 p0128
  have p0130 :=
    @gRexlimiv (.classEq (.cv n) (synCplc (.cv q) (synC1c)))
      (.imp (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWne
                (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
            (synWral p (synCnnc)
              (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
                (synWne (synCplc (.cv m) (.cv m))
                  (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
        (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n))))
      q (synCnnc) dv_cache_0015 p0129
  have p0131 :=
    @gCom12 (synWrex q (synCnnc) (.classEq (.cv n) (synCplc (.cv q) (synC1c))))
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n)))
      p0130
  have p0132 :=
    @gAdantrl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (.imp (synWrex q (synCnnc) (.classEq (.cv n) (synCplc (.cv q) (synC1c))))
        (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n))))
      (.classMem (.cv n) (synCnnc)) p0131
  have p0133 :=
    @gJaod
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWa (.classMem (.cv n) (synCnnc))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (.classEq (.cv n) (synC0c))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n)))
      (synWrex q (synCnnc) (.classEq (.cv n) (synCplc (.cv q) (synC1c)))) p0069 p0132
  have p0134 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWa (.classMem (.cv n) (synCnnc))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (synWo (.classEq (.cv n) (synC0c))
        (synWrex q (synCnnc) (.classEq (.cv n) (synCplc (.cv q) (synC1c)))))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n)))
      p0062 p0133
  have p0135 :=
    @gSimplll (.classMem (.cv m) (synCnnc))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (synWral p (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
      (synWa (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
  have p0136 :=
    @gAdantr
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWa (.classMem (.cv n) (synCnnc))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (.classMem (.cv m) (synCnnc))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      p0135
  have p0137 := @gPeano2 (synCplc (.cv m) (.cv m))
  have p0138 :=
    @gN3syl
      (synWa (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWne
                (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
            (synWral p (synCnnc)
              (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
                (synWne (synCplc (.cv m) (.cv m))
                  (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
          (synWa (.classMem (.cv n) (synCnnc))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
        (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.classMem (.cv m) (synCnnc)) (.classMem (synCplc (.cv m) (.cv m)) (synCnnc))
      (.classMem (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCnnc)) p0136 p0097
      p0137
  have p0139 :=
    @gSimplrl
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
      (.classMem (.cv n) (synCnnc))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
  have p0140 := @gNncaddccl (.cv n) (.cv n)
  have p0141 :=
    @gAnidms (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) p0140
  have p0142 :=
    @gSyl
      (synWa (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWne
                (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
            (synWral p (synCnnc)
              (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
                (synWne (synCplc (.cv m) (.cv m))
                  (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
          (synWa (.classMem (.cv n) (synCnnc))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
        (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.classMem (.cv n) (synCnnc)) (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      p0139 p0141
  have p0143 :=
    @gSimpr
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWa (.classMem (.cv n) (synCnnc))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
  have p0144 :=
    @gSimpllr (.classMem (.cv m) (synCnnc))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (synWral p (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
      (synWa (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
  have p0145 :=
    @gAdantr
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWa (.classMem (.cv n) (synCnnc))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      p0144
  have p0146 :=
    @gPrepeano4 (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
      (synCplc (.cv n) (.cv n))
  have p0147 :=
    @gSyl22anc
      (synWa (synWa (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWne
                (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
            (synWral p (synCnnc)
              (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
                (synWne (synCplc (.cv m) (.cv m))
                  (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
          (synWa (.classMem (.cv n) (synCnnc))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
        (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.classMem (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n)))
      p0138 p0142 p0143 p0145 p0146
  have p0148 :=
    @gEx
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWa (.classMem (.cv n) (synCnnc))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n)))
      p0147
  have p0149 :=
    @gNecon3d
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWa (.classMem (.cv n) (synCnnc))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
      (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
      (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n)) p0148
  have p0150 :=
    @gMpd
      (synWa (synWa (synWa (.classMem (.cv m) (synCnnc))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synC0))) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
        (synWa (.classMem (.cv n) (synCnnc))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (synWne (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synCplc (.cv n) (.cv n)))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      p0134 p0149
  have p0151 :=
    @gExpr
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
      (.classMem (.cv n) (synCnnc))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
        (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      p0150
  have p0152 :=
    @gRalrimiva
      (synWa (synWa (.classMem (.cv m) (synCnnc))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synC0))) (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
          (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      n (synCnnc) dv_cache_0016 p0151
  have p0153 :=
    @gEx
      (synWa (.classMem (.cv m) (synCnnc))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
      (synWral p (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      p0152
  have p0154 :=
    @gEmbantd
      (synWa (.classMem (.cv m) (synCnnc))
        (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0)))
      (synWne (synCplc (.cv m) (.cv m)) (synC0))
      (synWral p (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
          (synWne (synCplc (.cv m) (.cv m)) (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      p0059 p0153
  have p0155 :=
    @gEx (.classMem (.cv m) (synCnnc))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (.imp (.imp (synWne (synCplc (.cv m) (.cv m)) (synC0)) (synWral p (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
              (synWne (synCplc (.cv m) (.cv m))
                (synCplc (synCplc (.cv p) (.cv p)) (synC1c)))))) (synWral n (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))
      p0154
  have p0156 :=
    @gCom23 (.classMem (.cv m) (synCnnc))
      (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c)) (synC0))
      (.imp (synWne (synCplc (.cv m) (.cv m)) (synC0)) (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
            (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      p0155
  have p0157_e04_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv j) (.cv k)) (synWb
          (.imp (synWne (synCplc (.cv j) (.cv j)) (synC0)) (synWral n (synCnnc)
              (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
                (synWne (synCplc (.cv j) (.cv j))
                  (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))
          (.imp (synWne (synCplc (.cv k) (.cv k)) (synC0)) (synWral n (synCnnc)
              (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
                (synWne (synCplc (.cv k) (.cv k))
                  (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne synCplc synWrex synWex synWa synC0 synCdif synCin
          synCcompl synCnin synWnan synCvv synWral synCnnc synCint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0048
  have p0157 :=
    @gFinds
      (.imp (synWne (synCplc (.cv j) (.cv j)) (synC0)) (synWral n (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
            (synWne (synCplc (.cv j) (.cv j))
              (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))
      (.imp (synWne (synC0c) (synC0)) (synWral n (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
            (synWne (synC0c) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))
      (.imp (synWne (synCplc (.cv m) (.cv m)) (synC0)) (synWral p (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv p) (.cv p)) (synC1c)) (synC0))
            (synWne (synCplc (.cv m) (.cv m))
              (synCplc (synCplc (.cv p) (.cv p)) (synC1c))))))
      (.imp (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
          (synC0)) (synWral n (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
            (synWne (synCplc (synCplc (synCplc (.cv m) (.cv m)) (synC1c)) (synC1c))
              (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))
      (.imp (synWne (synCplc (.cv k) (.cv k)) (synC0)) (synWral n (synCnnc)
          (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
            (synWne (synCplc (.cv k) (.cv k))
              (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))
      j m (.cv k) dv_cache_0017 dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
      dv_cache_0022 dv_cache_0023 p0005 p0014 p0029 p0041 p0157_e04_recanon p0053 p0156
  have p0158 :=
    (Nominal.biimpRefl (synWne (synCplc (.cv k) (.cv k))
        (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
  have p0159 :=
    @gImbi2i
      (synWne (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.neg (.classEq (synCplc (.cv k) (.cv k))
          (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) p0158
  have p0160 :=
    @gCon2b (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (.classEq (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
  have p0161 :=
    @gBitri
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) (.neg
          (.classEq (synCplc (.cv k) (.cv k))
            (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (.imp (.classEq (synCplc (.cv k) (.cv k))
          (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (.neg (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      p0159 p0160
  have p0162 :=
    @gImnan
      (.classEq (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
  have p0163 :=
    @gBitri
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.imp (.classEq (synCplc (.cv k) (.cv k))
          (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (.neg (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (.neg (synWa (.classEq (synCplc (.cv k) (.cv k))
            (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      p0161 p0162
  have p0164 :=
    @gRalbii
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (synWne (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.neg (synWa (.classEq (synCplc (.cv k) (.cv k))
            (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      n (synCnnc) p0163
  have p0165 :=
    @gRalnex
      (synWa (.classEq (synCplc (.cv k) (.cv k))
          (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      n (synCnnc)
  have p0166 :=
    @gBitri
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (synWral n (synCnnc) (.neg (synWa (.classEq (synCplc (.cv k) (.cv k))
              (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))
      (.neg (synWrex n (synCnnc) (synWa (.classEq (synCplc (.cv k) (.cv k))
              (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))
      p0164 p0165
  have p0167 :=
    @gSyl6ib (.classMem (.cv k) (synCnnc)) (synWne (synCplc (.cv k) (.cv k)) (synC0))
      (synWral n (synCnnc)
        (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
          (synWne (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      (.neg (synWrex n (synCnnc) (synWa (.classEq (synCplc (.cv k) (.cv k))
              (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))
      p0157 p0166
  have p0168 :=
    @gEqeq1 (.cv x) (synCplc (.cv k) (.cv k))
      (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
  have p0169 :=
    @gAnbi1d (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
      (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq (synCplc (.cv k) (.cv k)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) p0168
  have p0170 :=
    @gRexbidv (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
      (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      (synWa (.classEq (synCplc (.cv k) (.cv k))
          (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      n (synCnnc) dv_cache_0024 p0169
  have p0171 :=
    @gNotbid (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
      (synWrex n (synCnnc)
        (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      (synWrex n (synCnnc) (synWa (.classEq (synCplc (.cv k) (.cv k))
            (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      p0170
  have p0172 :=
    @gImbi2d (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
      (.neg (synWrex n (synCnnc)
          (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))
      (.neg (synWrex n (synCnnc) (synWa (.classEq (synCplc (.cv k) (.cv k))
              (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))
      (synWne (synCplc (.cv k) (.cv k)) (synC0)) p0171
  have p0173 :=
    @gSyl5ibrcom (.classMem (.cv k) (synCnnc))
      (.imp (synWne (synCplc (.cv k) (.cv k)) (synC0)) (.neg (synWrex n (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
              (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))))
      (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
      (.imp (synWne (synCplc (.cv k) (.cv k)) (synC0)) (.neg (synWrex n (synCnnc) (synWa
              (.classEq (synCplc (.cv k) (.cv k))
                (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
              (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))))
      p0167 p0172
  have p0174 :=
    @gImp3a (.classMem (.cv k) (synCnnc)) (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
      (synWne (synCplc (.cv k) (.cv k)) (synC0))
      (.neg (synWrex n (synCnnc)
          (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))
      p0173
  have p0175 :=
    @gRexlimiv
      (synWa (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
        (synWne (synCplc (.cv k) (.cv k)) (synC0)))
      (.neg (synWrex n (synCnnc)
          (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))
      k (synCnnc) dv_cache_0025 p0174
  have p0176 :=
    @gImnan
      (synWrex k (synCnnc) (synWa (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
          (synWne (synCplc (.cv k) (.cv k)) (synC0))))
      (synWrex n (synCnnc)
        (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
  have p0177 :=
    @gMpbi
      (.imp (synWrex k (synCnnc) (synWa (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
            (synWne (synCplc (.cv k) (.cv k)) (synC0)))) (.neg (synWrex n (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
              (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))))
      (.neg (synWa (synWrex k (synCnnc) (synWa (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
              (synWne (synCplc (.cv k) (.cv k)) (synC0)))) (synWrex n (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
              (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))))
      p0175 p0176
  have p0178 :=
    @gAbf
      (synWa (synWrex k (synCnnc) (synWa (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
            (synWne (synCplc (.cv k) (.cv k)) (synC0)))) (synWrex n (synCnnc)
          (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))))
      x p0177
  have p0179 :=
    @gEqtri (synCin (synCevenfin) (synCoddfin))
      (.cab x (synWa (synWrex k (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (.cv k) (.cv k)))
              (synWne (synCplc (.cv k) (.cv k)) (synC0)))) (synWrex n (synCnnc)
            (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
              (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))))
      (synC0) p0004 p0178
  exact p0179


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part005`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_eventfin`. -/
@[expose]
noncomputable def gEventfin (M : Class) :
    Nominal.NPrf
      (.imp (.classMem M (synCevenfin)) (.classMem (synCtfin M) (synCevenfin))) :=
  by
  let proofSupport : Finset Var := M.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_x_ne_m : x ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_x : m ≠ x := Ne.symm fresh_x_ne_m
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) M)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_M, or_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_M, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((synWa (synWrex n (synCnnc) (.classEq M (synCplc (.cv n) (.cv n))))
          (synWne M (synC0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_M, fresh_x_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_n, not_false_eq_true])
  have dv_cache_0006 : m ∉ ((synCtfin (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_m_ne_n,
          not_false_eq_true])
  have dv_cache_0007 : m ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 :
    m ∉
      ((Wff.classEq (synCtfin (synCplc (.cv n) (.cv n)))
          (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_n, or_false, not_false_eq_true])
  have dv_cache_0009 :
    m ∉ ((Wff.classEq (.cv x) (synCtfin (synCplc (.cv n) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_x, fresh_m_ne_n, or_false, not_false_eq_true])
  have dv_cache_0010 : m ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0011 : x ∉ ((synCtfin (synCplc (.cv n) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_n, or_false, not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((synWa (synWrex m (synCnnc)
            (.classEq (synCtfin (synCplc (.cv n) (.cv n))) (synCplc (.cv m) (.cv m))))
          (synWne (synCtfin (synCplc (.cv n) (.cv n))) (synC0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_n, fresh_x_ne_m,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0013 :
    n ∉ ((Wff.imp (synWne M (synC0)) (.classMem (synCtfin M) (synCevenfin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cevenfin, Finset.mem_union,
          fresh_n_not_M, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gEqeq1 (.cv x) M (synCplc (.cv n) (.cv n))
  have p0001 :=
    @gRexbidv (.classEq (.cv x) M) (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
      (.classEq M (synCplc (.cv n) (.cv n))) n (synCnnc) dv_cache_0001 p0000
  have p0002 := @gNeeq1 (.cv x) M (synC0)
  have p0003 :=
    @gAnbi12d (.classEq (.cv x) M)
      (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
      (synWrex n (synCnnc) (.classEq M (synCplc (.cv n) (.cv n))))
      (synWne (.cv x) (synC0)) (synWne M (synC0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfEvenfin x n
      dv_cache_0002
  have p0005 :=
    @gElab2g
      (synWa (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (.cv n) (.cv n))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex n (synCnnc) (.classEq M (synCplc (.cv n) (.cv n))))
        (synWne M (synC0)))
      x M (synCevenfin) (synCevenfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @gIbi (.classMem M (synCevenfin))
      (synWa (synWrex n (synCnnc) (.classEq M (synCplc (.cv n) (.cv n))))
        (synWne M (synC0)))
      p0005
  have p0007 := @gAddceq2 (.cv n) (synC0) (.cv n)
  have p0008 := @gAddcnul1 (.cv n)
  have p0009 :=
    @gSyl6eq (.classEq (.cv n) (synC0)) (synCplc (.cv n) (.cv n))
      (synCplc (.cv n) (synC0)) (synC0) p0007 p0008
  have p0010 := @gNecon3i (.cv n) (synC0) (synCplc (.cv n) (.cv n)) (synC0) p0009
  have p0011 := @gTfinprop (.cv n) x dv_cache_0005
  have p0012 :=
    @gSimpld (synWa (.classMem (.cv n) (synCnnc)) (synWne (.cv n) (synC0)))
      (.classMem (synCtfin (.cv n)) (synCnnc))
      (synWrex x (.cv n) (.classMem (synCpw1 (.cv x)) (synCtfin (.cv n)))) p0011
  have p0013 :=
    @gSylan2 (synWne (synCplc (.cv n) (.cv n)) (synC0)) (.classMem (.cv n) (synCnnc))
      (synWne (.cv n) (synC0)) (.classMem (synCtfin (.cv n)) (synCnnc)) p0010 p0012
  have p0014 := @gTfindi (.cv n) (.cv n)
  have p0015 :=
    @gN3anidm12 (.classMem (.cv n) (synCnnc))
      (synWne (synCplc (.cv n) (.cv n)) (synC0))
      (.classEq (synCtfin (synCplc (.cv n) (.cv n)))
        (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))
      p0014
  have p0016 := @gAddceq12 (.cv m) (.cv m) (synCtfin (.cv n)) (synCtfin (.cv n))
  have p0017 :=
    @gAnidms (.classEq (.cv m) (synCtfin (.cv n)))
      (.classEq (synCplc (.cv m) (.cv m)) (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))
      p0016
  have p0018 :=
    @gEqeq2d (.classEq (.cv m) (synCtfin (.cv n))) (synCplc (.cv m) (.cv m))
      (synCplc (synCtfin (.cv n)) (synCtfin (.cv n)))
      (synCtfin (synCplc (.cv n) (.cv n))) p0017
  have p0019 :=
    @gRspcev (.classEq (synCtfin (synCplc (.cv n) (.cv n))) (synCplc (.cv m) (.cv m)))
      (.classEq (synCtfin (synCplc (.cv n) (.cv n)))
        (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))
      m (synCtfin (.cv n)) (synCnnc) dv_cache_0006 dv_cache_0007 dv_cache_0008 p0018
  have p0020 :=
    @gSyl2anc
      (synWa (.classMem (.cv n) (synCnnc)) (synWne (synCplc (.cv n) (.cv n)) (synC0)))
      (.classMem (synCtfin (.cv n)) (synCnnc))
      (.classEq (synCtfin (synCplc (.cv n) (.cv n)))
        (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))
      (synWrex m (synCnnc)
        (.classEq (synCtfin (synCplc (.cv n) (.cv n))) (synCplc (.cv m) (.cv m))))
      p0013 p0015 p0019
  have p0021 := @gNncaddccl (.cv n) (.cv n)
  have p0022 :=
    @gAnidms (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) p0021
  have p0023 := @gTfinnnul (synCplc (.cv n) (.cv n))
  have p0024 :=
    @gSylan (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (synWne (synCplc (.cv n) (.cv n)) (synC0))
      (synWne (synCtfin (synCplc (.cv n) (.cv n))) (synC0)) p0022 p0023
  have p0025 :=
    @gJca
      (synWa (.classMem (.cv n) (synCnnc)) (synWne (synCplc (.cv n) (.cv n)) (synC0)))
      (synWrex m (synCnnc)
        (.classEq (synCtfin (synCplc (.cv n) (.cv n))) (synCplc (.cv m) (.cv m))))
      (synWne (synCtfin (synCplc (.cv n) (.cv n))) (synC0)) p0020 p0024
  have p0026 := @gTfinex (synCplc (.cv n) (.cv n))
  have p0027 :=
    @gEqeq1 (.cv x) (synCtfin (synCplc (.cv n) (.cv n))) (synCplc (.cv m) (.cv m))
  have p0028 :=
    @gRexbidv (.classEq (.cv x) (synCtfin (synCplc (.cv n) (.cv n))))
      (.classEq (.cv x) (synCplc (.cv m) (.cv m)))
      (.classEq (synCtfin (synCplc (.cv n) (.cv n))) (synCplc (.cv m) (.cv m))) m
      (synCnnc) dv_cache_0009 p0027
  have p0029 := @gNeeq1 (.cv x) (synCtfin (synCplc (.cv n) (.cv n))) (synC0)
  have p0030 :=
    @gAnbi12d (.classEq (.cv x) (synCtfin (synCplc (.cv n) (.cv n))))
      (synWrex m (synCnnc) (.classEq (.cv x) (synCplc (.cv m) (.cv m))))
      (synWrex m (synCnnc)
        (.classEq (synCtfin (synCplc (.cv n) (.cv n))) (synCplc (.cv m) (.cv m))))
      (synWne (.cv x) (synC0)) (synWne (synCtfin (synCplc (.cv n) (.cv n))) (synC0))
      p0028 p0029
  have p0031 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfEvenfin x m
      dv_cache_0010
  have p0032 :=
    @gElab2
      (synWa (synWrex m (synCnnc) (.classEq (.cv x) (synCplc (.cv m) (.cv m))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex m (synCnnc)
          (.classEq (synCtfin (synCplc (.cv n) (.cv n))) (synCplc (.cv m) (.cv m))))
        (synWne (synCtfin (synCplc (.cv n) (.cv n))) (synC0)))
      x (synCtfin (synCplc (.cv n) (.cv n))) (synCevenfin) dv_cache_0011 dv_cache_0012
      p0026 p0030 p0031
  have p0033 :=
    @gSylibr
      (synWa (.classMem (.cv n) (synCnnc)) (synWne (synCplc (.cv n) (.cv n)) (synC0)))
      (synWa (synWrex m (synCnnc)
          (.classEq (synCtfin (synCplc (.cv n) (.cv n))) (synCplc (.cv m) (.cv m))))
        (synWne (synCtfin (synCplc (.cv n) (.cv n))) (synC0)))
      (.classMem (synCtfin (synCplc (.cv n) (.cv n))) (synCevenfin)) p0025 p0032
  have p0034 :=
    @gEx (.classMem (.cv n) (synCnnc)) (synWne (synCplc (.cv n) (.cv n)) (synC0))
      (.classMem (synCtfin (synCplc (.cv n) (.cv n))) (synCevenfin)) p0033
  have p0035 := @gNeeq1 M (synCplc (.cv n) (.cv n)) (synC0)
  have p0036 := @gTfineq M (synCplc (.cv n) (.cv n))
  have p0037 :=
    @gEleq1d (.classEq M (synCplc (.cv n) (.cv n))) (synCtfin M)
      (synCtfin (synCplc (.cv n) (.cv n))) (synCevenfin) p0036
  have p0038 :=
    @gImbi12d (.classEq M (synCplc (.cv n) (.cv n))) (synWne M (synC0))
      (synWne (synCplc (.cv n) (.cv n)) (synC0))
      (.classMem (synCtfin M) (synCevenfin))
      (.classMem (synCtfin (synCplc (.cv n) (.cv n))) (synCevenfin)) p0035 p0037
  have p0039 :=
    @gBiimprd (.classEq M (synCplc (.cv n) (.cv n)))
      (.imp (synWne M (synC0)) (.classMem (synCtfin M) (synCevenfin)))
      (.imp (synWne (synCplc (.cv n) (.cv n)) (synC0))
        (.classMem (synCtfin (synCplc (.cv n) (.cv n))) (synCevenfin)))
      p0038
  have p0040 :=
    @gCom12 (.classEq M (synCplc (.cv n) (.cv n)))
      (.imp (synWne (synCplc (.cv n) (.cv n)) (synC0))
        (.classMem (synCtfin (synCplc (.cv n) (.cv n))) (synCevenfin)))
      (.imp (synWne M (synC0)) (.classMem (synCtfin M) (synCevenfin))) p0039
  have p0041 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.imp (synWne (synCplc (.cv n) (.cv n)) (synC0))
        (.classMem (synCtfin (synCplc (.cv n) (.cv n))) (synCevenfin)))
      (.imp (.classEq M (synCplc (.cv n) (.cv n)))
        (.imp (synWne M (synC0)) (.classMem (synCtfin M) (synCevenfin))))
      p0034 p0040
  have p0042 :=
    @gRexlimiv (.classEq M (synCplc (.cv n) (.cv n)))
      (.imp (synWne M (synC0)) (.classMem (synCtfin M) (synCevenfin))) n (synCnnc)
      dv_cache_0013 p0041
  have p0043 :=
    @gImp (synWrex n (synCnnc) (.classEq M (synCplc (.cv n) (.cv n))))
      (synWne M (synC0)) (.classMem (synCtfin M) (synCevenfin)) p0042
  have p0044 :=
    @gSyl (.classMem M (synCevenfin))
      (synWa (synWrex n (synCnnc) (.classEq M (synCplc (.cv n) (.cv n))))
        (synWne M (synC0)))
      (.classMem (synCtfin M) (synCevenfin)) p0006 p0043
  exact p0044

/-- Checked nominal proof certificate identified upstream as `g_oddtfin`. -/
@[expose]
noncomputable def gOddtfin (M : Class) :
    Nominal.NPrf
      (.imp (.classMem M (synCoddfin)) (.classMem (synCtfin M) (synCoddfin))) :=
  by
  let proofSupport : Finset Var := M.fv
  let n : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_M : n ∉ M.fv := by
    intro h
    exact fresh_n (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_M : x ∉ M.fv := by
    intro h
    exact fresh_x (h)
  have fresh_n_ne_x : n ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_n : x ≠ n := Ne.symm fresh_n_ne_x
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_x_ne_m : x ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_x : m ≠ x := Ne.symm fresh_x_ne_m
  have dv_cache_0001 : n ∉ ((Wff.classEq (.cv x) M)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_x, fresh_n_not_M, or_false, not_false_eq_true])
  have dv_cache_0002 : n ≠ x := by
    clear dv_cache_0001
    exact (show n ≠ x from (by exact fresh_n_ne_x))
  have dv_cache_0003 : x ∉ (M).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_M, not_false_eq_true])
  have dv_cache_0004 :
    x ∉
      ((synWa (synWrex n (synCnnc)
            (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
          (synWne M (synC0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_M, fresh_x_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_n, not_false_eq_true])
  have dv_cache_0006 : m ∉ ((synCtfin (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_m_ne_n,
          not_false_eq_true])
  have dv_cache_0007 : m ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0008 :
    m ∉
      ((Wff.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synCplc (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0009 :
    m ∉
      ((Wff.classEq (.cv x) (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_x, fresh_m_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0010 : m ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show m ≠ x from (by exact fresh_m_ne_x))
  have dv_cache_0011 :
    x ∉ ((synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0012 :
    x ∉
      ((synWa (synWrex m (synCnnc)
            (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
              (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
          (synWne (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synC0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_n, fresh_x_ne_m,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0013 :
    n ∉ ((Wff.imp (synWne M (synC0)) (.classMem (synCtfin M) (synCoddfin)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_coddfin, Finset.mem_union,
          fresh_n_not_M, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gEqeq1 (.cv x) M (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
  have p0001 :=
    @gRexbidv (.classEq (.cv x) M)
      (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) n (synCnnc)
      dv_cache_0001 p0000
  have p0002 := @gNeeq1 (.cv x) M (synC0)
  have p0003 :=
    @gAnbi12d (.classEq (.cv x) M)
      (synWrex n (synCnnc) (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWrex n (synCnnc) (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWne (.cv x) (synC0)) (synWne M (synC0)) p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOddfin x n
      dv_cache_0002
  have p0005 :=
    @gElab2g
      (synWa (synWrex n (synCnnc)
          (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex n (synCnnc)
          (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne M (synC0)))
      x M (synCoddfin) (synCoddfin) dv_cache_0003 dv_cache_0004 p0003 p0004
  have p0006 :=
    @gIbi (.classMem M (synCoddfin))
      (synWa (synWrex n (synCnnc)
          (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne M (synC0)))
      p0005
  have p0007 := @gAddceq2 (.cv n) (synC0) (.cv n)
  have p0008 := @gAddcnul1 (.cv n)
  have p0009 :=
    @gSyl6eq (.classEq (.cv n) (synC0)) (synCplc (.cv n) (.cv n))
      (synCplc (.cv n) (synC0)) (synC0) p0007 p0008
  have p0010 := @gAddceq1 (synCplc (.cv n) (.cv n)) (synC0) (synC1c)
  have p0011 :=
    @gSyl (.classEq (.cv n) (synC0)) (.classEq (synCplc (.cv n) (.cv n)) (synC0))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synCplc (synC0) (synC1c)))
      p0009 p0010
  have p0012 := @gAddccom (synC0) (synC1c)
  have p0013 := @gAddcnul1 (synC1c)
  have p0014 :=
    @gEqtri (synCplc (synC0) (synC1c)) (synCplc (synC1c) (synC0)) (synC0) p0012
      p0013
  have p0015 :=
    @gSyl6eq (.classEq (.cv n) (synC0)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
      (synCplc (synC0) (synC1c)) (synC0) p0011 p0014
  have p0016 :=
    @gNecon3i (.cv n) (synC0) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)
      p0015
  have p0017 := @gTfinprop (.cv n) x dv_cache_0005
  have p0018 :=
    @gSimpld (synWa (.classMem (.cv n) (synCnnc)) (synWne (.cv n) (synC0)))
      (.classMem (synCtfin (.cv n)) (synCnnc))
      (synWrex x (.cv n) (.classMem (synCpw1 (.cv x)) (synCtfin (.cv n)))) p0017
  have p0019 :=
    @gSylan2 (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (.classMem (.cv n) (synCnnc)) (synWne (.cv n) (synC0))
      (.classMem (synCtfin (.cv n)) (synCnnc)) p0016 p0018
  have p0020 := @gNncaddccl (.cv n) (.cv n)
  have p0021 :=
    @gAnidms (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) p0020
  have p0022 := @gN1cnnc
  have p0023 := @gTfindi (synCplc (.cv n) (.cv n)) (synC1c)
  have p0024 :=
    @gMp3an2 (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (.classMem (synC1c) (synCnnc))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synCplc (synCtfin (synCplc (.cv n) (.cv n))) (synCtfin (synC1c))))
      p0022 p0023
  have p0025 :=
    @gSylan (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synCplc (synCtfin (synCplc (.cv n) (.cv n))) (synCtfin (synC1c))))
      p0021 p0024
  have p0026 := @gAddcnnul (synCplc (.cv n) (.cv n)) (synC1c)
  have p0027 :=
    @gSimpld (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (synWne (synCplc (.cv n) (.cv n)) (synC0)) (synWne (synC1c) (synC0)) p0026
  have p0028 := @gTfindi (.cv n) (.cv n)
  have p0029 :=
    @gN3anidm12 (.classMem (.cv n) (synCnnc))
      (synWne (synCplc (.cv n) (.cv n)) (synC0))
      (.classEq (synCtfin (synCplc (.cv n) (.cv n)))
        (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))
      p0028
  have p0030 :=
    @gSylan2 (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (.classMem (.cv n) (synCnnc)) (synWne (synCplc (.cv n) (.cv n)) (synC0))
      (.classEq (synCtfin (synCplc (.cv n) (.cv n)))
        (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))
      p0027 p0029
  have p0031 := @gTfin1c
  have p0032 :=
    @gAddceq12 (synCtfin (synCplc (.cv n) (.cv n))) (synCtfin (synC1c))
      (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))) (synC1c)
  have p0033 :=
    @gMpan2
      (.classEq (synCtfin (synCplc (.cv n) (.cv n)))
        (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))
      (.classEq (synCtfin (synC1c)) (synC1c))
      (.classEq (synCplc (synCtfin (synCplc (.cv n) (.cv n))) (synCtfin (synC1c)))
        (synCplc (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))) (synC1c)))
      p0031 p0032
  have p0034 :=
    @gSyl
      (synWa (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      (.classEq (synCtfin (synCplc (.cv n) (.cv n)))
        (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))
      (.classEq (synCplc (synCtfin (synCplc (.cv n) (.cv n))) (synCtfin (synC1c)))
        (synCplc (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))) (synC1c)))
      p0030 p0033
  have p0035 :=
    @gEqtrd
      (synWa (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synCplc (synCtfin (synCplc (.cv n) (.cv n))) (synCtfin (synC1c)))
      (synCplc (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))) (synC1c)) p0025 p0034
  have p0036 := @gAddceq12 (.cv m) (.cv m) (synCtfin (.cv n)) (synCtfin (.cv n))
  have p0037 :=
    @gAnidms (.classEq (.cv m) (synCtfin (.cv n)))
      (.classEq (synCplc (.cv m) (.cv m)) (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))
      p0036
  have p0038 :=
    @gAddceq1 (synCplc (.cv m) (.cv m))
      (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))) (synC1c)
  have p0039 :=
    @gSyl (.classEq (.cv m) (synCtfin (.cv n)))
      (.classEq (synCplc (.cv m) (.cv m)) (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
        (synCplc (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))) (synC1c)))
      p0037 p0038
  have p0040 :=
    @gEqeq2d (.classEq (.cv m) (synCtfin (.cv n)))
      (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
      (synCplc (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))) (synC1c))
      (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) p0039
  have p0041 :=
    @gRspcev
      (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synCplc (synCplc (.cv m) (.cv m)) (synC1c)))
      (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synCplc (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))) (synC1c)))
      m (synCtfin (.cv n)) (synCnnc) dv_cache_0006 dv_cache_0007 dv_cache_0008 p0040
  have p0042 :=
    @gSyl2anc
      (synWa (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      (.classMem (synCtfin (.cv n)) (synCnnc))
      (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synCplc (synCplc (synCtfin (.cv n)) (synCtfin (.cv n))) (synC1c)))
      (synWrex m (synCnnc)
        (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
      p0019 p0035 p0041
  have p0043 := @gPeano2 (synCplc (.cv n) (.cv n))
  have p0044 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synCnnc)) p0021 p0043
  have p0045 := @gTfinnnul (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
  have p0046 :=
    @gSylan (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synCnnc))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (synWne (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synC0)) p0044
      p0045
  have p0047 :=
    @gJca
      (synWa (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      (synWrex m (synCnnc)
        (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
      (synWne (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synC0)) p0042
      p0046
  have p0048 := @gTfinex (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
  have p0049 :=
    @gEqeq1 (.cv x) (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synCplc (synCplc (.cv m) (.cv m)) (synC1c))
  have p0050 :=
    @gRexbidv
      (.classEq (.cv x) (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (.classEq (.cv x) (synCplc (synCplc (.cv m) (.cv m)) (synC1c)))
      (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synCplc (synCplc (.cv m) (.cv m)) (synC1c)))
      m (synCnnc) dv_cache_0009 p0049
  have p0051 :=
    @gNeeq1 (.cv x) (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synC0)
  have p0052 :=
    @gAnbi12d
      (.classEq (.cv x) (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWrex m (synCnnc) (.classEq (.cv x) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
      (synWrex m (synCnnc)
        (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
      (synWne (.cv x) (synC0))
      (synWne (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synC0)) p0050
      p0051
  have p0053 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOddfin x m
      dv_cache_0010
  have p0054 :=
    @gElab2
      (synWa (synWrex m (synCnnc)
          (.classEq (.cv x) (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
        (synWne (.cv x) (synC0)))
      (synWa (synWrex m (synCnnc)
          (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
        (synWne (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synC0)))
      x (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synCoddfin)
      dv_cache_0011 dv_cache_0012 p0048 p0052 p0053
  have p0055 :=
    @gSylibr
      (synWa (.classMem (.cv n) (synCnnc))
        (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      (synWa (synWrex m (synCnnc)
          (.classEq (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
            (synCplc (synCplc (.cv m) (.cv m)) (synC1c))))
        (synWne (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synC0)))
      (.classMem (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synCoddfin))
      p0047 p0054
  have p0056 :=
    @gEx (.classMem (.cv n) (synCnnc))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (.classMem (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synCoddfin))
      p0055
  have p0057 := @gNeeq1 M (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)
  have p0058 := @gTfineq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
  have p0059 :=
    @gEleq1d (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synCtfin M)
      (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synCoddfin) p0058
  have p0060 :=
    @gImbi12d (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (synWne M (synC0))
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (.classMem (synCtfin M) (synCoddfin))
      (.classMem (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synCoddfin))
      p0057 p0059
  have p0061 :=
    @gBiimprd (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.imp (synWne M (synC0)) (.classMem (synCtfin M) (synCoddfin)))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (.classMem (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synCoddfin)))
      p0060
  have p0062 :=
    @gCom12 (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (.classMem (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synCoddfin)))
      (.imp (synWne M (synC0)) (.classMem (synCtfin M) (synCoddfin))) p0061
  have p0063 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
        (.classMem (synCtfin (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (synCoddfin)))
      (.imp (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (.imp (synWne M (synC0)) (.classMem (synCtfin M) (synCoddfin))))
      p0056 p0062
  have p0064 :=
    @gRexlimiv (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.imp (synWne M (synC0)) (.classMem (synCtfin M) (synCoddfin))) n (synCnnc)
      dv_cache_0013 p0063
  have p0065 :=
    @gImp
      (synWrex n (synCnnc) (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
      (synWne M (synC0)) (.classMem (synCtfin M) (synCoddfin)) p0064
  have p0066 :=
    @gSyl (.classMem M (synCoddfin))
      (synWa (synWrex n (synCnnc)
          (.classEq M (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) (synWne M (synC0)))
      (.classMem (synCtfin M) (synCoddfin)) p0006 p0065
  exact p0066


end NFChoice.DirectNominalPrf.WPPReplay

end
