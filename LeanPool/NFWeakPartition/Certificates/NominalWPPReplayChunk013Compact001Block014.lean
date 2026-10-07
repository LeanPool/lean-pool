/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk013Compact001Block013

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk013Compact001Part065`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nnc3n3p1`. -/
@[expose]
noncomputable def gNnc3n3p1 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (.neg
          (.classEq (synCplc (synCplc A A) A)
            (synCplc (synCplc (synCplc B B) B) (synC1c))))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let n : Var := freshVar proofSupport 0
  let a : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let p : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  let x : Var := freshVar proofSupport 5
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (Finset.mem_union_left _ (h))
  have fresh_n_not_B : n ∉ B.fv := by
    intro h
    exact fresh_n (Finset.mem_union_right _ (h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_a_not_A : a ∉ A.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (h))
  have fresh_n_ne_a : n ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_n : a ≠ n := Ne.symm fresh_n_ne_a
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_n_ne_p : n ≠ p :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_p_ne_n : p ≠ n := Ne.symm fresh_n_ne_p
  have fresh_n_ne_q : n ≠ q :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_q_ne_n : q ≠ n := Ne.symm fresh_n_ne_q
  have fresh_a_ne_m : a ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_a : m ≠ a := Ne.symm fresh_a_ne_m
  have fresh_a_ne_p : a ≠ p :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_p_ne_a : p ≠ a := Ne.symm fresh_a_ne_p
  have fresh_m_ne_p : m ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_p_ne_m : p ≠ m := Ne.symm fresh_m_ne_p
  have fresh_m_ne_q : m ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_q_ne_m : q ≠ m := Ne.symm fresh_m_ne_q
  have fresh_p_ne_q : p ≠ q :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_p : q ≠ p := Ne.symm fresh_p_ne_q
  have fresh_p_ne_x : p ≠ x :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_x_ne_p : x ≠ p := Ne.symm fresh_p_ne_x
  have fresh_q_ne_x : q ≠ x :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_x_ne_q : x ≠ q := Ne.symm fresh_q_ne_x
  have dv_cache_0001 : n ∉ ((Class.cv a)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_a, not_false_eq_true])
  have dv_cache_0002 :
    n ∉
      ((synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                    (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
                (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                      (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn)))))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : n ∉ ((synCnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((synCop (.cv n) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_n, fresh_p_ne_a, or_false, not_false_eq_true])
  have dv_cache_0005 :
    p ∉
      ((synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                    (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                  (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                    (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                  (synCaddcfn))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : q ∉ ((synCop (.cv p) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_n, or_false, not_false_eq_true])
  have dv_cache_0007 :
    q ∉
      ((synCtxp (synCcom (synCaddcfn) (synCcnv
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
          (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                  (synCaddcfn))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_q, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_p, not_false_eq_true])
  have dv_cache_0010 : x ∉ ((synCaddcfn)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0011 :
    x ∉
      ((synCcnv (synCres (synC1st)
            (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : x ∉ ((synCop (.cv q) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_q, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 :
    x ∉ ((synWbr (synCop (.cv q) (synC1c)) (synCaddcfn) (.cv p))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wbr,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_q, fresh_x_ne_p, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0014 : q ∉ ((synCplc (synCplc (.cv n) (.cv n)) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_n, or_false, not_false_eq_true])
  have dv_cache_0015 :
    q ∉
      ((Wff.classEq (.cv p)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0016 : p ∉ ((synCplc (synCplc (.cv a) (.cv a)) (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_a, or_false, not_false_eq_true])
  have dv_cache_0017 :
    p ∉
      ((Wff.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_a, fresh_p_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0018 :
    a ∉
      ((synCcompl (synCima (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn)
                      (synCcnv (synCres (synC1st)
                          (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv
                      (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                    (synCtxp (synCcnv (synC1st))
                                      (synCin (synC1st) (synC2nd)))) (synC2nd))
                                (synCaddcfn)))) (synCima
                            (synCtxp (synCcom (synC1st) (synC1st))
                              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                            (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                          (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCnnc)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cima,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_crn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctxp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccom,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_caddcfn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cres,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1st,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c2nd,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : n ∉ ((Wff.classEq (.cv a) (synC0c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_a, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0020 : n ∉ ((Wff.objEq a m)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_m, or_false, not_false_eq_true])
  have dv_cache_0021 : n ∉ ((Wff.classEq (.cv a) (synCplc (.cv m) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
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
          Finset.mem_singleton, fresh_n_ne_a, fresh_n_ne_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0022 : p ∉ ((synCnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0023 :
    p ∉
      ((Wff.neg (.classEq
            (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
              (synCplc (.cv m) (synC1c)))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_p_ne_m, fresh_p_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0024 :
    n ∉
      ((Wff.neg (.classEq
            (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
              (synCplc (.cv m) (synC1c)))
            (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_p, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0025 : n ∉ ((Wff.classEq (.cv a) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_a, fresh_n_not_A, or_false, not_false_eq_true])
  have dv_cache_0026 : q ∉ ((Class.cv p)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_q_ne_p, not_false_eq_true])
  have dv_cache_0027 : n ∉ ((Class.cv q)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_q, not_false_eq_true])
  have dv_cache_0028 :
    n ∉
      ((Wff.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
            (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_m, fresh_n_ne_q, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0029 :
    q ∉
      ((Wff.neg (.classEq
            (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
              (synCplc (.cv m) (synC1c)))
            (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_q_ne_m, fresh_q_ne_p, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0030 :
    q ∉
      ((synWa (.classMem (.cv m) (synCnnc)) (synWral n (synCnnc) (.neg
              (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
                (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_q_ne_m, fresh_q_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0031 :
    p ∉
      ((synWa (.classMem (.cv m) (synCnnc)) (synWral n (synCnnc) (.neg
              (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
                (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_p_ne_m, fresh_p_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0032 : a ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_A, not_false_eq_true])
  have dv_cache_0033 :
    a ∉
      ((synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0034 :
    m ∉
      ((synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_m_ne_a, fresh_m_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0035 :
    a ∉
      ((synWral n (synCnnc) (.neg (.classEq (synC0c)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_n, compact_fv_not_mem_empty,
          or_false, and_false, not_false_eq_true])
  have dv_cache_0036 :
    a ∉
      ((synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc A A) A)
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_not_A, fresh_a_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0037 :
    a ∉
      ((synWral p (synCnnc) (.neg (.classEq (synCplc
                (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
                (synCplc (.cv m) (synC1c)))
              (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_a_ne_m, fresh_a_ne_p,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0038 : a ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact (show a ≠ m from (by exact fresh_a_ne_m))
  have dv_cache_0039 : n ∉ (B).fv :=
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
        simp only [fresh_n_not_B, not_false_eq_true])
  have dv_cache_0040 :
    n ∉
      ((Wff.neg (.classEq (synCplc (synCplc A A) A)
            (synCplc (synCplc (synCplc B B) B) (synC1c))))).fv :=
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
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_n_not_A, fresh_n_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @gVex a
  have p0001 :=
    @gElcompl (.cv a)
      (synCima (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                    (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
                (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                      (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))) (synCnnc))
      p0000
  have p0002 :=
    @gElima n (.cv a)
      (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                  (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
              (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                    (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))))
      (synCnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    (Nominal.biimpRefl (synWbr (.cv n) (synCrn (synCtxp (synCrn (synCtxp
                (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                      (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                    (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                      (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))) (.cv a)))
  have p0004 :=
    @gElrn p (synCop (.cv n) (.cv a))
      (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                  (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      dv_cache_0004 dv_cache_0005
  have p0005 :=
    (Nominal.biimpRefl (synWbr (.cv p) (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn)
                (synCcnv (synCres (synC1st)
                    (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                  (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                    (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
        (synCop (.cv n) (.cv a))))
  have p0006 :=
    @gOteltxp (.cv p) (.cv n) (.cv a)
      (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
          (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))))
      (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
  have p0007 :=
    @gBitri
      (synWbr (.cv p) (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                  (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
              (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                    (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
        (synCop (.cv n) (.cv a)))
      (.classMem (synCop (.cv p) (synCop (.cv n) (.cv a))) (synCtxp (synCrn (synCtxp
              (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                    (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                  (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                    (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))))
      (synWa (.classMem (synCop (.cv p) (.cv n)) (synCrn (synCtxp (synCcom (synCaddcfn)
                (synCcnv (synCres (synC1st)
                    (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                  (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn)))))))) (.classMem (synCop (.cv p) (.cv a)) (synCcnv
            (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))))
      p0005 p0006
  have p0008 :=
    @gElrn2 q (synCop (.cv p) (.cv n))
      (synCtxp (synCcom (synCaddcfn) (synCcnv
            (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
        (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      dv_cache_0006 dv_cache_0007
  have p0009 :=
    @gOteltxp (.cv q) (.cv p) (.cv n)
      (synCcom (synCaddcfn) (synCcnv
          (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
      (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
  have p0010 :=
    @gOpelco x (.cv q) (.cv p) (synCaddcfn)
      (synCcnv (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0011 :=
    @gBrcnv (.cv q) (.cv x)
      (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))
  have p0012 :=
    @gBrres (.cv x) (.cv q) (synC1st)
      (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))
  have p0013 :=
    @gBitri
      (synWbr (.cv q) (synCcnv
          (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))) (.cv x))
      (synWbr (.cv x)
        (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))) (.cv q))
      (synWa (synWbr (.cv x) (synC1st) (.cv q))
        (.classMem (.cv x) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))
      p0011 p0012
  have p0014 := @gEliniseg (synC2nd) (synC1c) (.cv x)
  have p0015 :=
    @gAnbi2i (.classMem (.cv x) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))
      (synWbr (.cv x) (synC2nd) (synC1c)) (synWbr (.cv x) (synC1st) (.cv q)) p0014
  have p0016 := @gVex q
  have p0017 := @gN1cex
  have p0018 := @gOp1st2nd (.cv q) (synC1c) (.cv x) p0016 p0017
  have p0019 :=
    @gN3bitri
      (synWbr (.cv q) (synCcnv
          (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))) (.cv x))
      (synWa (synWbr (.cv x) (synC1st) (.cv q))
        (.classMem (.cv x) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))
      (synWa (synWbr (.cv x) (synC1st) (.cv q)) (synWbr (.cv x) (synC2nd) (synC1c)))
      (.classEq (.cv x) (synCop (.cv q) (synC1c))) p0013 p0015 p0018
  have p0020 :=
    @gAnbi1i
      (synWbr (.cv q) (synCcnv
          (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))) (.cv x))
      (.classEq (.cv x) (synCop (.cv q) (synC1c)))
      (synWbr (.cv x) (synCaddcfn) (.cv p)) p0019
  have p0021 :=
    @gExbii
      (synWa (synWbr (.cv q) (synCcnv
            (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))) (.cv x))
        (synWbr (.cv x) (synCaddcfn) (.cv p)))
      (synWa (.classEq (.cv x) (synCop (.cv q) (synC1c)))
        (synWbr (.cv x) (synCaddcfn) (.cv p)))
      x p0020
  have p0023 := @gOpex (.cv q) (synC1c) p0016 p0017
  have p0024 := @gBreq1 (.cv x) (synCop (.cv q) (synC1c)) (.cv p) (synCaddcfn)
  have p0025 :=
    @gCeqsexv (synWbr (.cv x) (synCaddcfn) (.cv p))
      (synWbr (synCop (.cv q) (synC1c)) (synCaddcfn) (.cv p)) x
      (synCop (.cv q) (synC1c)) dv_cache_0012 dv_cache_0013 p0023 p0024
  have p0026 :=
    @gBitri
      (synWex x (synWa (synWbr (.cv q) (synCcnv
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))
            (.cv x)) (synWbr (.cv x) (synCaddcfn) (.cv p))))
      (synWex x (synWa (.classEq (.cv x) (synCop (.cv q) (synC1c)))
          (synWbr (.cv x) (synCaddcfn) (.cv p))))
      (synWbr (synCop (.cv q) (synC1c)) (synCaddcfn) (.cv p)) p0021 p0025
  have p0028 := @gBraddcfn (.cv q) (synC1c) (.cv p) p0016 p0017
  have p0029 := @gEqcom (synCplc (.cv q) (synC1c)) (.cv p)
  have p0030 :=
    @gBitri (synWbr (synCop (.cv q) (synC1c)) (synCaddcfn) (.cv p))
      (.classEq (synCplc (.cv q) (synC1c)) (.cv p))
      (.classEq (.cv p) (synCplc (.cv q) (synC1c))) p0028 p0029
  have p0031 :=
    @gN3bitri
      (.classMem (synCop (.cv q) (.cv p)) (synCcom (synCaddcfn) (synCcnv
            (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))))
      (synWex x (synWa (synWbr (.cv q) (synCcnv
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))
            (.cv x)) (synWbr (.cv x) (synCaddcfn) (.cv p))))
      (synWbr (synCop (.cv q) (synC1c)) (synCaddcfn) (.cv p))
      (.classEq (.cv p) (synCplc (.cv q) (synC1c))) p0010 p0026 p0030
  have p0032 :=
    @gOpelcnv (.cv q) (.cv n)
      (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
  have p0033 := @gNncdiv3lem1 n q
  have p0034 :=
    @gBitri
      (.classMem (synCop (.cv q) (.cv n)) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      (.classMem (synCop (.cv n) (.cv q)) (synCrn (synCin (synCins3 (synCcnv (synCima
                  (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      (.classEq (.cv q) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) p0032 p0033
  have p0035 :=
    @gAnbi12i
      (.classMem (synCop (.cv q) (.cv p)) (synCcom (synCaddcfn) (synCcnv
            (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))))
      (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
      (.classMem (synCop (.cv q) (.cv n)) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      (.classEq (.cv q) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) p0031 p0034
  have p0036 :=
    @gAncom (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
      (.classEq (.cv q) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
  have p0037 :=
    @gN3bitri
      (.classMem (synCop (.cv q) (synCop (.cv p) (.cv n))) (synCtxp (synCcom (synCaddcfn)
            (synCcnv
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
          (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))))
      (synWa (.classMem (synCop (.cv q) (.cv p)) (synCcom (synCaddcfn) (synCcnv
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))))
        (.classMem (synCop (.cv q) (.cv n)) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                    (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))))
      (synWa (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
        (.classEq (.cv q) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))))
      (synWa (.classEq (.cv q) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv p) (synCplc (.cv q) (synC1c))))
      p0009 p0035 p0036
  have p0038 :=
    @gExbii
      (.classMem (synCop (.cv q) (synCop (.cv p) (.cv n))) (synCtxp (synCcom (synCaddcfn)
            (synCcnv
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
          (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))))
      (synWa (.classEq (.cv q) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv p) (synCplc (.cv q) (synC1c))))
      q p0037
  have p0039 := @gVex n
  have p0040 := @gAddcex (.cv n) (.cv n) p0039 p0039
  have p0041 := @gAddcex (synCplc (.cv n) (.cv n)) (.cv n) p0040 p0039
  have p0042 := @gAddceq1 (.cv q) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)
  have p0043 :=
    @gEqeq2d (.classEq (.cv q) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (synCplc (.cv q) (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) (.cv p) p0042
  have p0044 :=
    @gCeqsexv (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
      (.classEq (.cv p) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      q (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) dv_cache_0014 dv_cache_0015 p0041
      p0043
  have p0045 :=
    @gN3bitri
      (.classMem (synCop (.cv p) (.cv n)) (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
            (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))))
      (synWex q (.classMem (synCop (.cv q) (synCop (.cv p) (.cv n))) (synCtxp
            (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                  (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))))
      (synWex q (synWa (.classEq (.cv q) (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv p) (synCplc (.cv q) (synC1c)))))
      (.classEq (.cv p) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      p0008 p0038 p0044
  have p0046 :=
    @gOpelcnv (.cv p) (.cv a)
      (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
  have p0047 := @gNncdiv3lem1 a p
  have p0048 :=
    @gBitri
      (.classMem (synCop (.cv p) (.cv a)) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      (.classMem (synCop (.cv a) (.cv p)) (synCrn (synCin (synCins3 (synCcnv (synCima
                  (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      (.classEq (.cv p) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))) p0046 p0047
  have p0049 :=
    @gAnbi12i
      (.classMem (synCop (.cv p) (.cv n)) (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
            (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))))
      (.classEq (.cv p) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classMem (synCop (.cv p) (.cv a)) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      (.classEq (.cv p) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))) p0045 p0048
  have p0050 :=
    @gAncom
      (.classEq (.cv p) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (.cv p) (synCplc (synCplc (.cv a) (.cv a)) (.cv a)))
  have p0051 :=
    @gN3bitri
      (synWbr (.cv p) (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                  (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
              (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                    (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
        (synCop (.cv n) (.cv a)))
      (synWa (.classMem (synCop (.cv p) (.cv n)) (synCrn (synCtxp (synCcom (synCaddcfn)
                (synCcnv (synCres (synC1st)
                    (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                  (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn)))))))) (.classMem (synCop (.cv p) (.cv a)) (synCcnv
            (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))))
      (synWa (.classEq (.cv p)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq (.cv p) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))))
      (synWa (.classEq (.cv p) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))) (.classEq (.cv p)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      p0007 p0049 p0050
  have p0052 :=
    @gExbii
      (synWbr (.cv p) (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                  (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
              (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                    (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
        (synCop (.cv n) (.cv a)))
      (synWa (.classEq (.cv p) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))) (.classEq (.cv p)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      p p0051
  have p0053 := @gAddcex (.cv a) (.cv a) p0000 p0000
  have p0054 := @gAddcex (synCplc (.cv a) (.cv a)) (.cv a) p0053 p0000
  have p0055 :=
    @gEqeq1 (.cv p) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
  have p0056 :=
    @gCeqsexv
      (.classEq (.cv p) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      p (synCplc (synCplc (.cv a) (.cv a)) (.cv a)) dv_cache_0016 dv_cache_0017 p0054
      p0055
  have p0057 :=
    @gN3bitri
      (.classMem (synCop (.cv n) (.cv a)) (synCrn (synCtxp (synCrn (synCtxp
                (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                      (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                    (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                      (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))))
      (synWex p (synWbr (.cv p) (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                    (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
                (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                      (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
          (synCop (.cv n) (.cv a))))
      (synWex p (synWa (.classEq (.cv p) (synCplc (synCplc (.cv a) (.cv a)) (.cv a)))
          (.classEq (.cv p)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      p0004 p0052 p0056
  have p0058 :=
    @gBitri
      (synWbr (.cv n) (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                    (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
                (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                      (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))) (.cv a))
      (.classMem (synCop (.cv n) (.cv a)) (synCrn (synCtxp (synCrn (synCtxp
                (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                      (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                    (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                      (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))))
      (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      p0003 p0057
  have p0059 :=
    @gRexbii
      (synWbr (.cv n) (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                    (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
                (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                      (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))) (.cv a))
      (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      n (synCnnc) p0058
  have p0060 :=
    @gDfrex2
      (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      n (synCnnc)
  have p0061 :=
    @gN3bitrri
      (.classMem (.cv a) (synCima (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn)
                    (synCcnv (synCres (synC1st)
                        (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv
                    (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                  (synCtxp (synCcnv (synC1st))
                                    (synCin (synC1st) (synC2nd)))) (synC2nd))
                              (synCaddcfn)))) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                        (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCnnc)))
      (synWrex n (synCnnc) (synWbr (.cv n) (synCrn (synCtxp (synCrn (synCtxp
                  (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                        (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv
                    (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                  (synCtxp (synCcnv (synC1st))
                                    (synCin (synC1st) (synC2nd)))) (synC2nd))
                              (synCaddcfn)))) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                        (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (.cv a)))
      (synWrex n (synCnnc) (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.neg (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))))
      p0002 p0059 p0060
  have p0062 :=
    @gCon1bii
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (.classMem (.cv a) (synCima (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn)
                    (synCcnv (synCres (synC1st)
                        (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv
                    (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                  (synCtxp (synCcnv (synC1st))
                                    (synCin (synC1st) (synC2nd)))) (synC2nd))
                              (synCaddcfn)))) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                        (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCnnc)))
      p0061
  have p0063 :=
    @gBitri
      (.classMem (.cv a) (synCcompl (synCima (synCrn (synCtxp (synCrn (synCtxp
                    (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                          (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv
                      (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                    (synCtxp (synCcnv (synC1st))
                                      (synCin (synC1st) (synC2nd)))) (synC2nd))
                                (synCaddcfn)))) (synCima
                            (synCtxp (synCcom (synC1st) (synC1st))
                              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                            (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                          (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCnnc))))
      (.neg (.classMem (.cv a) (synCima (synCrn (synCtxp (synCrn (synCtxp
                    (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                          (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv
                      (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                    (synCtxp (synCcnv (synC1st))
                                      (synCin (synC1st) (synC2nd)))) (synC2nd))
                                (synCaddcfn)))) (synCima
                            (synCtxp (synCcom (synC1st) (synC1st))
                              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                            (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                          (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCnnc))))
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      p0001 p0062
  have p0064 :=
    @gEqabi
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      a
      (synCcompl (synCima (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn)
                    (synCcnv (synCres (synC1st)
                        (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv
                    (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                  (synCtxp (synCcnv (synC1st))
                                    (synCin (synC1st) (synC2nd)))) (synC2nd))
                              (synCaddcfn)))) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                        (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCnnc)))
      dv_cache_0018 p0063
  have p0065 := @gAddcfnex
  have p0066 := @gN1stex
  have p0067 := @gN2ndex
  have p0068 := @gCnvex (synC2nd) p0067
  have p0069 := @gSnex (synC1c)
  have p0070 := @gImaex (synCcnv (synC2nd)) (synCsn (synC1c)) p0068 p0069
  have p0071 :=
    @gResex (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))) p0066 p0070
  have p0072 :=
    @gCnvex (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))
      p0071
  have p0073 :=
    @gCoex (synCaddcfn)
      (synCcnv (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))
      p0065 p0072
  have p0075 := @gCnvex (synC1st) p0066
  have p0078 := @gInex (synC1st) (synC2nd) p0066 p0067
  have p0079 := @gTxpex (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)) p0075 p0078
  have p0080 :=
    @gRnex (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))) p0079
  have p0082 :=
    @gTxpex (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
      (synC2nd) p0080 p0067
  have p0084 :=
    @gImaex
      (synCtxp (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
        (synC2nd))
      (synCaddcfn) p0082 p0065
  have p0085 :=
    @gCnvex
      (synCima (synCtxp
          (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd)))) (synC2nd))
        (synCaddcfn))
      p0084
  have p0086 :=
    @gIns3ex
      (synCcnv (synCima (synCtxp
            (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
            (synC2nd)) (synCaddcfn)))
      p0085
  have p0089 := @gCoex (synC1st) (synC1st) p0066 p0066
  have p0092 := @gCoex (synC2nd) (synC1st) p0067 p0066
  have p0094 := @gTxpex (synCcom (synC2nd) (synC1st)) (synC2nd) p0092 p0067
  have p0095 :=
    @gTxpex (synCcom (synC1st) (synC1st))
      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)) p0089 p0094
  have p0097 :=
    @gImaex
      (synCtxp (synCcom (synC1st) (synC1st))
        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
      (synCaddcfn) p0095 p0065
  have p0098 :=
    @gInex
      (synCins3 (synCcnv (synCima (synCtxp
              (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
              (synC2nd)) (synCaddcfn))))
      (synCima (synCtxp (synCcom (synC1st) (synC1st))
          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))
      p0086 p0097
  have p0099 :=
    @gRnex
      (synCin (synCins3 (synCcnv (synCima (synCtxp
                (synCrn (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                (synC2nd)) (synCaddcfn)))) (synCima
          (synCtxp (synCcom (synC1st) (synC1st))
            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))
      p0098
  have p0100 :=
    @gCnvex
      (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                    (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                  (synC2nd)) (synCaddcfn)))) (synCima
            (synCtxp (synCcom (synC1st) (synC1st))
              (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))
      p0099
  have p0101 :=
    @gTxpex
      (synCcom (synCaddcfn) (synCcnv
          (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
      (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      p0073 p0100
  have p0102 :=
    @gRnex
      (synCtxp (synCcom (synCaddcfn) (synCcnv
            (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
        (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      p0101
  have p0103 :=
    @gTxpex
      (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
              (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
          (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                          (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                        (synC2nd)) (synCaddcfn)))) (synCima
                  (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))))
      (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                      (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                    (synC2nd)) (synCaddcfn)))) (synCima
              (synCtxp (synCcom (synC1st) (synC1st))
                (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))
      p0102 p0100
  have p0104 :=
    @gRnex
      (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv (synCres (synC1st)
                  (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv (synCrn
                (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                            (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                          (synC2nd)) (synCaddcfn)))) (synCima
                    (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                  (synCima (synCtxp (synCrn
                        (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                      (synC2nd)) (synCaddcfn)))) (synCima
                (synCtxp (synCcom (synC1st) (synC1st))
                  (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn))))))
      p0103
  have p0105 := @gNncex
  have p0106 :=
    @gImaex
      (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                  (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
              (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                              (synCtxp (synCcnv (synC1st)) (synCin (synC1st) (synC2nd))))
                            (synC2nd)) (synCaddcfn)))) (synCima
                      (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                    (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                            (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                (synCima (synCtxp (synCcom (synC1st) (synC1st))
                    (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd))) (synCaddcfn)))))))
      (synCnnc) p0104 p0105
  have p0107 :=
    @gComplex
      (synCima (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn) (synCcnv
                    (synCres (synC1st) (synCima (synCcnv (synC2nd)) (synCsn (synC1c))))))
                (synCcnv (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                (synCtxp (synCcnv (synC1st))
                                  (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                      (synCima (synCtxp (synCcom (synC1st) (synC1st))
                          (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                        (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                      (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                              (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                  (synCima (synCtxp (synCcom (synC1st) (synC1st))
                      (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                    (synCaddcfn))))))) (synCnnc))
      p0106
  have p0108 :=
    @gEqeltrri
      (synCcompl (synCima (synCrn (synCtxp (synCrn (synCtxp (synCcom (synCaddcfn)
                    (synCcnv (synCres (synC1st)
                        (synCima (synCcnv (synC2nd)) (synCsn (synC1c)))))) (synCcnv
                    (synCrn (synCin (synCins3 (synCcnv (synCima (synCtxp (synCrn
                                  (synCtxp (synCcnv (synC1st))
                                    (synCin (synC1st) (synC2nd)))) (synC2nd))
                              (synCaddcfn)))) (synCima
                          (synCtxp (synCcom (synC1st) (synC1st))
                            (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                          (synCaddcfn))))))) (synCcnv (synCrn (synCin (synCins3 (synCcnv
                        (synCima (synCtxp (synCrn (synCtxp (synCcnv (synC1st))
                                (synCin (synC1st) (synC2nd)))) (synC2nd)) (synCaddcfn))))
                    (synCima (synCtxp (synCcom (synC1st) (synC1st))
                        (synCtxp (synCcom (synC2nd) (synC1st)) (synC2nd)))
                      (synCaddcfn))))))) (synCnnc)))
      (.cab a (synWral n (synCnnc) (.neg
            (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))))
      (synCvv) p0064 p0107
  have p0109 := @gAddceq12 (.cv a) (.cv a) (synC0c) (synC0c)
  have p0110 :=
    @gAnidms (.classEq (.cv a) (synC0c))
      (.classEq (synCplc (.cv a) (.cv a)) (synCplc (synC0c) (synC0c))) p0109
  have p0111 := @gId (.classEq (.cv a) (synC0c))
  have p0112 :=
    @gAddceq12d (.classEq (.cv a) (synC0c)) (synCplc (.cv a) (.cv a))
      (synCplc (synC0c) (synC0c)) (.cv a) (synC0c) p0110 p0111
  have p0113 := @gAddcid1 (synCplc (synC0c) (synC0c))
  have p0114 := @gAddcid2 (synC0c)
  have p0115 :=
    @gEqtri (synCplc (synCplc (synC0c) (synC0c)) (synC0c))
      (synCplc (synC0c) (synC0c)) (synC0c) p0113 p0114
  have p0116 :=
    @gSyl6eq (.classEq (.cv a) (synC0c)) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
      (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC0c) p0112 p0115
  have p0117 :=
    @gEqeq1d (.classEq (.cv a) (synC0c)) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
      (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) p0116
  have p0118 :=
    @gNotbid (.classEq (.cv a) (synC0c))
      (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      p0117
  have p0119 :=
    @gRalbidv (.classEq (.cv a) (synC0c))
      (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.neg (.classEq (synC0c)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      n (synCnnc) dv_cache_0019 p0118
  have p0120 := @gAddceq12 (.cv a) (.cv a) (.cv m) (.cv m)
  have p0121_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq a m) (.objEq a m))
        (.classEq (synCplc (.cv a) (.cv a)) (synCplc (.cv m) (.cv m)))) :=
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
      p0120
  have p0121 :=
    @gAnidms (.objEq a m)
      (.classEq (synCplc (.cv a) (.cv a)) (synCplc (.cv m) (.cv m))) p0121_e00_recanon
  have p0122 := @gId (.objEq a m)
  have p0123_e01_recanon : Nominal.NPrf (.imp (.objEq a m) (.classEq (.cv a) (.cv m))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0122
  have p0123 :=
    @gAddceq12d (.objEq a m) (synCplc (.cv a) (.cv a)) (synCplc (.cv m) (.cv m))
      (.cv a) (.cv m) p0121 p0123_e01_recanon
  have p0124 :=
    @gEqeq1d (.objEq a m) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
      (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) p0123
  have p0125 :=
    @gNotbid (.objEq a m)
      (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      p0124
  have p0126 :=
    @gRalbidv (.objEq a m)
      (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      n (synCnnc) dv_cache_0020 p0125
  have p0127 :=
    @gAddceq12 (.cv a) (.cv a) (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))
  have p0128 :=
    @gAnidms (.classEq (.cv a) (synCplc (.cv m) (synC1c)))
      (.classEq (synCplc (.cv a) (.cv a))
        (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))))
      p0127
  have p0129 := @gId (.classEq (.cv a) (synCplc (.cv m) (synC1c)))
  have p0130 :=
    @gAddceq12d (.classEq (.cv a) (synCplc (.cv m) (synC1c)))
      (synCplc (.cv a) (.cv a))
      (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))) (.cv a)
      (synCplc (.cv m) (synC1c)) p0128 p0129
  have p0131 :=
    @gEqeq1d (.classEq (.cv a) (synCplc (.cv m) (synC1c)))
      (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
      (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
        (synCplc (.cv m) (synC1c)))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) p0130
  have p0132 :=
    @gNotbid (.classEq (.cv a) (synCplc (.cv m) (synC1c)))
      (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c)))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      p0131
  have p0133 :=
    @gRalbidv (.classEq (.cv a) (synCplc (.cv m) (synC1c)))
      (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c)))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      n (synCnnc) dv_cache_0021 p0132
  have p0134 := @gAddceq12 (.cv n) (.cv n) (.cv p) (.cv p)
  have p0135_e00_recanon :
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
      p0134
  have p0135 :=
    @gAnidms (.objEq n p)
      (.classEq (synCplc (.cv n) (.cv n)) (synCplc (.cv p) (.cv p))) p0135_e00_recanon
  have p0136 := @gId (.objEq n p)
  have p0137_e01_recanon : Nominal.NPrf (.imp (.objEq n p) (.classEq (.cv n) (.cv p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0136
  have p0137 :=
    @gAddceq12d (.objEq n p) (synCplc (.cv n) (.cv n)) (synCplc (.cv p) (.cv p))
      (.cv n) (.cv p) p0135 p0137_e01_recanon
  have p0138 :=
    @gAddceq1d (.objEq n p) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
      (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c) p0137
  have p0139 :=
    @gEqeq2d (.objEq n p)
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
      (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))
      (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
        (synCplc (.cv m) (synC1c)))
      p0138
  have p0140 :=
    @gNotbid (.objEq n p)
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c)))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c)))
        (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c)))
      p0139
  have p0141 :=
    @gCbvralv
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c)))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c)))
          (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))))
      n p (synCnnc) dv_cache_0003 dv_cache_0022 dv_cache_0023 dv_cache_0024 p0140
  have p0142 :=
    @gSyl6bb (.classEq (.cv a) (synCplc (.cv m) (synC1c)))
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (synWral n (synCnnc) (.neg (.classEq
            (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
              (synCplc (.cv m) (synC1c)))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (synWral p (synCnnc) (.neg (.classEq
            (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
              (synCplc (.cv m) (synC1c)))
            (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c)))))
      p0133 p0141
  have p0143 := @gAddceq12 (.cv a) (.cv a) A A
  have p0144 :=
    @gAnidms (.classEq (.cv a) A) (.classEq (synCplc (.cv a) (.cv a)) (synCplc A A))
      p0143
  have p0145 := @gId (.classEq (.cv a) A)
  have p0146 :=
    @gAddceq12d (.classEq (.cv a) A) (synCplc (.cv a) (.cv a)) (synCplc A A) (.cv a) A
      p0144 p0145
  have p0147 :=
    @gEqeq1d (.classEq (.cv a) A) (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
      (synCplc (synCplc A A) A)
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) p0146
  have p0148 :=
    @gNotbid (.classEq (.cv a) A)
      (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc A A) A)
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      p0147
  have p0149 :=
    @gRalbidv (.classEq (.cv a) A)
      (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.neg (.classEq (synCplc (synCplc A A) A)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      n (synCnnc) dv_cache_0025 p0148
  have p0150 := @gN1ne0c
  have p0151 := (Nominal.biimpRefl (synWne (synC1c) (synC0c)))
  have p0152 :=
    @gMpbi (synWne (synC1c) (synC0c)) (.neg (.classEq (synC1c) (synC0c))) p0150
      p0151
  have p0153 :=
    @gIntnan (.classEq (synC1c) (synC0c))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC0c)) p0152
  have p0154 :=
    @gEqcom (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
  have p0155 := @gNncaddccl (.cv n) (.cv n)
  have p0156 :=
    @gAnidms (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) p0155
  have p0157 := @gNncaddccl (synCplc (.cv n) (.cv n)) (.cv n)
  have p0158 :=
    @gMpancom (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCnnc)) p0156 p0157
  have p0159 := @gNnnc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
  have p0160 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCncs)) p0158 p0159
  have p0161 := @gN1cnc
  have p0162 := @gAddceq0 (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)
  have p0163 :=
    @gSylancl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCncs))
      (.classMem (synC1c) (synCncs))
      (synWb (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
          (synC0c)) (synWa (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC0c))
          (.classEq (synC1c) (synC0c))))
      p0160 p0161 p0162
  have p0164 :=
    @gSyl5bb
      (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) (synC0c))
      (.classMem (.cv n) (synCnnc))
      (synWa (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC0c))
        (.classEq (synC1c) (synC0c)))
      p0154 p0163
  have p0165 :=
    @gMtbiri (.classMem (.cv n) (synCnnc))
      (.classEq (synC0c) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (synWa (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC0c))
        (.classEq (synC1c) (synC0c)))
      p0153 p0164
  have p0166 :=
    @gRgen
      (.neg (.classEq (synC0c)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      n (synCnnc) p0165
  have p0167 := @gNnc0suc q (.cv p) dv_cache_0026
  have p0168 :=
    @gN0cnsuc (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (.cv m))
  have p0169 :=
    (Nominal.biimpRefl (synWne
        (synCplc (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (.cv m)) (synC1c))
        (synC0c)))
  have p0170 :=
    @gMpbi
      (synWne (synCplc (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (.cv m))
          (synC1c)) (synC0c))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (.cv m))
            (synC1c)) (synC0c)))
      p0168 p0169
  have p0171 :=
    @gA1i
      (.neg (.classEq
          (synCplc (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (.cv m))
            (synC1c)) (synC0c)))
      (.classMem (.cv m) (synCnnc)) p0170
  have p0172 := @gAddcass (synCplc (.cv m) (synC1c)) (.cv m) (synC1c)
  have p0173 :=
    @gAddceq1i (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (synC1c))
      (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))) (.cv m) p0172
  have p0174 :=
    @gAddc32 (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (synC1c) (.cv m)
  have p0175 :=
    @gEqtr3i
      (synCplc (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (synC1c)) (.cv m))
      (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))) (.cv m))
      (synCplc (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (.cv m)) (synC1c))
      p0173 p0174
  have p0176 :=
    @gEqeq1i
      (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))) (.cv m))
      (synCplc (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (.cv m)) (synC1c))
      (synC0c) p0175
  have p0177 :=
    @gSylnibr (.classMem (.cv m) (synCnnc))
      (.classEq (synCplc (synCplc (synCplc (synCplc (.cv m) (synC1c)) (.cv m)) (.cv m))
          (synC1c)) (synC0c))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (.cv m)) (synC0c))
      p0171 p0176
  have p0178 := @gPeano2 (.cv m)
  have p0179 := @gNncaddccl (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))
  have p0180 :=
    @gAnidms (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      (.classMem (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
        (synCnnc))
      p0179
  have p0181 :=
    @gSyl (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (.cv m) (synC1c)) (synCnnc))
      (.classMem (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
        (synCnnc))
      p0178 p0180
  have p0182 :=
    @gNncaddccl (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
      (.cv m)
  have p0183 :=
    @gMpancom
      (.classMem (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
        (synCnnc))
      (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (.cv m)) (synCnnc))
      p0181 p0182
  have p0184 := @gPeano1
  have p0185 :=
    @gSuc11nnc
      (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c))) (.cv m))
      (synC0c)
  have p0186 :=
    @gSylancl (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (.cv m)) (synCnnc))
      (.classMem (synC0c) (synCnnc))
      (synWb (.classEq (synCplc
            (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
              (.cv m)) (synC1c)) (synCplc (synC0c) (synC1c))) (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (.cv m)) (synC0c)))
      p0183 p0184 p0185
  have p0187 :=
    @gMtbird (.classMem (.cv m) (synCnnc))
      (.classEq (synCplc
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (.cv m)) (synC1c)) (synCplc (synC0c) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (.cv m)) (synC0c))
      p0177 p0186
  have p0188 :=
    @gAddcass (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
      (.cv m) (synC1c)
  have p0189 :=
    @gEqeq1i
      (synCplc (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (.cv m)) (synC1c))
      (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
        (synCplc (.cv m) (synC1c)))
      (synCplc (synC0c) (synC1c)) p0188
  have p0190 :=
    @gSylnib (.classMem (.cv m) (synCnnc))
      (.classEq (synCplc
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (.cv m)) (synC1c)) (synCplc (synC0c) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c))) (synCplc (synC0c) (synC1c)))
      p0187 p0189
  have p0191 := @gAddceq12 (.cv p) (.cv p) (synC0c) (synC0c)
  have p0192 :=
    @gAnidms (.classEq (.cv p) (synC0c))
      (.classEq (synCplc (.cv p) (.cv p)) (synCplc (synC0c) (synC0c))) p0191
  have p0193 := @gId (.classEq (.cv p) (synC0c))
  have p0194 :=
    @gAddceq12d (.classEq (.cv p) (synC0c)) (synCplc (.cv p) (.cv p))
      (synCplc (synC0c) (synC0c)) (.cv p) (synC0c) p0192 p0193
  have p0195 :=
    @gSyl6eq (.classEq (.cv p) (synC0c)) (synCplc (synCplc (.cv p) (.cv p)) (.cv p))
      (synCplc (synCplc (synC0c) (synC0c)) (synC0c)) (synC0c) p0194 p0115
  have p0196 :=
    @gAddceq1d (.classEq (.cv p) (synC0c)) (synCplc (synCplc (.cv p) (.cv p)) (.cv p))
      (synC0c) (synC1c) p0195
  have p0197 :=
    @gEqeq2d (.classEq (.cv p) (synC0c))
      (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))
      (synCplc (synC0c) (synC1c))
      (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
        (synCplc (.cv m) (synC1c)))
      p0196
  have p0198 :=
    @gNotbid (.classEq (.cv p) (synC0c))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c)))
        (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c))) (synCplc (synC0c) (synC1c)))
      p0197
  have p0199 :=
    @gSyl5ibrcom (.classMem (.cv m) (synCnnc))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c)))
          (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))))
      (.classEq (.cv p) (synC0c))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c))) (synCplc (synC0c) (synC1c))))
      p0190 p0198
  have p0200 :=
    @gAdantr (.classMem (.cv m) (synCnnc))
      (.imp (.classEq (.cv p) (synC0c)) (.neg (.classEq
            (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
              (synCplc (.cv m) (synC1c)))
            (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c)))))
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      p0199
  have p0201 := @gAddceq12 (.cv n) (.cv n) (.cv q) (.cv q)
  have p0202_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objEq n q) (.objEq n q))
        (.classEq (synCplc (.cv n) (.cv n)) (synCplc (.cv q) (.cv q)))) :=
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
      p0201
  have p0202 :=
    @gAnidms (.objEq n q)
      (.classEq (synCplc (.cv n) (.cv n)) (synCplc (.cv q) (.cv q))) p0202_e00_recanon
  have p0203 := @gId (.objEq n q)
  have p0204_e01_recanon : Nominal.NPrf (.imp (.objEq n q) (.classEq (.cv n) (.cv q))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0203
  have p0204 :=
    @gAddceq12d (.objEq n q) (synCplc (.cv n) (.cv n)) (synCplc (.cv q) (.cv q))
      (.cv n) (.cv q) p0202 p0204_e01_recanon
  have p0205 :=
    @gAddceq1d (.objEq n q) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
      (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c) p0204
  have p0206 :=
    @gEqeq2d (.objEq n q)
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
      (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))
      (synCplc (synCplc (.cv m) (.cv m)) (.cv m)) p0205
  have p0207 :=
    @gNotbid (.objEq n q)
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c)))
      p0206
  have p0208_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv n) (.cv q)) (synWb (.neg
            (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))) (.neg
            (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
              (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0207
  have p0208 :=
    @gRspcv
      (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
          (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))))
      n (.cv q) (synCnnc) dv_cache_0027 dv_cache_0003 dv_cache_0028 p0208_e00_recanon
  have p0209 :=
    @gAdantl (.classMem (.cv q) (synCnnc))
      (.imp (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))) (.neg
          (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
            (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c)))))
      (.classMem (.cv m) (synCnnc)) p0208
  have p0210 := @gAddc6 (.cv m) (synC1c) (.cv m) (synC1c) (.cv m) (synC1c)
  have p0211 := @gAddc6 (.cv q) (synC1c) (.cv q) (synC1c) (.cv q) (synC1c)
  have p0212 :=
    @gAddceq1i
      (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
        (synCplc (.cv q) (synC1c)))
      (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q))
        (synCplc (synCplc (synC1c) (synC1c)) (synC1c)))
      (synC1c) p0211
  have p0213 :=
    @gAddc32 (synCplc (synCplc (.cv q) (.cv q)) (.cv q))
      (synCplc (synCplc (synC1c) (synC1c)) (synC1c)) (synC1c)
  have p0214 :=
    @gEqtri
      (synCplc (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synCplc (.cv q) (synC1c))) (synC1c))
      (synCplc (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q))
          (synCplc (synCplc (synC1c) (synC1c)) (synC1c))) (synC1c))
      (synCplc (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))
        (synCplc (synCplc (synC1c) (synC1c)) (synC1c)))
      p0212 p0213
  have p0215 :=
    @gEqeq12i
      (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
        (synCplc (.cv m) (synC1c)))
      (synCplc (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
        (synCplc (synCplc (synC1c) (synC1c)) (synC1c)))
      (synCplc (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synCplc (.cv q) (synC1c))) (synC1c))
      (synCplc (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))
        (synCplc (synCplc (synC1c) (synC1c)) (synC1c)))
      p0210 p0214
  have p0216 := @gNncaddccl (.cv m) (.cv m)
  have p0217 :=
    @gAnidms (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (.cv m) (.cv m)) (synCnnc)) p0216
  have p0218 := @gNncaddccl (synCplc (.cv m) (.cv m)) (.cv m)
  have p0219 :=
    @gMpancom (.classMem (synCplc (.cv m) (.cv m)) (synCnnc))
      (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (synCplc (.cv m) (.cv m)) (.cv m)) (synCnnc)) p0217 p0218
  have p0220 := @gNncaddccl (.cv q) (.cv q)
  have p0221 :=
    @gAnidms (.classMem (.cv q) (synCnnc))
      (.classMem (synCplc (.cv q) (.cv q)) (synCnnc)) p0220
  have p0222 := @gNncaddccl (synCplc (.cv q) (.cv q)) (.cv q)
  have p0223 :=
    @gMpancom (.classMem (synCplc (.cv q) (.cv q)) (synCnnc))
      (.classMem (.cv q) (synCnnc))
      (.classMem (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synCnnc)) p0221 p0222
  have p0224 := @gPeano2 (synCplc (synCplc (.cv q) (.cv q)) (.cv q))
  have p0225 :=
    @gSyl (.classMem (.cv q) (synCnnc))
      (.classMem (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c)) (synCnnc))
      p0223 p0224
  have p0226 := @gN1cnnc
  have p0228 := @gNncaddccl (synC1c) (synC1c)
  have p0229 :=
    @gMp2an (.classMem (synC1c) (synCnnc)) (.classMem (synC1c) (synCnnc))
      (.classMem (synCplc (synC1c) (synC1c)) (synCnnc)) p0226 p0226 p0228
  have p0231 := @gNncaddccl (synCplc (synC1c) (synC1c)) (synC1c)
  have p0232 :=
    @gMp2an (.classMem (synCplc (synC1c) (synC1c)) (synCnnc))
      (.classMem (synC1c) (synCnnc))
      (.classMem (synCplc (synCplc (synC1c) (synC1c)) (synC1c)) (synCnnc)) p0229
      p0226 p0231
  have p0233 :=
    @gAddccan1 (synCplc (synCplc (synC1c) (synC1c)) (synC1c))
      (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
      (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))
  have p0234 :=
    @gMp3an3 (.classMem (synCplc (synCplc (.cv m) (.cv m)) (.cv m)) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c)) (synCnnc))
      (.classMem (synCplc (synCplc (synC1c) (synC1c)) (synC1c)) (synCnnc))
      (synWb (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
            (synCplc (synCplc (synC1c) (synC1c)) (synC1c)))
          (synCplc (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))
            (synCplc (synCplc (synC1c) (synC1c)) (synC1c))))
        (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
          (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))))
      p0232 p0233
  have p0235 :=
    @gSyl2an (.classMem (.cv m) (synCnnc))
      (.classMem (synCplc (synCplc (.cv m) (.cv m)) (.cv m)) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c)) (synCnnc))
      (synWb (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
            (synCplc (synCplc (synC1c) (synC1c)) (synC1c)))
          (synCplc (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))
            (synCplc (synCplc (synC1c) (synC1c)) (synC1c))))
        (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
          (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))))
      (.classMem (.cv q) (synCnnc)) p0219 p0225 p0234
  have p0236 :=
    @gSyl5bb
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c))) (synCplc
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synCplc (.cv q) (synC1c))) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
          (synCplc (synCplc (synC1c) (synC1c)) (synC1c)))
        (synCplc (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c))
          (synCplc (synCplc (synC1c) (synC1c)) (synC1c))))
      (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv q) (synCnnc)))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c)))
      p0215 p0235
  have p0237 :=
    @gBiimpd (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv q) (synCnnc)))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c))) (synCplc
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synCplc (.cv q) (synC1c))) (synC1c)))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c)))
      p0236
  have p0238 :=
    @gNsyld (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv q) (synCnnc)))
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
        (synCplc (synCplc (synCplc (.cv q) (.cv q)) (.cv q)) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c))) (synCplc
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synCplc (.cv q) (synC1c))) (synC1c)))
      p0209 p0237
  have p0239 :=
    @gImp (synWa (.classMem (.cv m) (synCnnc)) (.classMem (.cv q) (synCnnc)))
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c))) (synCplc
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synCplc (.cv q) (synC1c))) (synC1c))))
      p0238
  have p0240 :=
    @gAn32s (.classMem (.cv m) (synCnnc)) (.classMem (.cv q) (synCnnc))
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c))) (synCplc
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synCplc (.cv q) (synC1c))) (synC1c))))
      p0239
  have p0241 :=
    @gAddceq12 (.cv p) (.cv p) (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))
  have p0242 :=
    @gAnidms (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
      (.classEq (synCplc (.cv p) (.cv p))
        (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))))
      p0241
  have p0243 := @gId (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
  have p0244 :=
    @gAddceq12d (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
      (synCplc (.cv p) (.cv p))
      (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c))) (.cv p)
      (synCplc (.cv q) (synC1c)) p0242 p0243
  have p0245 :=
    @gAddceq1d (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
      (synCplc (synCplc (.cv p) (.cv p)) (.cv p))
      (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
        (synCplc (.cv q) (synC1c)))
      (synC1c) p0244
  have p0246 :=
    @gEqeq2d (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
      (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))
      (synCplc (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
          (synCplc (.cv q) (synC1c))) (synC1c))
      (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
        (synCplc (.cv m) (synC1c)))
      p0245
  have p0247 :=
    @gNotbid (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c)))
        (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
          (synCplc (.cv m) (synC1c))) (synCplc
          (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
            (synCplc (.cv q) (synC1c))) (synC1c)))
      p0246
  have p0248 :=
    @gSyl5ibrcom
      (synWa (synWa (.classMem (.cv m) (synCnnc)) (synWral n (synCnnc) (.neg
              (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
                (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))))
        (.classMem (.cv q) (synCnnc)))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c)))
          (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))))
      (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c))) (synCplc
            (synCplc (synCplc (synCplc (.cv q) (synC1c)) (synCplc (.cv q) (synC1c)))
              (synCplc (.cv q) (synC1c))) (synC1c))))
      p0240 p0247
  have p0249 :=
    @gRexlimdva
      (synWa (.classMem (.cv m) (synCnnc)) (synWral n (synCnnc) (.neg
            (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))))
      (.classEq (.cv p) (synCplc (.cv q) (synC1c)))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c)))
          (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))))
      q (synCnnc) dv_cache_0029 dv_cache_0030 p0248
  have p0250 :=
    @gJaod
      (synWa (.classMem (.cv m) (synCnnc)) (synWral n (synCnnc) (.neg
            (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))))
      (.classEq (.cv p) (synC0c))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c)))
          (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))))
      (synWrex q (synCnnc) (.classEq (.cv p) (synCplc (.cv q) (synC1c)))) p0200 p0249
  have p0251 :=
    @gSyl5bi (.classMem (.cv p) (synCnnc))
      (synWo (.classEq (.cv p) (synC0c))
        (synWrex q (synCnnc) (.classEq (.cv p) (synCplc (.cv q) (synC1c)))))
      (synWa (.classMem (.cv m) (synCnnc)) (synWral n (synCnnc) (.neg
            (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c)))
          (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))))
      p0167 p0250
  have p0252 :=
    @gRalrimiv
      (synWa (.classMem (.cv m) (synCnnc)) (synWral n (synCnnc) (.neg
            (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
              (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))))
      (.neg (.classEq
          (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
            (synCplc (.cv m) (synC1c)))
          (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c))))
      p (synCnnc) dv_cache_0031 p0251
  have p0253 :=
    @gEx (.classMem (.cv m) (synCnnc))
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (synWral p (synCnnc) (.neg (.classEq
            (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
              (synCplc (.cv m) (synC1c)))
            (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c)))))
      p0252
  have p0254 :=
    @gFinds
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv a) (.cv a)) (.cv a))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (synWral n (synCnnc) (.neg (.classEq (synC0c)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc (.cv m) (.cv m)) (.cv m))
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (synWral p (synCnnc) (.neg (.classEq
            (synCplc (synCplc (synCplc (.cv m) (synC1c)) (synCplc (.cv m) (synC1c)))
              (synCplc (.cv m) (synC1c)))
            (synCplc (synCplc (synCplc (.cv p) (.cv p)) (.cv p)) (synC1c)))))
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc A A) A)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      a m A dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
      dv_cache_0037 dv_cache_0038 p0108 p0119 p0126 p0142 p0149 p0166 p0253
  have p0255 := @gAddceq12 (.cv n) (.cv n) B B
  have p0256 :=
    @gAnidms (.classEq (.cv n) B) (.classEq (synCplc (.cv n) (.cv n)) (synCplc B B))
      p0255
  have p0257 := @gId (.classEq (.cv n) B)
  have p0258 :=
    @gAddceq12d (.classEq (.cv n) B) (synCplc (.cv n) (.cv n)) (synCplc B B) (.cv n) B
      p0256 p0257
  have p0259 :=
    @gAddceq1d (.classEq (.cv n) B) (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
      (synCplc (synCplc B B) B) (synC1c) p0258
  have p0260 :=
    @gEqeq2d (.classEq (.cv n) B)
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
      (synCplc (synCplc (synCplc B B) B) (synC1c)) (synCplc (synCplc A A) A) p0259
  have p0261 :=
    @gNotbid (.classEq (.cv n) B)
      (.classEq (synCplc (synCplc A A) A)
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc A A) A) (synCplc (synCplc (synCplc B B) B) (synC1c)))
      p0260
  have p0262 :=
    @gRspccv
      (.neg (.classEq (synCplc (synCplc A A) A)
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.neg (.classEq (synCplc (synCplc A A) A)
          (synCplc (synCplc (synCplc B B) B) (synC1c))))
      n B (synCnnc) dv_cache_0039 dv_cache_0003 dv_cache_0040 p0261
  have p0263 :=
    @gSyl (.classMem A (synCnnc))
      (synWral n (synCnnc) (.neg (.classEq (synCplc (synCplc A A) A)
            (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      (.imp (.classMem B (synCnnc)) (.neg (.classEq (synCplc (synCplc A A) A)
            (synCplc (synCplc (synCplc B B) B) (synC1c)))))
      p0254 p0262
  have p0264 :=
    @gImp (.classMem A (synCnnc)) (.classMem B (synCnnc))
      (.neg (.classEq (synCplc (synCplc A A) A)
          (synCplc (synCplc (synCplc B B) B) (synC1c))))
      p0263
  exact p0264


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk013Compact001Part066`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_nnc3n3p2`. -/
@[expose]
noncomputable def gNnc3n3p2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc))) (.neg
          (.classEq (synCplc (synCplc A A) A)
            (synCplc (synCplc (synCplc B B) B) (synC2c))))) :=
  by
  have p0000 := @gPeano2 B
  have p0001 := @gNnc3n3p1 (synCplc B (synC1c)) A
  have p0002 :=
    @gSylan (.classMem B (synCnnc)) (.classMem (synCplc B (synC1c)) (synCnnc))
      (.classMem A (synCnnc))
      (.neg (.classEq (synCplc (synCplc (synCplc B (synC1c)) (synCplc B (synC1c)))
            (synCplc B (synC1c))) (synCplc (synCplc (synCplc A A) A) (synC1c))))
      p0000 p0001
  have p0003 :=
    @gAncoms (.classMem B (synCnnc)) (.classMem A (synCnnc))
      (.neg (.classEq (synCplc (synCplc (synCplc B (synC1c)) (synCplc B (synC1c)))
            (synCplc B (synC1c))) (synCplc (synCplc (synCplc A A) A) (synC1c))))
      p0002
  have p0004 :=
    @gEqcom (synCplc (synCplc (synCplc A A) A) (synC1c))
      (synCplc (synCplc (synCplc (synCplc B B) B) (synC2c)) (synC1c))
  have p0005 := @gAddc4 B (synC1c) B (synC1c)
  have p0006 :=
    @gAddceq1i (synCplc (synCplc B (synC1c)) (synCplc B (synC1c)))
      (synCplc (synCplc B B) (synCplc (synC1c) (synC1c))) B p0005
  have p0007 := @gAddc32 (synCplc B B) (synCplc (synC1c) (synC1c)) B
  have p0008 := @gN1p1e2c
  have p0009 :=
    @gAddceq2i (synCplc (synC1c) (synC1c)) (synC2c) (synCplc (synCplc B B) B) p0008
  have p0010 :=
    @gN3eqtrri (synCplc (synCplc (synCplc B (synC1c)) (synCplc B (synC1c))) B)
      (synCplc (synCplc (synCplc B B) (synCplc (synC1c) (synC1c))) B)
      (synCplc (synCplc (synCplc B B) B) (synCplc (synC1c) (synC1c)))
      (synCplc (synCplc (synCplc B B) B) (synC2c)) p0006 p0007 p0009
  have p0011 :=
    @gAddceq1i (synCplc (synCplc (synCplc B B) B) (synC2c))
      (synCplc (synCplc (synCplc B (synC1c)) (synCplc B (synC1c))) B) (synC1c)
      p0010
  have p0012 :=
    @gAddcass (synCplc (synCplc B (synC1c)) (synCplc B (synC1c))) B (synC1c)
  have p0013 :=
    @gEqtri (synCplc (synCplc (synCplc (synCplc B B) B) (synC2c)) (synC1c))
      (synCplc (synCplc (synCplc (synCplc B (synC1c)) (synCplc B (synC1c))) B) (synC1c))
      (synCplc (synCplc (synCplc B (synC1c)) (synCplc B (synC1c))) (synCplc B (synC1c)))
      p0011 p0012
  have p0014 :=
    @gEqeq1i (synCplc (synCplc (synCplc (synCplc B B) B) (synC2c)) (synC1c))
      (synCplc (synCplc (synCplc B (synC1c)) (synCplc B (synC1c))) (synCplc B (synC1c)))
      (synCplc (synCplc (synCplc A A) A) (synC1c)) p0013
  have p0015 :=
    @gBitri
      (.classEq (synCplc (synCplc (synCplc A A) A) (synC1c))
        (synCplc (synCplc (synCplc (synCplc B B) B) (synC2c)) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (synCplc B B) B) (synC2c)) (synC1c))
        (synCplc (synCplc (synCplc A A) A) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc B (synC1c)) (synCplc B (synC1c)))
          (synCplc B (synC1c))) (synCplc (synCplc (synCplc A A) A) (synC1c)))
      p0004 p0014
  have p0016 :=
    @gSylnibr (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classEq (synCplc (synCplc (synCplc B (synC1c)) (synCplc B (synC1c)))
          (synCplc B (synC1c))) (synCplc (synCplc (synCplc A A) A) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc A A) A) (synC1c))
        (synCplc (synCplc (synCplc (synCplc B B) B) (synC2c)) (synC1c)))
      p0003 p0015
  have p0017 := @gNncaddccl A A
  have p0018 :=
    @gAnidms (.classMem A (synCnnc)) (.classMem (synCplc A A) (synCnnc)) p0017
  have p0019 := @gNncaddccl (synCplc A A) A
  have p0020 :=
    @gMpancom (.classMem (synCplc A A) (synCnnc)) (.classMem A (synCnnc))
      (.classMem (synCplc (synCplc A A) A) (synCnnc)) p0018 p0019
  have p0021 := @gNncaddccl B B
  have p0022 :=
    @gAnidms (.classMem B (synCnnc)) (.classMem (synCplc B B) (synCnnc)) p0021
  have p0023 := @gNncaddccl (synCplc B B) B
  have p0024 :=
    @gMpancom (.classMem (synCplc B B) (synCnnc)) (.classMem B (synCnnc))
      (.classMem (synCplc (synCplc B B) B) (synCnnc)) p0022 p0023
  have p0025 := @gN2nnc
  have p0026 := @gNncaddccl (synCplc (synCplc B B) B) (synC2c)
  have p0027 :=
    @gSylancl (.classMem B (synCnnc)) (.classMem (synCplc (synCplc B B) B) (synCnnc))
      (.classMem (synC2c) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc B B) B) (synC2c)) (synCnnc)) p0024 p0025
      p0026
  have p0028 :=
    @gSuc11nnc (synCplc (synCplc A A) A)
      (synCplc (synCplc (synCplc B B) B) (synC2c))
  have p0029 :=
    @gSyl2an (.classMem A (synCnnc)) (.classMem (synCplc (synCplc A A) A) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc B B) B) (synC2c)) (synCnnc))
      (synWb (.classEq (synCplc (synCplc (synCplc A A) A) (synC1c))
          (synCplc (synCplc (synCplc (synCplc B B) B) (synC2c)) (synC1c)))
        (.classEq (synCplc (synCplc A A) A) (synCplc (synCplc (synCplc B B) B) (synC2c))))
      (.classMem B (synCnnc)) p0020 p0027 p0028
  have p0030 :=
    @gMtbid (synWa (.classMem A (synCnnc)) (.classMem B (synCnnc)))
      (.classEq (synCplc (synCplc (synCplc A A) A) (synC1c))
        (synCplc (synCplc (synCplc (synCplc B B) B) (synC2c)) (synC1c)))
      (.classEq (synCplc (synCplc A A) A) (synCplc (synCplc (synCplc B B) B) (synC2c)))
      p0016 p0029
  exact p0030

/-- Checked nominal proof certificate identified upstream as `g_nchoicelem1`. -/
@[expose]
noncomputable def gNchoicelem1 (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (synCnnc)) (.neg (.classEq A (synCplc (synCtc A) (synC1c))))) :=
  by
  let proofSupport : Finset Var := A.fv
  let n : Var := freshVar proofSupport 0
  have fresh_n : n ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_n_not_A : n ∉ A.fv := by
    intro h
    exact fresh_n (h)
  have dv_cache_0001 : n ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_n_not_A, not_false_eq_true])
  have dv_cache_0002 : n ∉ ((Wff.neg (.classEq A (synCplc (synCtc A) (synC1c))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          fresh_n_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gNncdiv3 A n dv_cache_0001
  have p0001 := @gId (.classMem (.cv n) (synCnnc))
  have p0002 := @gNntccl (.cv n)
  have p0003 := @gNnc3n3p1 (.cv n) (synCtc (.cv n))
  have p0004 :=
    @gSyl2anc (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (.classMem (synCtc (.cv n)) (synCnnc))
      (.neg (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCplc
            (synCplc (synCplc (synCtc (.cv n)) (synCtc (.cv n))) (synCtc (.cv n)))
            (synC1c))))
      p0001 p0002 p0003
  have p0005 := @gNncaddccl (.cv n) (.cv n)
  have p0006 :=
    @gAnidms (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) p0005
  have p0007 := @gNnnc (synCplc (.cv n) (.cv n))
  have p0008 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCncs)) p0006 p0007
  have p0009 := @gNnnc (.cv n)
  have p0010 := @gTcdi (synCplc (.cv n) (.cv n)) (.cv n)
  have p0011 :=
    @gSyl2anc (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCncs)) (.classMem (.cv n) (synCncs))
      (.classEq (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (synCplc (synCtc (synCplc (.cv n) (.cv n))) (synCtc (.cv n))))
      p0008 p0009 p0010
  have p0012 := @gTcdi (.cv n) (.cv n)
  have p0013 :=
    @gSyl2anc (.classMem (.cv n) (synCnnc)) (.classMem (.cv n) (synCncs))
      (.classMem (.cv n) (synCncs))
      (.classEq (synCtc (synCplc (.cv n) (.cv n)))
        (synCplc (synCtc (.cv n)) (synCtc (.cv n))))
      p0009 p0009 p0012
  have p0014 :=
    @gAddceq1d (.classMem (.cv n) (synCnnc)) (synCtc (synCplc (.cv n) (.cv n)))
      (synCplc (synCtc (.cv n)) (synCtc (.cv n))) (synCtc (.cv n)) p0013
  have p0015 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (synCplc (synCtc (synCplc (.cv n) (.cv n))) (synCtc (.cv n)))
      (synCplc (synCplc (synCtc (.cv n)) (synCtc (.cv n))) (synCtc (.cv n))) p0011
      p0014
  have p0016 :=
    @gAddceq1d (.classMem (.cv n) (synCnnc))
      (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (synCplc (synCplc (synCtc (.cv n)) (synCtc (.cv n))) (synCtc (.cv n)))
      (synC1c) p0015
  have p0017 :=
    @gEqeq2d (.classMem (.cv n) (synCnnc))
      (synCplc (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (synC1c))
      (synCplc (synCplc (synCplc (synCtc (.cv n)) (synCtc (.cv n))) (synCtc (.cv n)))
        (synC1c))
      (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) p0016
  have p0018 :=
    @gMtbird (.classMem (.cv n) (synCnnc))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
        (synCplc (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (synC1c)))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCplc
          (synCplc (synCplc (synCtc (.cv n)) (synCtc (.cv n))) (synCtc (.cv n)))
          (synC1c)))
      p0004 p0017
  have p0019 := @gId (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
  have p0020 := @gTceq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
  have p0021 :=
    @gAddceq1d (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (synCtc A)
      (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (synC1c) p0020
  have p0022 :=
    @gEqeq12d (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) A
      (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCplc (synCtc A) (synC1c))
      (synCplc (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (synC1c)) p0019
      p0021
  have p0023 :=
    @gNotbid (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.classEq A (synCplc (synCtc A) (synC1c)))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
        (synCplc (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (synC1c)))
      p0022
  have p0024 :=
    @gSyl5ibrcom (.classMem (.cv n) (synCnnc))
      (.neg (.classEq A (synCplc (synCtc A) (synC1c))))
      (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.neg (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
          (synCplc (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (synC1c))))
      p0018 p0023
  have p0025 := @gNncaddccl (synCplc (.cv n) (.cv n)) (.cv n)
  have p0026 :=
    @gSyl2anc (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (.cv n)) (synCnnc)) (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCnnc)) p0006 p0001
      p0025
  have p0027 := @gNnnc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
  have p0028 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCncs)) p0026 p0027
  have p0029 := @gN1cnc
  have p0030 := @gTcdi (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)
  have p0031 :=
    @gSylancl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCncs))
      (.classMem (synC1c) (synCncs))
      (.classEq (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (synCplc (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (synCtc (synC1c))))
      p0028 p0029 p0030
  have p0032 := @gTc1c
  have p0033 :=
    @gA1i (.classEq (synCtc (synC1c)) (synC1c)) (.classMem (.cv n) (synCnnc)) p0032
  have p0034 :=
    @gAddceq12d (.classMem (.cv n) (synCnnc))
      (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (synCplc (synCplc (synCtc (.cv n)) (synCtc (.cv n))) (synCtc (.cv n)))
      (synCtc (synC1c)) (synC1c) p0015 p0033
  have p0035 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (synCplc (synCtc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))) (synCtc (synC1c)))
      (synCplc (synCplc (synCplc (synCtc (.cv n)) (synCtc (.cv n))) (synCtc (.cv n)))
        (synC1c))
      p0031 p0034
  have p0036 :=
    @gEqeq2d (.classMem (.cv n) (synCnnc))
      (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (synCplc (synCplc (synCplc (synCtc (.cv n)) (synCtc (.cv n))) (synCtc (.cv n)))
        (synC1c))
      (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) p0035
  have p0037 :=
    @gMtbird (.classMem (.cv n) (synCnnc))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
        (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCplc
          (synCplc (synCplc (synCtc (.cv n)) (synCtc (.cv n))) (synCtc (.cv n)))
          (synC1c)))
      p0004 p0036
  have p0038 := @gPeano2 (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
  have p0039 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) (synCnnc))
      p0026 p0038
  have p0040 :=
    @gNntccl (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
  have p0041 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) (synCnnc))
      (.classMem (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (synCnnc))
      p0039 p0040
  have p0042 :=
    @gSuc11nnc (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
      (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
  have p0043 :=
    @gSyl2anc (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCnnc))
      (.classMem (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (synCnnc))
      (synWb (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
          (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
            (synC1c))) (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
          (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))))
      p0026 p0041 p0042
  have p0044 :=
    @gMtbird (.classMem (.cv n) (synCnnc))
      (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) (synCplc
          (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (synC1c)))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (.cv n))
        (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))))
      p0037 p0043
  have p0045 :=
    @gId (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
  have p0046 :=
    @gTceq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
  have p0047 :=
    @gAddceq1d
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (synCtc A)
      (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (synC1c) p0046
  have p0048 :=
    @gEqeq12d
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))) A
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
      (synCplc (synCtc A) (synC1c))
      (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (synC1c))
      p0045 p0047
  have p0049 :=
    @gNotbid
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq A (synCplc (synCtc A) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)) (synCplc
          (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (synC1c)))
      p0048
  have p0050 :=
    @gSyl5ibrcom (.classMem (.cv n) (synCnnc))
      (.neg (.classEq A (synCplc (synCtc A) (synC1c))))
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.neg (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c))
          (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
            (synC1c))))
      p0044 p0049
  have p0051 := @gPeano2 (.cv n)
  have p0052 := @gNntccl (synCplc (.cv n) (synC1c))
  have p0053 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCnnc))
      (.classMem (synCtc (synCplc (.cv n) (synC1c))) (synCnnc)) p0051 p0052
  have p0054 := @gNnc3n3p2 (synCtc (synCplc (.cv n) (synC1c))) (.cv n)
  have p0055 :=
    @gSyl2anc (.classMem (.cv n) (synCnnc))
      (.classMem (synCtc (synCplc (.cv n) (synC1c))) (synCnnc))
      (.classMem (.cv n) (synCnnc))
      (.neg (.classEq (synCplc (synCplc (synCtc (synCplc (.cv n) (synC1c)))
              (synCtc (synCplc (.cv n) (synC1c)))) (synCtc (synCplc (.cv n) (synC1c))))
          (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      p0053 p0001 p0054
  have p0056 := @gN2nnc
  have p0057 := @gNncaddccl (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)
  have p0058 :=
    @gSylancl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCnnc))
      (.classMem (synC2c) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synCnnc))
      p0026 p0056 p0057
  have p0059 := @gNnnc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
  have p0060 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synCncs))
      p0058 p0059
  have p0062 :=
    @gTcdi (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synC1c)
  have p0063 :=
    @gSylancl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synCncs))
      (.classMem (synC1c) (synCncs))
      (.classEq (synCtc
          (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
            (synC1c))) (synCplc
          (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
          (synCtc (synC1c))))
      p0060 p0029 p0062
  have p0064 :=
    @gEqcomd (.classMem (.cv n) (synCnnc))
      (synCtc (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
          (synC1c)))
      (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
        (synCtc (synC1c)))
      p0063
  have p0066 :=
    @gAddceq2i (synCtc (synC1c)) (synC1c)
      (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))) p0032
  have p0067 := @gAddccom (synCplc (synC1c) (synC1c)) (.cv n)
  have p0068 := @gN1p1e2c
  have p0069 := @gAddceq2i (synCplc (synC1c) (synC1c)) (synC2c) (.cv n) p0068
  have p0070 :=
    @gEqtr2i (synCplc (synCplc (synC1c) (synC1c)) (.cv n))
      (synCplc (.cv n) (synCplc (synC1c) (synC1c))) (synCplc (.cv n) (synC2c)) p0067
      p0069
  have p0071 :=
    @gAddceq1i (synCplc (.cv n) (synC2c))
      (synCplc (synCplc (synC1c) (synC1c)) (.cv n)) (synC1c) p0070
  have p0072 := @gAddcass (.cv n) (synC2c) (synC1c)
  have p0073 := @gAddcass (synCplc (synC1c) (synC1c)) (.cv n) (synC1c)
  have p0074 :=
    @gN3eqtr3i (synCplc (synCplc (.cv n) (synC2c)) (synC1c))
      (synCplc (synCplc (synCplc (synC1c) (synC1c)) (.cv n)) (synC1c))
      (synCplc (.cv n) (synCplc (synC2c) (synC1c)))
      (synCplc (synCplc (synC1c) (synC1c)) (synCplc (.cv n) (synC1c))) p0071 p0072
      p0073
  have p0075 :=
    @gAddceq2i (synCplc (.cv n) (synCplc (synC2c) (synC1c)))
      (synCplc (synCplc (synC1c) (synC1c)) (synCplc (.cv n) (synC1c)))
      (synCplc (.cv n) (.cv n)) p0074
  have p0076 :=
    @gAddcass (synCplc (.cv n) (.cv n)) (.cv n) (synCplc (synC2c) (synC1c))
  have p0077 :=
    @gAddcass (synCplc (.cv n) (.cv n)) (synCplc (synC1c) (synC1c))
      (synCplc (.cv n) (synC1c))
  have p0078 :=
    @gN3eqtr4i
      (synCplc (synCplc (.cv n) (.cv n)) (synCplc (.cv n) (synCplc (synC2c) (synC1c))))
      (synCplc (synCplc (.cv n) (.cv n))
        (synCplc (synCplc (synC1c) (synC1c)) (synCplc (.cv n) (synC1c))))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCplc (synC2c) (synC1c)))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synCplc (synC1c) (synC1c)))
        (synCplc (.cv n) (synC1c)))
      p0075 p0076 p0077
  have p0079 :=
    @gAddcass (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c) (synC1c)
  have p0080 := @gAddc4 (.cv n) (synC1c) (.cv n) (synC1c)
  have p0081 :=
    @gAddceq1i (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
      (synCplc (synCplc (.cv n) (.cv n)) (synCplc (synC1c) (synC1c)))
      (synCplc (.cv n) (synC1c)) p0080
  have p0082 :=
    @gN3eqtr4i
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synCplc (synC2c) (synC1c)))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (synCplc (synC1c) (synC1c)))
        (synCplc (.cv n) (synC1c)))
      (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
        (synCplc (.cv n) (synC1c)))
      p0078 p0079 p0081
  have p0083 :=
    @gTceq
      (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
        (synCplc (.cv n) (synC1c)))
  have p0084 := Nominal.mp p0082 p0083
  have p0085 :=
    @gN3eqtr3g (.classMem (.cv n) (synCnnc))
      (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
        (synCtc (synC1c)))
      (synCtc (synCplc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
          (synC1c)))
      (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
        (synC1c))
      (synCtc (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
          (synCplc (.cv n) (synC1c))))
      p0064 p0066 p0084
  have p0086 := @gNnnc (synCplc (.cv n) (synC1c))
  have p0087 :=
    @gSyl (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCncs)) p0051 p0086
  have p0088 := @gNcaddccl (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))
  have p0089 :=
    @gSyl2anc (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCncs))
      (.classMem (synCplc (.cv n) (synC1c)) (synCncs))
      (.classMem (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
        (synCncs))
      p0087 p0087 p0088
  have p0090 :=
    @gTcdi (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
      (synCplc (.cv n) (synC1c))
  have p0091 :=
    @gSyl2anc (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
        (synCncs))
      (.classMem (synCplc (.cv n) (synC1c)) (synCncs))
      (.classEq (synCtc
          (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
            (synCplc (.cv n) (synC1c)))) (synCplc
          (synCtc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))))
          (synCtc (synCplc (.cv n) (synC1c)))))
      p0089 p0087 p0090
  have p0092 := @gTcdi (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))
  have p0093 :=
    @gSyl2anc (.classMem (.cv n) (synCnnc))
      (.classMem (synCplc (.cv n) (synC1c)) (synCncs))
      (.classMem (synCplc (.cv n) (synC1c)) (synCncs))
      (.classEq (synCtc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))))
        (synCplc (synCtc (synCplc (.cv n) (synC1c)))
          (synCtc (synCplc (.cv n) (synC1c)))))
      p0087 p0087 p0092
  have p0094 :=
    @gAddceq1d (.classMem (.cv n) (synCnnc))
      (synCtc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))))
      (synCplc (synCtc (synCplc (.cv n) (synC1c))) (synCtc (synCplc (.cv n) (synC1c))))
      (synCtc (synCplc (.cv n) (synC1c))) p0093
  have p0095 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCtc (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
          (synCplc (.cv n) (synC1c))))
      (synCplc (synCtc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c))))
        (synCtc (synCplc (.cv n) (synC1c))))
      (synCplc (synCplc (synCtc (synCplc (.cv n) (synC1c)))
          (synCtc (synCplc (.cv n) (synC1c)))) (synCtc (synCplc (.cv n) (synC1c))))
      p0091 p0094
  have p0096 :=
    @gEqtrd (.classMem (.cv n) (synCnnc))
      (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
        (synC1c))
      (synCtc (synCplc (synCplc (synCplc (.cv n) (synC1c)) (synCplc (.cv n) (synC1c)))
          (synCplc (.cv n) (synC1c))))
      (synCplc (synCplc (synCtc (synCplc (.cv n) (synC1c)))
          (synCtc (synCplc (.cv n) (synC1c)))) (synCtc (synCplc (.cv n) (synC1c))))
      p0085 p0095
  have p0097 :=
    @gEqeq1d (.classMem (.cv n) (synCnnc))
      (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
        (synC1c))
      (synCplc (synCplc (synCtc (synCplc (.cv n) (synC1c)))
          (synCtc (synCplc (.cv n) (synC1c)))) (synCtc (synCplc (.cv n) (synC1c))))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) p0096
  have p0098 :=
    @gMtbird (.classMem (.cv n) (synCnnc))
      (.classEq (synCplc
          (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
          (synC1c)) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (.classEq (synCplc (synCplc (synCtc (synCplc (.cv n) (synC1c)))
            (synCtc (synCplc (.cv n) (synC1c)))) (synCtc (synCplc (.cv n) (synC1c))))
        (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      p0055 p0097
  have p0099 :=
    @gEqcom
      (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
        (synC1c))
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
  have p0100 :=
    @gSylnib (.classMem (.cv n) (synCnnc))
      (.classEq (synCplc
          (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
          (synC1c)) (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synCplc
          (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
          (synC1c)))
      p0098 p0099
  have p0101 :=
    @gId (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
  have p0102 :=
    @gTceq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
  have p0103 :=
    @gAddceq1d
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (synCtc A)
      (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (synC1c) p0102
  have p0104 :=
    @gEqeq12d
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))) A
      (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
      (synCplc (synCtc A) (synC1c))
      (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
        (synC1c))
      p0101 p0103
  have p0105 :=
    @gNotbid
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (.classEq A (synCplc (synCtc A) (synC1c)))
      (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)) (synCplc
          (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
          (synC1c)))
      p0104
  have p0106 :=
    @gSyl5ibrcom (.classMem (.cv n) (synCnnc))
      (.neg (.classEq A (synCplc (synCtc A) (synC1c))))
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      (.neg (.classEq (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))
          (synCplc (synCtc (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
            (synC1c))))
      p0100 p0105
  have p0107 :=
    @gN3jaod (.classMem (.cv n) (synCnnc))
      (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
      (.neg (.classEq A (synCplc (synCtc A) (synC1c))))
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
      (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))
      p0024 p0050 p0106
  have p0108 :=
    @gRexlimiv
      (synW3o (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
        (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
        (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c))))
      (.neg (.classEq A (synCplc (synCtc A) (synC1c)))) n (synCnnc) dv_cache_0002
      p0107
  have p0109 :=
    @gSyl (.classMem A (synCnnc))
      (synWrex n (synCnnc) (synW3o (.classEq A (synCplc (synCplc (.cv n) (.cv n)) (.cv n)))
          (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC1c)))
          (.classEq A (synCplc (synCplc (synCplc (.cv n) (.cv n)) (.cv n)) (synC2c)))))
      (.neg (.classEq A (synCplc (synCtc A) (synC1c)))) p0000 p0108
  exact p0109

/-- Checked nominal proof certificate identified upstream as `g_freceq12`. -/
@[expose]
noncomputable def gFreceq12 (F : Class) (G : Class) (I : Class) (J : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq F G) (.classEq I J))
        (.classEq (synCfrec F I) (synCfrec G J))) :=
  by
  let proofSupport : Finset Var := F.fv ∪ G.fv ∪ I.fv ∪ J.fv
  let x : Var := freshVar proofSupport 0
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_F : x ∉ F.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (h))))
  have fresh_x_not_G : x ∉ G.fv := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (h))))
  have fresh_x_not_I : x ∉ I.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_J : x ∉ J.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have dv_cache_0001 : x ∉ (F).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_F, not_false_eq_true])
  have dv_cache_0002 : x ∉ (I).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_I, not_false_eq_true])
  have dv_cache_0003 : x ∉ (G).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_G, not_false_eq_true])
  have dv_cache_0004 : x ∉ (J).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_J, not_false_eq_true])
  have p0000 := @gOpeq2 I J (synC0c)
  have p0001 := @gSneqd (.classEq I J) (synCop (synC0c) I) (synCop (synC0c) J) p0000
  have p0002 :=
    @gClos1eq1 (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F)
      (synCsn (synCop (synC0c) I)) (synCsn (synCop (synC0c) J))
  have p0003 :=
    @gSyl (.classEq I J)
      (.classEq (synCsn (synCop (synC0c) I)) (synCsn (synCop (synC0c) J)))
      (.classEq (synCclos1 (synCsn (synCop (synC0c) I))
          (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F))
        (synCclos1 (synCsn (synCop (synC0c) J))
          (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F)))
      p0001 p0002
  have p0004 := @gPprodeq2 F G (synCmpt x (synCvv) (synCplc (.cv x) (synC1c)))
  have p0005 :=
    @gClos1eq2 (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F)
      (synCsn (synCop (synC0c) J))
      (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)
  have p0006 :=
    @gSyl (.classEq F G)
      (.classEq (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F)
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      (.classEq (synCclos1 (synCsn (synCop (synC0c) J))
          (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F))
        (synCclos1 (synCsn (synCop (synC0c) J))
          (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G)))
      p0004 p0005
  have p0007 :=
    @gSylan9eqr (.classEq I J) (.classEq F G)
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F))
      (synCclos1 (synCsn (synCop (synC0c) J))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F))
      (synCclos1 (synCsn (synCop (synC0c) J))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      p0003 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFrec x F I
      dv_cache_0001 dv_cache_0002
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfFrec x G J
      dv_cache_0003 dv_cache_0004
  have p0010 :=
    @gN3eqtr4g (synWa (.classEq F G) (.classEq I J))
      (synCclos1 (synCsn (synCop (synC0c) I))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) F))
      (synCclos1 (synCsn (synCop (synC0c) J))
        (synCpprod (synCmpt x (synCvv) (synCplc (.cv x) (synC1c))) G))
      (synCfrec F I) (synCfrec G J) p0007 p0008 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end
