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

@[expose]
noncomputable def g_nnc3n3p1 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.neg
          (.classEq (syn_cplc (syn_cplc A A) A)
            (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c1c))))) :=
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
      ((syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                    (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
                (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                      (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn)))))))).fv :=
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
  have dv_cache_0003 : n ∉ ((syn_cnnc)).fv :=
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
  have dv_cache_0004 : p ∉ ((syn_cop (.cv n) (.cv a))).fv :=
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
      ((syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                    (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                  (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                    (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                  (syn_caddcfn))))))).fv :=
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
  have dv_cache_0006 : q ∉ ((syn_cop (.cv p) (.cv n))).fv :=
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
      ((syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
          (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                  (syn_caddcfn))))))).fv :=
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
  have dv_cache_0010 : x ∉ ((syn_caddcfn)).fv :=
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
      ((syn_ccnv (syn_cres (syn_c1st)
            (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))).fv :=
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
  have dv_cache_0012 : x ∉ ((syn_cop (.cv q) (syn_c1c))).fv :=
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
    x ∉ ((syn_wbr (syn_cop (.cv q) (syn_c1c)) (syn_caddcfn) (.cv p))).fv :=
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
  have dv_cache_0014 : q ∉ ((syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))).fv :=
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
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))).fv :=
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
  have dv_cache_0016 : p ∉ ((syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))).fv :=
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
      ((Wff.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))).fv :=
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
      ((syn_ccompl (syn_cima (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn)
                      (syn_ccnv (syn_cres (syn_c1st)
                          (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv
                      (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                    (syn_ctxp (syn_ccnv (syn_c1st))
                                      (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                                (syn_caddcfn)))) (syn_cima
                            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                            (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                          (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_cnnc)))).fv :=
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
  have dv_cache_0019 : n ∉ ((Wff.classEq (.cv a) (syn_c0c))).fv :=
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
  have dv_cache_0021 : n ∉ ((Wff.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))).fv :=
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
  have dv_cache_0022 : p ∉ ((syn_cnnc)).fv :=
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
            (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
              (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))).fv :=
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
            (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
              (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))))).fv :=
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
      ((Wff.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
            (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))))).fv :=
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
            (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
              (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))))).fv :=
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
      ((syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wral n (syn_cnnc) (.neg
              (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
                (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))))).fv :=
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
      ((syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wral n (syn_cnnc) (.neg
              (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
                (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))))).fv :=
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
      ((syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))).fv :=
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
      ((syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))).fv :=
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
      ((syn_wral n (syn_cnnc) (.neg (.classEq (syn_c0c)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))).fv :=
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
      ((syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc A A) A)
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))).fv :=
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
      ((syn_wral p (syn_cnnc) (.neg (.classEq (syn_cplc
                (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
                (syn_cplc (.cv m) (syn_c1c)))
              (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c)))))).fv :=
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
      ((Wff.neg (.classEq (syn_cplc (syn_cplc A A) A)
            (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c1c))))).fv :=
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
  have p0000 := @g_vex a
  have p0001 :=
    @g_elcompl (.cv a)
      (syn_cima (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                    (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
                (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                      (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))) (syn_cnnc))
      p0000
  have p0002 :=
    @g_elima n (.cv a)
      (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                  (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
              (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                    (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))))
      (syn_cnnc) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0003 :=
    (Nominal.biimpRefl (syn_wbr (.cv n) (syn_crn (syn_ctxp (syn_crn (syn_ctxp
                (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                      (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                    (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                      (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))) (.cv a)))
  have p0004 :=
    @g_elrn p (syn_cop (.cv n) (.cv a))
      (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                  (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      dv_cache_0004 dv_cache_0005
  have p0005 :=
    (Nominal.biimpRefl (syn_wbr (.cv p) (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn)
                (syn_ccnv (syn_cres (syn_c1st)
                    (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                  (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                    (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
        (syn_cop (.cv n) (.cv a))))
  have p0006 :=
    @g_oteltxp (.cv p) (.cv n) (.cv a)
      (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
          (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))))
      (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
  have p0007 :=
    @g_bitri
      (syn_wbr (.cv p) (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                  (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
              (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                    (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
        (syn_cop (.cv n) (.cv a)))
      (.classMem (syn_cop (.cv p) (syn_cop (.cv n) (.cv a))) (syn_ctxp (syn_crn (syn_ctxp
              (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                    (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                  (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                    (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))))
      (syn_wa (.classMem (syn_cop (.cv p) (.cv n)) (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn)
                (syn_ccnv (syn_cres (syn_c1st)
                    (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                  (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn)))))))) (.classMem (syn_cop (.cv p) (.cv a)) (syn_ccnv
            (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))))
      p0005 p0006
  have p0008 :=
    @g_elrn2 q (syn_cop (.cv p) (.cv n))
      (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
            (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
        (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      dv_cache_0006 dv_cache_0007
  have p0009 :=
    @g_oteltxp (.cv q) (.cv p) (.cv n)
      (syn_ccom (syn_caddcfn) (syn_ccnv
          (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
      (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
  have p0010 :=
    @g_opelco x (.cv q) (.cv p) (syn_caddcfn)
      (syn_ccnv (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))
      dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0011 :=
    @g_brcnv (.cv q) (.cv x)
      (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))
  have p0012 :=
    @g_brres (.cv x) (.cv q) (syn_c1st)
      (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))
  have p0013 :=
    @g_bitri
      (syn_wbr (.cv q) (syn_ccnv
          (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))) (.cv x))
      (syn_wbr (.cv x)
        (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))) (.cv q))
      (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv q))
        (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))
      p0011 p0012
  have p0014 := @g_eliniseg (syn_c2nd) (syn_c1c) (.cv x)
  have p0015 :=
    @g_anbi2i (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))
      (syn_wbr (.cv x) (syn_c2nd) (syn_c1c)) (syn_wbr (.cv x) (syn_c1st) (.cv q)) p0014
  have p0016 := @g_vex q
  have p0017 := @g_n_1cex
  have p0018 := @g_op1st2nd (.cv q) (syn_c1c) (.cv x) p0016 p0017
  have p0019 :=
    @g_n_3bitri
      (syn_wbr (.cv q) (syn_ccnv
          (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))) (.cv x))
      (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv q))
        (.classMem (.cv x) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))
      (syn_wa (syn_wbr (.cv x) (syn_c1st) (.cv q)) (syn_wbr (.cv x) (syn_c2nd) (syn_c1c)))
      (.classEq (.cv x) (syn_cop (.cv q) (syn_c1c))) p0013 p0015 p0018
  have p0020 :=
    @g_anbi1i
      (syn_wbr (.cv q) (syn_ccnv
          (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))) (.cv x))
      (.classEq (.cv x) (syn_cop (.cv q) (syn_c1c)))
      (syn_wbr (.cv x) (syn_caddcfn) (.cv p)) p0019
  have p0021 :=
    @g_exbii
      (syn_wa (syn_wbr (.cv q) (syn_ccnv
            (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))) (.cv x))
        (syn_wbr (.cv x) (syn_caddcfn) (.cv p)))
      (syn_wa (.classEq (.cv x) (syn_cop (.cv q) (syn_c1c)))
        (syn_wbr (.cv x) (syn_caddcfn) (.cv p)))
      x p0020
  have p0023 := @g_opex (.cv q) (syn_c1c) p0016 p0017
  have p0024 := @g_breq1 (.cv x) (syn_cop (.cv q) (syn_c1c)) (.cv p) (syn_caddcfn)
  have p0025 :=
    @g_ceqsexv (syn_wbr (.cv x) (syn_caddcfn) (.cv p))
      (syn_wbr (syn_cop (.cv q) (syn_c1c)) (syn_caddcfn) (.cv p)) x
      (syn_cop (.cv q) (syn_c1c)) dv_cache_0012 dv_cache_0013 p0023 p0024
  have p0026 :=
    @g_bitri
      (syn_wex x (syn_wa (syn_wbr (.cv q) (syn_ccnv
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))
            (.cv x)) (syn_wbr (.cv x) (syn_caddcfn) (.cv p))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cop (.cv q) (syn_c1c)))
          (syn_wbr (.cv x) (syn_caddcfn) (.cv p))))
      (syn_wbr (syn_cop (.cv q) (syn_c1c)) (syn_caddcfn) (.cv p)) p0021 p0025
  have p0028 := @g_braddcfn (.cv q) (syn_c1c) (.cv p) p0016 p0017
  have p0029 := @g_eqcom (syn_cplc (.cv q) (syn_c1c)) (.cv p)
  have p0030 :=
    @g_bitri (syn_wbr (syn_cop (.cv q) (syn_c1c)) (syn_caddcfn) (.cv p))
      (.classEq (syn_cplc (.cv q) (syn_c1c)) (.cv p))
      (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c))) p0028 p0029
  have p0031 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv q) (.cv p)) (syn_ccom (syn_caddcfn) (syn_ccnv
            (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))))
      (syn_wex x (syn_wa (syn_wbr (.cv q) (syn_ccnv
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))
            (.cv x)) (syn_wbr (.cv x) (syn_caddcfn) (.cv p))))
      (syn_wbr (syn_cop (.cv q) (syn_c1c)) (syn_caddcfn) (.cv p))
      (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c))) p0010 p0026 p0030
  have p0032 :=
    @g_opelcnv (.cv q) (.cv n)
      (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
  have p0033 := @g_nncdiv3lem1 n q
  have p0034 :=
    @g_bitri
      (.classMem (syn_cop (.cv q) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      (.classMem (syn_cop (.cv n) (.cv q)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                  (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      (.classEq (.cv q) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) p0032 p0033
  have p0035 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv q) (.cv p)) (syn_ccom (syn_caddcfn) (syn_ccnv
            (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))))
      (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
      (.classMem (syn_cop (.cv q) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      (.classEq (.cv q) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) p0031 p0034
  have p0036 :=
    @g_ancom (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
      (.classEq (.cv q) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
  have p0037 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv q) (syn_cop (.cv p) (.cv n))) (syn_ctxp (syn_ccom (syn_caddcfn)
            (syn_ccnv
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
          (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))))
      (syn_wa (.classMem (syn_cop (.cv q) (.cv p)) (syn_ccom (syn_caddcfn) (syn_ccnv
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))))
        (.classMem (syn_cop (.cv q) (.cv n)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                    (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))))
      (syn_wa (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
        (.classEq (.cv q) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))))
      (syn_wa (.classEq (.cv q) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c))))
      p0009 p0035 p0036
  have p0038 :=
    @g_exbii
      (.classMem (syn_cop (.cv q) (syn_cop (.cv p) (.cv n))) (syn_ctxp (syn_ccom (syn_caddcfn)
            (syn_ccnv
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
          (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))))
      (syn_wa (.classEq (.cv q) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c))))
      q p0037
  have p0039 := @g_vex n
  have p0040 := @g_addcex (.cv n) (.cv n) p0039 p0039
  have p0041 := @g_addcex (syn_cplc (.cv n) (.cv n)) (.cv n) p0040 p0039
  have p0042 := @g_addceq1 (.cv q) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)
  have p0043 :=
    @g_eqeq2d (.classEq (.cv q) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (syn_cplc (.cv q) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (.cv p) p0042
  have p0044 :=
    @g_ceqsexv (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
      (.classEq (.cv p) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      q (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) dv_cache_0014 dv_cache_0015 p0041
      p0043
  have p0045 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv p) (.cv n)) (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
            (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))))
      (syn_wex q (.classMem (syn_cop (.cv q) (syn_cop (.cv p) (.cv n))) (syn_ctxp
            (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                  (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))))
      (syn_wex q (syn_wa (.classEq (.cv q) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))))
      (.classEq (.cv p) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      p0008 p0038 p0044
  have p0046 :=
    @g_opelcnv (.cv p) (.cv a)
      (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
  have p0047 := @g_nncdiv3lem1 a p
  have p0048 :=
    @g_bitri
      (.classMem (syn_cop (.cv p) (.cv a)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      (.classMem (syn_cop (.cv a) (.cv p)) (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima
                  (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      (.classEq (.cv p) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))) p0046 p0047
  have p0049 :=
    @g_anbi12i
      (.classMem (syn_cop (.cv p) (.cv n)) (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
            (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))))
      (.classEq (.cv p) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classMem (syn_cop (.cv p) (.cv a)) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      (.classEq (.cv p) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))) p0045 p0048
  have p0050 :=
    @g_ancom
      (.classEq (.cv p) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (.cv p) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))
  have p0051 :=
    @g_n_3bitri
      (syn_wbr (.cv p) (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                  (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
              (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                    (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
        (syn_cop (.cv n) (.cv a)))
      (syn_wa (.classMem (syn_cop (.cv p) (.cv n)) (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn)
                (syn_ccnv (syn_cres (syn_c1st)
                    (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                  (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn)))))))) (.classMem (syn_cop (.cv p) (.cv a)) (syn_ccnv
            (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))))
      (syn_wa (.classEq (.cv p)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq (.cv p) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))))
      (syn_wa (.classEq (.cv p) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))) (.classEq (.cv p)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      p0007 p0049 p0050
  have p0052 :=
    @g_exbii
      (syn_wbr (.cv p) (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                  (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
              (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                    (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
        (syn_cop (.cv n) (.cv a)))
      (syn_wa (.classEq (.cv p) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))) (.classEq (.cv p)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      p p0051
  have p0053 := @g_addcex (.cv a) (.cv a) p0000 p0000
  have p0054 := @g_addcex (syn_cplc (.cv a) (.cv a)) (.cv a) p0053 p0000
  have p0055 :=
    @g_eqeq1 (.cv p) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0056 :=
    @g_ceqsexv
      (.classEq (.cv p) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      p (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)) dv_cache_0016 dv_cache_0017 p0054
      p0055
  have p0057 :=
    @g_n_3bitri
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_crn (syn_ctxp
                (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                      (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                    (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                      (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))))
      (syn_wex p (syn_wbr (.cv p) (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                    (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
                (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                      (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
          (syn_cop (.cv n) (.cv a))))
      (syn_wex p (syn_wa (.classEq (.cv p) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a)))
          (.classEq (.cv p)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      p0004 p0052 p0056
  have p0058 :=
    @g_bitri
      (syn_wbr (.cv n) (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                    (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
                (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                      (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))) (.cv a))
      (.classMem (syn_cop (.cv n) (.cv a)) (syn_crn (syn_ctxp (syn_crn (syn_ctxp
                (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                      (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                    (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                      (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))))
      (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      p0003 p0057
  have p0059 :=
    @g_rexbii
      (syn_wbr (.cv n) (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                    (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
                (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                      (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))) (.cv a))
      (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      n (syn_cnnc) p0058
  have p0060 :=
    @g_dfrex2
      (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      n (syn_cnnc)
  have p0061 :=
    @g_n_3bitrri
      (.classMem (.cv a) (syn_cima (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn)
                    (syn_ccnv (syn_cres (syn_c1st)
                        (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv
                    (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                  (syn_ctxp (syn_ccnv (syn_c1st))
                                    (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                              (syn_caddcfn)))) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                        (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_cnnc)))
      (syn_wrex n (syn_cnnc) (syn_wbr (.cv n) (syn_crn (syn_ctxp (syn_crn (syn_ctxp
                  (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                        (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv
                    (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                  (syn_ctxp (syn_ccnv (syn_c1st))
                                    (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                              (syn_caddcfn)))) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                        (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (.cv a)))
      (syn_wrex n (syn_cnnc) (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.neg (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))))
      p0002 p0059 p0060
  have p0062 :=
    @g_con1bii
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (.classMem (.cv a) (syn_cima (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn)
                    (syn_ccnv (syn_cres (syn_c1st)
                        (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv
                    (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                  (syn_ctxp (syn_ccnv (syn_c1st))
                                    (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                              (syn_caddcfn)))) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                        (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_cnnc)))
      p0061
  have p0063 :=
    @g_bitri
      (.classMem (.cv a) (syn_ccompl (syn_cima (syn_crn (syn_ctxp (syn_crn (syn_ctxp
                    (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                          (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv
                      (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                    (syn_ctxp (syn_ccnv (syn_c1st))
                                      (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                                (syn_caddcfn)))) (syn_cima
                            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                            (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                          (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_cnnc))))
      (.neg (.classMem (.cv a) (syn_cima (syn_crn (syn_ctxp (syn_crn (syn_ctxp
                    (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                          (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv
                      (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                    (syn_ctxp (syn_ccnv (syn_c1st))
                                      (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                                (syn_caddcfn)))) (syn_cima
                            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                            (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                          (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_cnnc))))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      p0001 p0062
  have p0064 :=
    @g_eqabi
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      a
      (syn_ccompl (syn_cima (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn)
                    (syn_ccnv (syn_cres (syn_c1st)
                        (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv
                    (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                  (syn_ctxp (syn_ccnv (syn_c1st))
                                    (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                              (syn_caddcfn)))) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                        (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_cnnc)))
      dv_cache_0018 p0063
  have p0065 := @g_addcfnex
  have p0066 := @g_n_1stex
  have p0067 := @g_n_2ndex
  have p0068 := @g_cnvex (syn_c2nd) p0067
  have p0069 := @g_snex (syn_c1c)
  have p0070 := @g_imaex (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)) p0068 p0069
  have p0071 :=
    @g_resex (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))) p0066 p0070
  have p0072 :=
    @g_cnvex (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))
      p0071
  have p0073 :=
    @g_coex (syn_caddcfn)
      (syn_ccnv (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))
      p0065 p0072
  have p0075 := @g_cnvex (syn_c1st) p0066
  have p0078 := @g_inex (syn_c1st) (syn_c2nd) p0066 p0067
  have p0079 := @g_txpex (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)) p0075 p0078
  have p0080 :=
    @g_rnex (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))) p0079
  have p0082 :=
    @g_txpex (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
      (syn_c2nd) p0080 p0067
  have p0084 :=
    @g_imaex
      (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
        (syn_c2nd))
      (syn_caddcfn) p0082 p0065
  have p0085 :=
    @g_cnvex
      (syn_cima (syn_ctxp
          (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
        (syn_caddcfn))
      p0084
  have p0086 :=
    @g_ins3ex
      (syn_ccnv (syn_cima (syn_ctxp
            (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
            (syn_c2nd)) (syn_caddcfn)))
      p0085
  have p0089 := @g_coex (syn_c1st) (syn_c1st) p0066 p0066
  have p0092 := @g_coex (syn_c2nd) (syn_c1st) p0067 p0066
  have p0094 := @g_txpex (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd) p0092 p0067
  have p0095 :=
    @g_txpex (syn_ccom (syn_c1st) (syn_c1st))
      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)) p0089 p0094
  have p0097 :=
    @g_imaex
      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
      (syn_caddcfn) p0095 p0065
  have p0098 :=
    @g_inex
      (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
              (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
              (syn_c2nd)) (syn_caddcfn))))
      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))
      p0086 p0097
  have p0099 :=
    @g_rnex
      (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp
                (syn_crn (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                (syn_c2nd)) (syn_caddcfn)))) (syn_cima
          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))
      p0098
  have p0100 :=
    @g_cnvex
      (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                    (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                  (syn_c2nd)) (syn_caddcfn)))) (syn_cima
            (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
              (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))
      p0099
  have p0101 :=
    @g_txpex
      (syn_ccom (syn_caddcfn) (syn_ccnv
          (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
      (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      p0073 p0100
  have p0102 :=
    @g_rnex
      (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
            (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
        (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      p0101
  have p0103 :=
    @g_txpex
      (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
              (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
          (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                          (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                        (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                  (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))))
      (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                      (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                    (syn_c2nd)) (syn_caddcfn)))) (syn_cima
              (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))
      p0102 p0100
  have p0104 :=
    @g_rnex
      (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv (syn_cres (syn_c1st)
                  (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv (syn_crn
                (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                            (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                          (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                    (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                  (syn_cima (syn_ctxp (syn_crn
                        (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                      (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                  (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn))))))
      p0103
  have p0105 := @g_nncex
  have p0106 :=
    @g_imaex
      (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                  (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
              (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                              (syn_ctxp (syn_ccnv (syn_c1st)) (syn_cin (syn_c1st) (syn_c2nd))))
                            (syn_c2nd)) (syn_caddcfn)))) (syn_cima
                      (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                    (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                            (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                    (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd))) (syn_caddcfn)))))))
      (syn_cnnc) p0104 p0105
  have p0107 :=
    @g_complex
      (syn_cima (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn) (syn_ccnv
                    (syn_cres (syn_c1st) (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c))))))
                (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                (syn_ctxp (syn_ccnv (syn_c1st))
                                  (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                      (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                          (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                        (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                      (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                              (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                  (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                      (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                    (syn_caddcfn))))))) (syn_cnnc))
      p0106
  have p0108 :=
    @g_eqeltrri
      (syn_ccompl (syn_cima (syn_crn (syn_ctxp (syn_crn (syn_ctxp (syn_ccom (syn_caddcfn)
                    (syn_ccnv (syn_cres (syn_c1st)
                        (syn_cima (syn_ccnv (syn_c2nd)) (syn_csn (syn_c1c)))))) (syn_ccnv
                    (syn_crn (syn_cin (syn_cins3 (syn_ccnv (syn_cima (syn_ctxp (syn_crn
                                  (syn_ctxp (syn_ccnv (syn_c1st))
                                    (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd))
                              (syn_caddcfn)))) (syn_cima
                          (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                            (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                          (syn_caddcfn))))))) (syn_ccnv (syn_crn (syn_cin (syn_cins3 (syn_ccnv
                        (syn_cima (syn_ctxp (syn_crn (syn_ctxp (syn_ccnv (syn_c1st))
                                (syn_cin (syn_c1st) (syn_c2nd)))) (syn_c2nd)) (syn_caddcfn))))
                    (syn_cima (syn_ctxp (syn_ccom (syn_c1st) (syn_c1st))
                        (syn_ctxp (syn_ccom (syn_c2nd) (syn_c1st)) (syn_c2nd)))
                      (syn_caddcfn))))))) (syn_cnnc)))
      (.cab a (syn_wral n (syn_cnnc) (.neg
            (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))))
      (syn_cvv) p0064 p0107
  have p0109 := @g_addceq12 (.cv a) (.cv a) (syn_c0c) (syn_c0c)
  have p0110 :=
    @g_anidms (.classEq (.cv a) (syn_c0c))
      (.classEq (syn_cplc (.cv a) (.cv a)) (syn_cplc (syn_c0c) (syn_c0c))) p0109
  have p0111 := @g_id (.classEq (.cv a) (syn_c0c))
  have p0112 :=
    @g_addceq12d (.classEq (.cv a) (syn_c0c)) (syn_cplc (.cv a) (.cv a))
      (syn_cplc (syn_c0c) (syn_c0c)) (.cv a) (syn_c0c) p0110 p0111
  have p0113 := @g_addcid1 (syn_cplc (syn_c0c) (syn_c0c))
  have p0114 := @g_addcid2 (syn_c0c)
  have p0115 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c))
      (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c) p0113 p0114
  have p0116 :=
    @g_syl6eq (.classEq (.cv a) (syn_c0c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
      (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c0c) p0112 p0115
  have p0117 :=
    @g_eqeq1d (.classEq (.cv a) (syn_c0c)) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
      (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) p0116
  have p0118 :=
    @g_notbid (.classEq (.cv a) (syn_c0c))
      (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      p0117
  have p0119 :=
    @g_ralbidv (.classEq (.cv a) (syn_c0c))
      (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.neg (.classEq (syn_c0c)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      n (syn_cnnc) dv_cache_0019 p0118
  have p0120 := @g_addceq12 (.cv a) (.cv a) (.cv m) (.cv m)
  have p0121_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq a m) (.objEq a m))
        (.classEq (syn_cplc (.cv a) (.cv a)) (syn_cplc (.cv m) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cplc syn_wrex syn_wex
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
    @g_anidms (.objEq a m)
      (.classEq (syn_cplc (.cv a) (.cv a)) (syn_cplc (.cv m) (.cv m))) p0121_e00_recanon
  have p0122 := @g_id (.objEq a m)
  have p0123_e01_recanon : Nominal.NPrf (.imp (.objEq a m) (.classEq (.cv a) (.cv m))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0122
  have p0123 :=
    @g_addceq12d (.objEq a m) (syn_cplc (.cv a) (.cv a)) (syn_cplc (.cv m) (.cv m))
      (.cv a) (.cv m) p0121 p0123_e01_recanon
  have p0124 :=
    @g_eqeq1d (.objEq a m) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
      (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) p0123
  have p0125 :=
    @g_notbid (.objEq a m)
      (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      p0124
  have p0126 :=
    @g_ralbidv (.objEq a m)
      (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      n (syn_cnnc) dv_cache_0020 p0125
  have p0127 :=
    @g_addceq12 (.cv a) (.cv a) (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))
  have p0128 :=
    @g_anidms (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))
      (.classEq (syn_cplc (.cv a) (.cv a))
        (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))))
      p0127
  have p0129 := @g_id (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))
  have p0130 :=
    @g_addceq12d (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))
      (syn_cplc (.cv a) (.cv a))
      (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))) (.cv a)
      (syn_cplc (.cv m) (syn_c1c)) p0128 p0129
  have p0131 :=
    @g_eqeq1d (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))
      (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
      (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (.cv m) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) p0130
  have p0132 :=
    @g_notbid (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      p0131
  have p0133 :=
    @g_ralbidv (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))
      (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      n (syn_cnnc) dv_cache_0021 p0132
  have p0134 := @g_addceq12 (.cv n) (.cv n) (.cv p) (.cv p)
  have p0135_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq n p) (.objEq n p))
        (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv p) (.cv p)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cplc syn_wrex syn_wex
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
    @g_anidms (.objEq n p)
      (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv p) (.cv p))) p0135_e00_recanon
  have p0136 := @g_id (.objEq n p)
  have p0137_e01_recanon : Nominal.NPrf (.imp (.objEq n p) (.classEq (.cv n) (.cv p))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0136
  have p0137 :=
    @g_addceq12d (.objEq n p) (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv p) (.cv p))
      (.cv n) (.cv p) p0135 p0137_e01_recanon
  have p0138 :=
    @g_addceq1d (.objEq n p) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
      (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c) p0137
  have p0139 :=
    @g_eqeq2d (.objEq n p)
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (.cv m) (syn_c1c)))
      p0138
  have p0140 :=
    @g_notbid (.objEq n p)
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c)))
      p0139
  have p0141 :=
    @g_cbvralv
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))))
      n p (syn_cnnc) dv_cache_0003 dv_cache_0022 dv_cache_0023 dv_cache_0024 p0140
  have p0142 :=
    @g_syl6bb (.classEq (.cv a) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (syn_wral n (syn_cnnc) (.neg (.classEq
            (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
              (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (syn_wral p (syn_cnnc) (.neg (.classEq
            (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
              (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c)))))
      p0133 p0141
  have p0143 := @g_addceq12 (.cv a) (.cv a) A A
  have p0144 :=
    @g_anidms (.classEq (.cv a) A) (.classEq (syn_cplc (.cv a) (.cv a)) (syn_cplc A A))
      p0143
  have p0145 := @g_id (.classEq (.cv a) A)
  have p0146 :=
    @g_addceq12d (.classEq (.cv a) A) (syn_cplc (.cv a) (.cv a)) (syn_cplc A A) (.cv a) A
      p0144 p0145
  have p0147 :=
    @g_eqeq1d (.classEq (.cv a) A) (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
      (syn_cplc (syn_cplc A A) A)
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) p0146
  have p0148 :=
    @g_notbid (.classEq (.cv a) A)
      (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc A A) A)
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      p0147
  have p0149 :=
    @g_ralbidv (.classEq (.cv a) A)
      (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.neg (.classEq (syn_cplc (syn_cplc A A) A)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      n (syn_cnnc) dv_cache_0025 p0148
  have p0150 := @g_n_1ne0c
  have p0151 := (Nominal.biimpRefl (syn_wne (syn_c1c) (syn_c0c)))
  have p0152 :=
    @g_mpbi (syn_wne (syn_c1c) (syn_c0c)) (.neg (.classEq (syn_c1c) (syn_c0c))) p0150
      p0151
  have p0153 :=
    @g_intnan (.classEq (syn_c1c) (syn_c0c))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c0c)) p0152
  have p0154 :=
    @g_eqcom (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0155 := @g_nncaddccl (.cv n) (.cv n)
  have p0156 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0155
  have p0157 := @g_nncaddccl (syn_cplc (.cv n) (.cv n)) (.cv n)
  have p0158 :=
    @g_mpancom (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc))
      (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc)) p0156 p0157
  have p0159 := @g_nnnc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0160 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cncs)) p0158 p0159
  have p0161 := @g_n_1cnc
  have p0162 := @g_addceq0 (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)
  have p0163 :=
    @g_sylancl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cncs))
      (.classMem (syn_c1c) (syn_cncs))
      (syn_wb (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
          (syn_c0c)) (syn_wa (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c0c))
          (.classEq (syn_c1c) (syn_c0c))))
      p0160 p0161 p0162
  have p0164 :=
    @g_syl5bb
      (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_c0c))
      (.classMem (.cv n) (syn_cnnc))
      (syn_wa (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c0c))
        (.classEq (syn_c1c) (syn_c0c)))
      p0154 p0163
  have p0165 :=
    @g_mtbiri (.classMem (.cv n) (syn_cnnc))
      (.classEq (syn_c0c) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (syn_wa (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c0c))
        (.classEq (syn_c1c) (syn_c0c)))
      p0153 p0164
  have p0166 :=
    @g_rgen
      (.neg (.classEq (syn_c0c)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      n (syn_cnnc) p0165
  have p0167 := @g_nnc0suc q (.cv p) dv_cache_0026
  have p0168 :=
    @g_n_0cnsuc (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (.cv m))
  have p0169 :=
    (Nominal.biimpRefl (syn_wne
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (.cv m)) (syn_c1c))
        (syn_c0c)))
  have p0170 :=
    @g_mpbi
      (syn_wne (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (.cv m))
          (syn_c1c)) (syn_c0c))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (.cv m))
            (syn_c1c)) (syn_c0c)))
      p0168 p0169
  have p0171 :=
    @g_a1i
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (.cv m))
            (syn_c1c)) (syn_c0c)))
      (.classMem (.cv m) (syn_cnnc)) p0170
  have p0172 := @g_addcass (syn_cplc (.cv m) (syn_c1c)) (.cv m) (syn_c1c)
  have p0173 :=
    @g_addceq1i (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (syn_c1c))
      (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))) (.cv m) p0172
  have p0174 :=
    @g_addc32 (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (syn_c1c) (.cv m)
  have p0175 :=
    @g_eqtr3i
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (syn_c1c)) (.cv m))
      (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))) (.cv m))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (.cv m)) (syn_c1c))
      p0173 p0174
  have p0176 :=
    @g_eqeq1i
      (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))) (.cv m))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (.cv m)) (syn_c1c))
      (syn_c0c) p0175
  have p0177 :=
    @g_sylnibr (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (.cv m)) (.cv m))
          (syn_c1c)) (syn_c0c))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (.cv m)) (syn_c0c))
      p0171 p0176
  have p0178 := @g_peano2 (.cv m)
  have p0179 := @g_nncaddccl (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))
  have p0180 :=
    @g_anidms (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cnnc))
      p0179
  have p0181 :=
    @g_syl (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (.cv m) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cnnc))
      p0178 p0180
  have p0182 :=
    @g_nncaddccl (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
      (.cv m)
  have p0183 :=
    @g_mpancom
      (.classMem (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cnnc))
      (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (.cv m)) (syn_cnnc))
      p0181 p0182
  have p0184 := @g_peano1
  have p0185 :=
    @g_suc11nnc
      (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c))) (.cv m))
      (syn_c0c)
  have p0186 :=
    @g_sylancl (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (.cv m)) (syn_cnnc))
      (.classMem (syn_c0c) (syn_cnnc))
      (syn_wb (.classEq (syn_cplc
            (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
              (.cv m)) (syn_c1c)) (syn_cplc (syn_c0c) (syn_c1c))) (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (.cv m)) (syn_c0c)))
      p0183 p0184 p0185
  have p0187 :=
    @g_mtbird (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_cplc
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (.cv m)) (syn_c1c)) (syn_cplc (syn_c0c) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (.cv m)) (syn_c0c))
      p0177 p0186
  have p0188 :=
    @g_addcass (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
      (.cv m) (syn_c1c)
  have p0189 :=
    @g_eqeq1i
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (.cv m)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (.cv m) (syn_c1c)))
      (syn_cplc (syn_c0c) (syn_c1c)) p0188
  have p0190 :=
    @g_sylnib (.classMem (.cv m) (syn_cnnc))
      (.classEq (syn_cplc
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (.cv m)) (syn_c1c)) (syn_cplc (syn_c0c) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_c0c) (syn_c1c)))
      p0187 p0189
  have p0191 := @g_addceq12 (.cv p) (.cv p) (syn_c0c) (syn_c0c)
  have p0192 :=
    @g_anidms (.classEq (.cv p) (syn_c0c))
      (.classEq (syn_cplc (.cv p) (.cv p)) (syn_cplc (syn_c0c) (syn_c0c))) p0191
  have p0193 := @g_id (.classEq (.cv p) (syn_c0c))
  have p0194 :=
    @g_addceq12d (.classEq (.cv p) (syn_c0c)) (syn_cplc (.cv p) (.cv p))
      (syn_cplc (syn_c0c) (syn_c0c)) (.cv p) (syn_c0c) p0192 p0193
  have p0195 :=
    @g_syl6eq (.classEq (.cv p) (syn_c0c)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p))
      (syn_cplc (syn_cplc (syn_c0c) (syn_c0c)) (syn_c0c)) (syn_c0c) p0194 p0115
  have p0196 :=
    @g_addceq1d (.classEq (.cv p) (syn_c0c)) (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p))
      (syn_c0c) (syn_c1c) p0195
  have p0197 :=
    @g_eqeq2d (.classEq (.cv p) (syn_c0c))
      (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))
      (syn_cplc (syn_c0c) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (.cv m) (syn_c1c)))
      p0196
  have p0198 :=
    @g_notbid (.classEq (.cv p) (syn_c0c))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_c0c) (syn_c1c)))
      p0197
  have p0199 :=
    @g_syl5ibrcom (.classMem (.cv m) (syn_cnnc))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))))
      (.classEq (.cv p) (syn_c0c))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c))) (syn_cplc (syn_c0c) (syn_c1c))))
      p0190 p0198
  have p0200 :=
    @g_adantr (.classMem (.cv m) (syn_cnnc))
      (.imp (.classEq (.cv p) (syn_c0c)) (.neg (.classEq
            (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
              (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c)))))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      p0199
  have p0201 := @g_addceq12 (.cv n) (.cv n) (.cv q) (.cv q)
  have p0202_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objEq n q) (.objEq n q))
        (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv q) (.cv q)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cplc syn_wrex syn_wex
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
    @g_anidms (.objEq n q)
      (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv q) (.cv q))) p0202_e00_recanon
  have p0203 := @g_id (.objEq n q)
  have p0204_e01_recanon : Nominal.NPrf (.imp (.objEq n q) (.classEq (.cv n) (.cv q))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0203
  have p0204 :=
    @g_addceq12d (.objEq n q) (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv q) (.cv q))
      (.cv n) (.cv q) p0202 p0204_e01_recanon
  have p0205 :=
    @g_addceq1d (.objEq n q) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
      (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c) p0204
  have p0206 :=
    @g_eqeq2d (.objEq n q)
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))
      (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m)) p0205
  have p0207 :=
    @g_notbid (.objEq n q)
      (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
        (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c)))
      p0206
  have p0208_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv n) (.cv q)) (syn_wb (.neg
            (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))) (.neg
            (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
              (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cplc syn_wrex syn_wex syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0207
  have p0208 :=
    @g_rspcv
      (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
          (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))))
      n (.cv q) (syn_cnnc) dv_cache_0027 dv_cache_0003 dv_cache_0028 p0208_e00_recanon
  have p0209 :=
    @g_adantl (.classMem (.cv q) (syn_cnnc))
      (.imp (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))) (.neg
          (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
            (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c)))))
      (.classMem (.cv m) (syn_cnnc)) p0208
  have p0210 := @g_addc6 (.cv m) (syn_c1c) (.cv m) (syn_c1c) (.cv m) (syn_c1c)
  have p0211 := @g_addc6 (.cv q) (syn_c1c) (.cv q) (syn_c1c) (.cv q) (syn_c1c)
  have p0212 :=
    @g_addceq1i
      (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
        (syn_cplc (.cv q) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q))
        (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)))
      (syn_c1c) p0211
  have p0213 :=
    @g_addc32 (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q))
      (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)) (syn_c1c)
  have p0214 :=
    @g_eqtri
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
          (syn_cplc (.cv q) (syn_c1c))) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q))
          (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c))) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))
        (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)))
      p0212 p0213
  have p0215 :=
    @g_eqeq12i
      (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (.cv m) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
        (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
          (syn_cplc (.cv q) (syn_c1c))) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))
        (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)))
      p0210 p0214
  have p0216 := @g_nncaddccl (.cv m) (.cv m)
  have p0217 :=
    @g_anidms (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (.cv m) (.cv m)) (syn_cnnc)) p0216
  have p0218 := @g_nncaddccl (syn_cplc (.cv m) (.cv m)) (.cv m)
  have p0219 :=
    @g_mpancom (.classMem (syn_cplc (.cv m) (.cv m)) (syn_cnnc))
      (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m)) (syn_cnnc)) p0217 p0218
  have p0220 := @g_nncaddccl (.cv q) (.cv q)
  have p0221 :=
    @g_anidms (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cplc (.cv q) (.cv q)) (syn_cnnc)) p0220
  have p0222 := @g_nncaddccl (syn_cplc (.cv q) (.cv q)) (.cv q)
  have p0223 :=
    @g_mpancom (.classMem (syn_cplc (.cv q) (.cv q)) (syn_cnnc))
      (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_cnnc)) p0221 p0222
  have p0224 := @g_peano2 (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q))
  have p0225 :=
    @g_syl (.classMem (.cv q) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c)) (syn_cnnc))
      p0223 p0224
  have p0226 := @g_n_1cnnc
  have p0228 := @g_nncaddccl (syn_c1c) (syn_c1c)
  have p0229 :=
    @g_mp2an (.classMem (syn_c1c) (syn_cnnc)) (.classMem (syn_c1c) (syn_cnnc))
      (.classMem (syn_cplc (syn_c1c) (syn_c1c)) (syn_cnnc)) p0226 p0226 p0228
  have p0231 := @g_nncaddccl (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)
  have p0232 :=
    @g_mp2an (.classMem (syn_cplc (syn_c1c) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_c1c) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)) (syn_cnnc)) p0229
      p0226 p0231
  have p0233 :=
    @g_addccan1 (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c))
      (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
      (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))
  have p0234 :=
    @g_mp3an3 (.classMem (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)) (syn_cnnc))
      (syn_wb (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
            (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))
            (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c))))
        (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
          (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))))
      p0232 p0233
  have p0235 :=
    @g_syl2an (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c)) (syn_cnnc))
      (syn_wb (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
            (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))
            (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c))))
        (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
          (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))))
      (.classMem (.cv q) (syn_cnnc)) p0219 p0225 p0234
  have p0236 :=
    @g_syl5bb
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c))) (syn_cplc
          (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
            (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
          (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c)))
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c))
          (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_c1c))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc)))
      (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
        (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c)))
      p0215 p0235
  have p0237 :=
    @g_biimpd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c))) (syn_cplc
          (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
            (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
        (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c)))
      p0236
  have p0238 :=
    @g_nsyld (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc)))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
        (syn_cplc (syn_cplc (syn_cplc (.cv q) (.cv q)) (.cv q)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c))) (syn_cplc
          (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
            (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)))
      p0209 p0237
  have p0239 :=
    @g_imp (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc)))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c))) (syn_cplc
            (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
              (syn_cplc (.cv q) (syn_c1c))) (syn_c1c))))
      p0238
  have p0240 :=
    @g_an32s (.classMem (.cv m) (syn_cnnc)) (.classMem (.cv q) (syn_cnnc))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c))) (syn_cplc
            (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
              (syn_cplc (.cv q) (syn_c1c))) (syn_c1c))))
      p0239
  have p0241 :=
    @g_addceq12 (.cv p) (.cv p) (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))
  have p0242 :=
    @g_anidms (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
      (.classEq (syn_cplc (.cv p) (.cv p))
        (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))))
      p0241
  have p0243 := @g_id (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
  have p0244 :=
    @g_addceq12d (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
      (syn_cplc (.cv p) (.cv p))
      (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c))) (.cv p)
      (syn_cplc (.cv q) (syn_c1c)) p0242 p0243
  have p0245 :=
    @g_addceq1d (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
      (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p))
      (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
        (syn_cplc (.cv q) (syn_c1c)))
      (syn_c1c) p0244
  have p0246 :=
    @g_eqeq2d (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
          (syn_cplc (.cv q) (syn_c1c))) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (.cv m) (syn_c1c)))
      p0245
  have p0247 :=
    @g_notbid (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c)))
        (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (.cv m) (syn_c1c))) (syn_cplc
          (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
            (syn_cplc (.cv q) (syn_c1c))) (syn_c1c)))
      p0246
  have p0248 :=
    @g_syl5ibrcom
      (syn_wa (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wral n (syn_cnnc) (.neg
              (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
                (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))))
        (.classMem (.cv q) (syn_cnnc)))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))))
      (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c))) (syn_cplc
            (syn_cplc (syn_cplc (syn_cplc (.cv q) (syn_c1c)) (syn_cplc (.cv q) (syn_c1c)))
              (syn_cplc (.cv q) (syn_c1c))) (syn_c1c))))
      p0240 p0247
  have p0249 :=
    @g_rexlimdva
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wral n (syn_cnnc) (.neg
            (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))))
      (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))))
      q (syn_cnnc) dv_cache_0029 dv_cache_0030 p0248
  have p0250 :=
    @g_jaod
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wral n (syn_cnnc) (.neg
            (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))))
      (.classEq (.cv p) (syn_c0c))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))))
      (syn_wrex q (syn_cnnc) (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))) p0200 p0249
  have p0251 :=
    @g_syl5bi (.classMem (.cv p) (syn_cnnc))
      (syn_wo (.classEq (.cv p) (syn_c0c))
        (syn_wrex q (syn_cnnc) (.classEq (.cv p) (syn_cplc (.cv q) (syn_c1c)))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wral n (syn_cnnc) (.neg
            (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))))
      p0167 p0250
  have p0252 :=
    @g_ralrimiv
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (syn_wral n (syn_cnnc) (.neg
            (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
              (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))))
      (.neg (.classEq
          (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (.cv m) (syn_c1c)))
          (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c))))
      p (syn_cnnc) dv_cache_0031 p0251
  have p0253 :=
    @g_ex (.classMem (.cv m) (syn_cnnc))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (syn_wral p (syn_cnnc) (.neg (.classEq
            (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
              (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c)))))
      p0252
  have p0254 :=
    @g_finds
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv a) (.cv a)) (.cv a))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_c0c)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc (.cv m) (.cv m)) (.cv m))
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (syn_wral p (syn_cnnc) (.neg (.classEq
            (syn_cplc (syn_cplc (syn_cplc (.cv m) (syn_c1c)) (syn_cplc (.cv m) (syn_c1c)))
              (syn_cplc (.cv m) (syn_c1c)))
            (syn_cplc (syn_cplc (syn_cplc (.cv p) (.cv p)) (.cv p)) (syn_c1c)))))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc A A) A)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      a m A dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035 dv_cache_0036
      dv_cache_0037 dv_cache_0038 p0108 p0119 p0126 p0142 p0149 p0166 p0253
  have p0255 := @g_addceq12 (.cv n) (.cv n) B B
  have p0256 :=
    @g_anidms (.classEq (.cv n) B) (.classEq (syn_cplc (.cv n) (.cv n)) (syn_cplc B B))
      p0255
  have p0257 := @g_id (.classEq (.cv n) B)
  have p0258 :=
    @g_addceq12d (.classEq (.cv n) B) (syn_cplc (.cv n) (.cv n)) (syn_cplc B B) (.cv n) B
      p0256 p0257
  have p0259 :=
    @g_addceq1d (.classEq (.cv n) B) (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
      (syn_cplc (syn_cplc B B) B) (syn_c1c) p0258
  have p0260 :=
    @g_eqeq2d (.classEq (.cv n) B)
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c1c)) (syn_cplc (syn_cplc A A) A) p0259
  have p0261 :=
    @g_notbid (.classEq (.cv n) B)
      (.classEq (syn_cplc (syn_cplc A A) A)
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc A A) A) (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c1c)))
      p0260
  have p0262 :=
    @g_rspccv
      (.neg (.classEq (syn_cplc (syn_cplc A A) A)
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.neg (.classEq (syn_cplc (syn_cplc A A) A)
          (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c1c))))
      n B (syn_cnnc) dv_cache_0039 dv_cache_0003 dv_cache_0040 p0261
  have p0263 :=
    @g_syl (.classMem A (syn_cnnc))
      (syn_wral n (syn_cnnc) (.neg (.classEq (syn_cplc (syn_cplc A A) A)
            (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      (.imp (.classMem B (syn_cnnc)) (.neg (.classEq (syn_cplc (syn_cplc A A) A)
            (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c1c)))))
      p0254 p0262
  have p0264 :=
    @g_imp (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))
      (.neg (.classEq (syn_cplc (syn_cplc A A) A)
          (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c1c))))
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

@[expose]
noncomputable def g_nnc3n3p2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc))) (.neg
          (.classEq (syn_cplc (syn_cplc A A) A)
            (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c))))) :=
  by
  have p0000 := @g_peano2 B
  have p0001 := @g_nnc3n3p1 (syn_cplc B (syn_c1c)) A
  have p0002 :=
    @g_sylan (.classMem B (syn_cnnc)) (.classMem (syn_cplc B (syn_c1c)) (syn_cnnc))
      (.classMem A (syn_cnnc))
      (.neg (.classEq (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c)))
            (syn_cplc B (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c))))
      p0000 p0001
  have p0003 :=
    @g_ancoms (.classMem B (syn_cnnc)) (.classMem A (syn_cnnc))
      (.neg (.classEq (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c)))
            (syn_cplc B (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c))))
      p0002
  have p0004 :=
    @g_eqcom (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c))
  have p0005 := @g_addc4 B (syn_c1c) B (syn_c1c)
  have p0006 :=
    @g_addceq1i (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c)))
      (syn_cplc (syn_cplc B B) (syn_cplc (syn_c1c) (syn_c1c))) B p0005
  have p0007 := @g_addc32 (syn_cplc B B) (syn_cplc (syn_c1c) (syn_c1c)) B
  have p0008 := @g_n_1p1e2c
  have p0009 :=
    @g_addceq2i (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c) (syn_cplc (syn_cplc B B) B) p0008
  have p0010 :=
    @g_n_3eqtrri (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) B)
      (syn_cplc (syn_cplc (syn_cplc B B) (syn_cplc (syn_c1c) (syn_c1c))) B)
      (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_cplc (syn_c1c) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) p0006 p0007 p0009
  have p0011 :=
    @g_addceq1i (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c))
      (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) B) (syn_c1c)
      p0010
  have p0012 :=
    @g_addcass (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) B (syn_c1c)
  have p0013 :=
    @g_eqtri (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) B) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) (syn_cplc B (syn_c1c)))
      p0011 p0012
  have p0014 :=
    @g_eqeq1i (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c))) (syn_cplc B (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)) p0013
  have p0015 :=
    @g_bitri
      (.classEq (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c)))
          (syn_cplc B (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)))
      p0004 p0014
  have p0016 :=
    @g_sylnibr (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc B (syn_c1c)) (syn_cplc B (syn_c1c)))
          (syn_cplc B (syn_c1c))) (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c)))
      p0003 p0015
  have p0017 := @g_nncaddccl A A
  have p0018 :=
    @g_anidms (.classMem A (syn_cnnc)) (.classMem (syn_cplc A A) (syn_cnnc)) p0017
  have p0019 := @g_nncaddccl (syn_cplc A A) A
  have p0020 :=
    @g_mpancom (.classMem (syn_cplc A A) (syn_cnnc)) (.classMem A (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc A A) A) (syn_cnnc)) p0018 p0019
  have p0021 := @g_nncaddccl B B
  have p0022 :=
    @g_anidms (.classMem B (syn_cnnc)) (.classMem (syn_cplc B B) (syn_cnnc)) p0021
  have p0023 := @g_nncaddccl (syn_cplc B B) B
  have p0024 :=
    @g_mpancom (.classMem (syn_cplc B B) (syn_cnnc)) (.classMem B (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc B B) B) (syn_cnnc)) p0022 p0023
  have p0025 := @g_n_2nnc
  have p0026 := @g_nncaddccl (syn_cplc (syn_cplc B B) B) (syn_c2c)
  have p0027 :=
    @g_sylancl (.classMem B (syn_cnnc)) (.classMem (syn_cplc (syn_cplc B B) B) (syn_cnnc))
      (.classMem (syn_c2c) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_cnnc)) p0024 p0025
      p0026
  have p0028 :=
    @g_suc11nnc (syn_cplc (syn_cplc A A) A)
      (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c))
  have p0029 :=
    @g_syl2an (.classMem A (syn_cnnc)) (.classMem (syn_cplc (syn_cplc A A) A) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_cnnc))
      (syn_wb (.classEq (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c))
          (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c)))
        (.classEq (syn_cplc (syn_cplc A A) A) (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c))))
      (.classMem B (syn_cnnc)) p0020 p0027 p0028
  have p0030 :=
    @g_mtbid (syn_wa (.classMem A (syn_cnnc)) (.classMem B (syn_cnnc)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc A A) A) (syn_c1c))
        (syn_cplc (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc A A) A) (syn_cplc (syn_cplc (syn_cplc B B) B) (syn_c2c)))
      p0016 p0029
  exact p0030

@[expose]
noncomputable def g_nchoicelem1 (A : Class) :
    Nominal.NPrf
      (.imp (.classMem A (syn_cnnc)) (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))))) :=
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
  have dv_cache_0002 : n ∉ ((Wff.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))))).fv :=
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
  have p0000 := @g_nncdiv3 A n dv_cache_0001
  have p0001 := @g_id (.classMem (.cv n) (syn_cnnc))
  have p0002 := @g_nntccl (.cv n)
  have p0003 := @g_nnc3n3p1 (.cv n) (syn_ctc (.cv n))
  have p0004 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_ctc (.cv n)) (syn_cnnc))
      (.neg (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc
            (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n)))
            (syn_c1c))))
      p0001 p0002 p0003
  have p0005 := @g_nncaddccl (.cv n) (.cv n)
  have p0006 :=
    @g_anidms (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) p0005
  have p0007 := @g_nnnc (syn_cplc (.cv n) (.cv n))
  have p0008 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cncs)) p0006 p0007
  have p0009 := @g_nnnc (.cv n)
  have p0010 := @g_tcdi (syn_cplc (.cv n) (.cv n)) (.cv n)
  have p0011 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cncs)) (.classMem (.cv n) (syn_cncs))
      (.classEq (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (syn_cplc (syn_ctc (syn_cplc (.cv n) (.cv n))) (syn_ctc (.cv n))))
      p0008 p0009 p0010
  have p0012 := @g_tcdi (.cv n) (.cv n)
  have p0013 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc)) (.classMem (.cv n) (syn_cncs))
      (.classMem (.cv n) (syn_cncs))
      (.classEq (syn_ctc (syn_cplc (.cv n) (.cv n)))
        (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))))
      p0009 p0009 p0012
  have p0014 :=
    @g_addceq1d (.classMem (.cv n) (syn_cnnc)) (syn_ctc (syn_cplc (.cv n) (.cv n)))
      (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n)) p0013
  have p0015 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (syn_cplc (syn_ctc (syn_cplc (.cv n) (.cv n))) (syn_ctc (.cv n)))
      (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n))) p0011
      p0014
  have p0016 :=
    @g_addceq1d (.classMem (.cv n) (syn_cnnc))
      (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n)))
      (syn_c1c) p0015
  have p0017 :=
    @g_eqeq2d (.classMem (.cv n) (syn_cnnc))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n)))
        (syn_c1c))
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) p0016
  have p0018 :=
    @g_mtbird (.classMem (.cv n) (syn_cnnc))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
        (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc
          (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n)))
          (syn_c1c)))
      p0004 p0017
  have p0019 := @g_id (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
  have p0020 := @g_tceq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0021 :=
    @g_addceq1d (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_ctc A)
      (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c) p0020
  have p0022 :=
    @g_eqeq12d (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) A
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_ctc A) (syn_c1c))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c)) p0019
      p0021
  have p0023 :=
    @g_notbid (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
        (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c)))
      p0022
  have p0024 :=
    @g_syl5ibrcom (.classMem (.cv n) (syn_cnnc))
      (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))))
      (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.neg (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
          (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_c1c))))
      p0018 p0023
  have p0025 := @g_nncaddccl (syn_cplc (.cv n) (.cv n)) (.cv n)
  have p0026 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (.cv n)) (syn_cnnc)) (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc)) p0006 p0001
      p0025
  have p0027 := @g_nnnc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0028 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cncs)) p0026 p0027
  have p0029 := @g_n_1cnc
  have p0030 := @g_tcdi (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)
  have p0031 :=
    @g_sylancl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cncs))
      (.classMem (syn_c1c) (syn_cncs))
      (.classEq (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_ctc (syn_c1c))))
      p0028 p0029 p0030
  have p0032 := @g_tc1c
  have p0033 :=
    @g_a1i (.classEq (syn_ctc (syn_c1c)) (syn_c1c)) (.classMem (.cv n) (syn_cnnc)) p0032
  have p0034 :=
    @g_addceq12d (.classMem (.cv n) (syn_cnnc))
      (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n)))
      (syn_ctc (syn_c1c)) (syn_c1c) p0015 p0033
  have p0035 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))) (syn_ctc (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n)))
        (syn_c1c))
      p0031 p0034
  have p0036 :=
    @g_eqeq2d (.classMem (.cv n) (syn_cnnc))
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n)))
        (syn_c1c))
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) p0035
  have p0037 :=
    @g_mtbird (.classMem (.cv n) (syn_cnnc))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
        (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc
          (syn_cplc (syn_cplc (syn_ctc (.cv n)) (syn_ctc (.cv n))) (syn_ctc (.cv n)))
          (syn_c1c)))
      p0004 p0036
  have p0038 := @g_peano2 (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
  have p0039 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cnnc))
      p0026 p0038
  have p0040 :=
    @g_nntccl (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0041 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (syn_cnnc))
      p0039 p0040
  have p0042 :=
    @g_suc11nnc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
  have p0043 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc))
      (.classMem (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (syn_cnnc))
      (syn_wb (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
          (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
            (syn_c1c))) (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
          (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))))
      p0026 p0041 p0042
  have p0044 :=
    @g_mtbird (.classMem (.cv n) (syn_cnnc))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cplc
          (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n))
        (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))))
      p0037 p0043
  have p0045 :=
    @g_id (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
  have p0046 :=
    @g_tceq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
  have p0047 :=
    @g_addceq1d
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (syn_ctc A)
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (syn_c1c) p0046
  have p0048 :=
    @g_eqeq12d
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))) A
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
      (syn_cplc (syn_ctc A) (syn_c1c))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (syn_c1c))
      p0045 p0047
  have p0049 :=
    @g_notbid
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)) (syn_cplc
          (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (syn_c1c)))
      p0048
  have p0050 :=
    @g_syl5ibrcom (.classMem (.cv n) (syn_cnnc))
      (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))))
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.neg (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c))
          (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
            (syn_c1c))))
      p0044 p0049
  have p0051 := @g_peano2 (.cv n)
  have p0052 := @g_nntccl (syn_cplc (.cv n) (syn_c1c))
  have p0053 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_cnnc)) p0051 p0052
  have p0054 := @g_nnc3n3p2 (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (.cv n)
  have p0055 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_cnnc))
      (.classMem (.cv n) (syn_cnnc))
      (.neg (.classEq (syn_cplc (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c)))
              (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      p0053 p0001 p0054
  have p0056 := @g_n_2nnc
  have p0057 := @g_nncaddccl (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)
  have p0058 :=
    @g_sylancl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cnnc))
      (.classMem (syn_c2c) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cnnc))
      p0026 p0056 p0057
  have p0059 := @g_nnnc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0060 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cncs))
      p0058 p0059
  have p0062 :=
    @g_tcdi (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c)
  have p0063 :=
    @g_sylancl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cncs))
      (.classMem (syn_c1c) (syn_cncs))
      (.classEq (syn_ctc
          (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
            (syn_c1c))) (syn_cplc
          (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
          (syn_ctc (syn_c1c))))
      p0060 p0029 p0062
  have p0064 :=
    @g_eqcomd (.classMem (.cv n) (syn_cnnc))
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
          (syn_c1c)))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
        (syn_ctc (syn_c1c)))
      p0063
  have p0066 :=
    @g_addceq2i (syn_ctc (syn_c1c)) (syn_c1c)
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) p0032
  have p0067 := @g_addccom (syn_cplc (syn_c1c) (syn_c1c)) (.cv n)
  have p0068 := @g_n_1p1e2c
  have p0069 := @g_addceq2i (syn_cplc (syn_c1c) (syn_c1c)) (syn_c2c) (.cv n) p0068
  have p0070 :=
    @g_eqtr2i (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (.cv n))
      (syn_cplc (.cv n) (syn_cplc (syn_c1c) (syn_c1c))) (syn_cplc (.cv n) (syn_c2c)) p0067
      p0069
  have p0071 :=
    @g_addceq1i (syn_cplc (.cv n) (syn_c2c))
      (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (.cv n)) (syn_c1c) p0070
  have p0072 := @g_addcass (.cv n) (syn_c2c) (syn_c1c)
  have p0073 := @g_addcass (syn_cplc (syn_c1c) (syn_c1c)) (.cv n) (syn_c1c)
  have p0074 :=
    @g_n_3eqtr3i (syn_cplc (syn_cplc (.cv n) (syn_c2c)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (.cv n)) (syn_c1c))
      (syn_cplc (.cv n) (syn_cplc (syn_c2c) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))) p0071 p0072
      p0073
  have p0075 :=
    @g_addceq2i (syn_cplc (.cv n) (syn_cplc (syn_c2c) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
      (syn_cplc (.cv n) (.cv n)) p0074
  have p0076 :=
    @g_addcass (syn_cplc (.cv n) (.cv n)) (.cv n) (syn_cplc (syn_c2c) (syn_c1c))
  have p0077 :=
    @g_addcass (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c))
      (syn_cplc (.cv n) (syn_c1c))
  have p0078 :=
    @g_n_3eqtr4i
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (.cv n) (syn_cplc (syn_c2c) (syn_c1c))))
      (syn_cplc (syn_cplc (.cv n) (.cv n))
        (syn_cplc (syn_cplc (syn_c1c) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_c2c) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c)))
        (syn_cplc (.cv n) (syn_c1c)))
      p0075 p0076 p0077
  have p0079 :=
    @g_addcass (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c) (syn_c1c)
  have p0080 := @g_addc4 (.cv n) (syn_c1c) (.cv n) (syn_c1c)
  have p0081 :=
    @g_addceq1i (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c)))
      (syn_cplc (.cv n) (syn_c1c)) p0080
  have p0082 :=
    @g_n_3eqtr4i
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_cplc (syn_c2c) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_cplc (syn_c1c) (syn_c1c)))
        (syn_cplc (.cv n) (syn_c1c)))
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
        (syn_cplc (.cv n) (syn_c1c)))
      p0078 p0079 p0081
  have p0083 :=
    @g_tceq
      (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
        (syn_cplc (.cv n) (syn_c1c)))
  have p0084 := Nominal.mp p0082 p0083
  have p0085 :=
    @g_n_3eqtr3g (.classMem (.cv n) (syn_cnnc))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
        (syn_ctc (syn_c1c)))
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
          (syn_c1c)))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
        (syn_c1c))
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
          (syn_cplc (.cv n) (syn_c1c))))
      p0064 p0066 p0084
  have p0086 := @g_nnnc (syn_cplc (.cv n) (syn_c1c))
  have p0087 :=
    @g_syl (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs)) p0051 p0086
  have p0088 := @g_ncaddccl (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))
  have p0089 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs))
      (.classMem (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
        (syn_cncs))
      p0087 p0087 p0088
  have p0090 :=
    @g_tcdi (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
      (syn_cplc (.cv n) (syn_c1c))
  have p0091 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
        (syn_cncs))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs))
      (.classEq (syn_ctc
          (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
            (syn_cplc (.cv n) (syn_c1c)))) (syn_cplc
          (syn_ctc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))
          (syn_ctc (syn_cplc (.cv n) (syn_c1c)))))
      p0089 p0087 p0090
  have p0092 := @g_tcdi (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))
  have p0093 :=
    @g_syl2anc (.classMem (.cv n) (syn_cnnc))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs))
      (.classMem (syn_cplc (.cv n) (syn_c1c)) (syn_cncs))
      (.classEq (syn_ctc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))
        (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c)))
          (syn_ctc (syn_cplc (.cv n) (syn_c1c)))))
      p0087 p0087 p0092
  have p0094 :=
    @g_addceq1d (.classMem (.cv n) (syn_cnnc))
      (syn_ctc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))
      (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c))) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))
      (syn_ctc (syn_cplc (.cv n) (syn_c1c))) p0093
  have p0095 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
          (syn_cplc (.cv n) (syn_c1c))))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c))))
        (syn_ctc (syn_cplc (.cv n) (syn_c1c))))
      (syn_cplc (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c)))
          (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))
      p0091 p0094
  have p0096 :=
    @g_eqtrd (.classMem (.cv n) (syn_cnnc))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
        (syn_c1c))
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (syn_c1c)) (syn_cplc (.cv n) (syn_c1c)))
          (syn_cplc (.cv n) (syn_c1c))))
      (syn_cplc (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c)))
          (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))
      p0085 p0095
  have p0097 :=
    @g_eqeq1d (.classMem (.cv n) (syn_cnnc))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
        (syn_c1c))
      (syn_cplc (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c)))
          (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) p0096
  have p0098 :=
    @g_mtbird (.classMem (.cv n) (syn_cnnc))
      (.classEq (syn_cplc
          (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
          (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (.classEq (syn_cplc (syn_cplc (syn_ctc (syn_cplc (.cv n) (syn_c1c)))
            (syn_ctc (syn_cplc (.cv n) (syn_c1c)))) (syn_ctc (syn_cplc (.cv n) (syn_c1c))))
        (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      p0055 p0097
  have p0099 :=
    @g_eqcom
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
        (syn_c1c))
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0100 :=
    @g_sylnib (.classMem (.cv n) (syn_cnnc))
      (.classEq (syn_cplc
          (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
          (syn_c1c)) (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cplc
          (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
          (syn_c1c)))
      p0098 p0099
  have p0101 :=
    @g_id (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
  have p0102 :=
    @g_tceq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
  have p0103 :=
    @g_addceq1d
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (syn_ctc A)
      (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (syn_c1c) p0102
  have p0104 :=
    @g_eqeq12d
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))) A
      (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
      (syn_cplc (syn_ctc A) (syn_c1c))
      (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
        (syn_c1c))
      p0101 p0103
  have p0105 :=
    @g_notbid
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)) (syn_cplc
          (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
          (syn_c1c)))
      p0104
  have p0106 :=
    @g_syl5ibrcom (.classMem (.cv n) (syn_cnnc))
      (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))))
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      (.neg (.classEq (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))
          (syn_cplc (syn_ctc (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
            (syn_c1c))))
      p0100 p0105
  have p0107 :=
    @g_n_3jaod (.classMem (.cv n) (syn_cnnc))
      (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
      (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c))))
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
      (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))
      p0024 p0050 p0106
  have p0108 :=
    @g_rexlimiv
      (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
        (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
        (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c))))
      (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))) n (syn_cnnc) dv_cache_0002
      p0107
  have p0109 :=
    @g_syl (.classMem A (syn_cnnc))
      (syn_wrex n (syn_cnnc) (syn_w3o (.classEq A (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)))
          (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c1c)))
          (.classEq A (syn_cplc (syn_cplc (syn_cplc (.cv n) (.cv n)) (.cv n)) (syn_c2c)))))
      (.neg (.classEq A (syn_cplc (syn_ctc A) (syn_c1c)))) p0000 p0108
  exact p0109

@[expose]
noncomputable def g_freceq12 (F : Class) (G : Class) (I : Class) (J : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classEq F G) (.classEq I J))
        (.classEq (syn_cfrec F I) (syn_cfrec G J))) :=
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
  have p0000 := @g_opeq2 I J (syn_c0c)
  have p0001 := @g_sneqd (.classEq I J) (syn_cop (syn_c0c) I) (syn_cop (syn_c0c) J) p0000
  have p0002 :=
    @g_clos1eq1 (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F)
      (syn_csn (syn_cop (syn_c0c) I)) (syn_csn (syn_cop (syn_c0c) J))
  have p0003 :=
    @g_syl (.classEq I J)
      (.classEq (syn_csn (syn_cop (syn_c0c) I)) (syn_csn (syn_cop (syn_c0c) J)))
      (.classEq (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
          (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F))
        (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J))
          (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F)))
      p0001 p0002
  have p0004 := @g_pprodeq2 F G (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c)))
  have p0005 :=
    @g_clos1eq2 (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F)
      (syn_csn (syn_cop (syn_c0c) J))
      (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)
  have p0006 :=
    @g_syl (.classEq F G)
      (.classEq (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F)
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      (.classEq (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J))
          (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F))
        (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J))
          (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G)))
      p0004 p0005
  have p0007 :=
    @g_sylan9eqr (.classEq I J) (.classEq F G)
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F))
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F))
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      p0003 p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x F I
      dv_cache_0001 dv_cache_0002
  have p0009 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_frec x G J
      dv_cache_0003 dv_cache_0004
  have p0010 :=
    @g_n_3eqtr4g (syn_wa (.classEq F G) (.classEq I J))
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) I))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) F))
      (syn_cclos1 (syn_csn (syn_cop (syn_c0c) J))
        (syn_cpprod (syn_cmpt x (syn_cvv) (syn_cplc (.cv x) (syn_c1c))) G))
      (syn_cfrec F I) (syn_cfrec G J) p0007 p0008 p0009
  exact p0010


end NFChoice.DirectNominalPrf.WPPReplay

end
