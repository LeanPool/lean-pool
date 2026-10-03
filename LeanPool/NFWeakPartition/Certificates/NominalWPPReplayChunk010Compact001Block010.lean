/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block009

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part026`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_vfinncsp :
    Nominal.NPrf
      (.imp (.classMem (syn_cvv) (syn_cfin)) (.classEq (syn_cncfin (syn_cspfin))
          (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have dv_cache_0001 : a ≠ x := by exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0002 :
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
    clear dv_cache_0001
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
  have dv_cache_0003 : t ∉ ((syn_cpw1 (syn_cspfin))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0004 : t ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_a, not_false_eq_true])
  have dv_cache_0005 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0006 : x ∉ ((syn_cspfin)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0007 :
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
      dv_cache_0006
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
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_a, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((syn_cspfin)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0009 : x ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show x ≠ t from (by exact fresh_x_ne_t))
  have dv_cache_0010 : t ∉ ((syn_csn (.cv x))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0011 :
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
  have dv_cache_0012 :
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
  have dv_cache_0013 : a ∉ ((syn_cspfin)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0014 : a ∉ ((syn_cncfin (syn_cspfin))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0015 : x ∉ ((syn_cncfin (syn_cspfin))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_vfinspeqtncv x a dv_cache_0001
  have p0001 :=
    @g_ncfineq (syn_cspfin)
      (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_csn (syn_cncfin (syn_cvv))))
  have p0002 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_cspfin)
        (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))))
      (.classEq (syn_cncfin (syn_cspfin)) (syn_cncfin (syn_cun
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_cncfin (syn_cvv))))))
      p0000 p0001
  have p0003 := @g_vfinncvntsp x a dv_cache_0001
  have p0004 :=
    @g_disjsn (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_cncfin (syn_cvv))
  have p0005 :=
    @g_sylibr (.classMem (syn_cvv) (syn_cfin))
      (.neg (.classMem (syn_cncfin (syn_cvv))
          (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      (.classEq
        (syn_cin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))) (syn_c0))
      p0003 p0004
  have p0006 := @g_vex a
  have p0007 :=
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
      (syn_cpw1 (syn_cspfin)) (.cv a) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006
  have p0008 :=
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
  have p0009 := @g_elpw1 x (.cv t) (syn_cspfin) dv_cache_0005 dv_cache_0006
  have p0010 :=
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
      p0009
  have p0011 :=
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
      x (syn_cspfin) dv_cache_0007
  have p0012 :=
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
      p0010 p0011
  have p0013 :=
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
      t p0012
  have p0014 :=
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
      x t (syn_cspfin) dv_cache_0008 dv_cache_0009
  have p0015 :=
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
      p0013 p0014
  have p0016 :=
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
      p0008 p0015
  have p0017 :=
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
      p0007 p0016
  have p0018 := @g_snex (.cv x)
  have p0019 := @g_opkeq1 (.cv t) (syn_csn (.cv x)) (.cv a)
  have p0020 :=
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
      p0019
  have p0021 :=
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
      t (syn_csn (.cv x)) dv_cache_0010 dv_cache_0011 p0018 p0020
  have p0022 := @g_vex x
  have p0023 := @g_eqtfinrelk (.cv x) (.cv a) p0022 p0006
  have p0024 :=
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
      (.classEq (.cv a) (syn_ctfin (.cv x))) p0021 p0023
  have p0025 :=
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
      (.classEq (.cv a) (syn_ctfin (.cv x))) x (syn_cspfin) p0024
  have p0026 :=
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
      (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))) p0017 p0025
  have p0027 :=
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
      dv_cache_0012 p0026
  have p0028 := @g_tfinrelkex
  have p0029 := @g_spfinex
  have p0030 := @g_pw1ex (syn_cspfin) p0029
  have p0031 :=
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
      (syn_cpw1 (syn_cspfin)) p0028 p0030
  have p0032 :=
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
      p0027 p0031
  have p0033 := @g_snex (syn_cncfin (syn_cvv))
  have p0034 :=
    @g_ncfindi (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_csn (syn_cncfin (syn_cvv))) (syn_cvv) (syn_cvv)
  have p0035 :=
    @g_mp3an2
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem
          (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cvv)))
      (.classMem (syn_csn (syn_cncfin (syn_cvv))) (syn_cvv))
      (.classEq
        (syn_cin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))) (syn_c0))
      (.classEq (syn_cncfin (syn_cun
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_cncfin (syn_cvv))))) (syn_cplc (syn_cncfin
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
          (syn_cncfin (syn_csn (syn_cncfin (syn_cvv))))))
      p0033 p0034
  have p0036 :=
    @g_mpanl2 (.classMem (syn_cvv) (syn_cfin))
      (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_cvv))
      (.classEq
        (syn_cin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))) (syn_c0))
      (.classEq (syn_cncfin (syn_cun
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_cncfin (syn_cvv))))) (syn_cplc (syn_cncfin
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
          (syn_cncfin (syn_csn (syn_cncfin (syn_cvv))))))
      p0032 p0035
  have p0037 :=
    @g_mpdan (.classMem (syn_cvv) (syn_cfin))
      (.classEq
        (syn_cin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))) (syn_c0))
      (.classEq (syn_cncfin (syn_cun
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
            (syn_csn (syn_cncfin (syn_cvv))))) (syn_cplc (syn_cncfin
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
          (syn_cncfin (syn_csn (syn_cncfin (syn_cvv))))))
      p0005 p0036
  have p0038 :=
    @g_ncfinprop (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_cvv)
  have p0039 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin))
      (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_cvv))
      (syn_wa (.classMem (syn_cncfin
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
          (syn_cnnc)) (.classMem
          (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))) (syn_cncfin
            (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))))
      p0032 p0038
  have p0040 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin
          (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cnnc))
      (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      p0039
  have p0042 := @g_ncfinprop (syn_cspfin) (syn_cvv)
  have p0043 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cspfin) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc))
        (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin))))
      p0029 p0042
  have p0044 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc))
      (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin))) p0043
  have p0045 := @g_tfincl (syn_cncfin (syn_cspfin))
  have p0046 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc))
      (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_cnnc)) p0044 p0045
  have p0047 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin
          (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cnnc))
      (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      p0039
  have p0048 := @g_vfinspnn
  have p0049 := @g_difss (syn_cnnc) (syn_csn (syn_c0))
  have p0050 :=
    @g_syl6ss (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin)
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cnnc) p0048 p0049
  have p0051 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc))
      (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin))) p0043
  have p0052 :=
    @g_tfinnn x (syn_cspfin) (syn_cncfin (syn_cspfin)) a dv_cache_0013 dv_cache_0006
      dv_cache_0014 dv_cache_0015 dv_cache_0001
  have p0053 :=
    @g_syl3anc (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) (syn_wss (syn_cspfin) (syn_cnnc))
      (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin)))
      (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (syn_cncfin (syn_cspfin))))
      p0044 p0050 p0051 p0052
  have p0054 :=
    @g_nnceleq (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
      (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      (syn_ctfin (syn_cncfin (syn_cspfin)))
  have p0055 :=
    @g_syl22anc (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin
          (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))) (syn_cnnc))
      (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_cnnc))
      (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))))
      (.classMem (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
        (syn_ctfin (syn_cncfin (syn_cspfin))))
      (.classEq (syn_cncfin
          (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
        (syn_ctfin (syn_cncfin (syn_cspfin))))
      p0040 p0046 p0047 p0053 p0054
  have p0056 := @g_ncfinex (syn_cvv)
  have p0057 := @g_ncfinsn (syn_cncfin (syn_cvv)) (syn_cvv)
  have p0058 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cvv)) (syn_cvv))
      (.classEq (syn_cncfin (syn_csn (syn_cncfin (syn_cvv)))) (syn_c1c)) p0056 p0057
  have p0059 :=
    @g_addceq12d (.classMem (syn_cvv) (syn_cfin))
      (syn_cncfin (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_cncfin (syn_csn (syn_cncfin (syn_cvv))))
      (syn_c1c) p0055 p0058
  have p0060 :=
    @g_n_3eqtrd (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cspfin))
      (syn_cncfin
        (syn_cun (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))
          (syn_csn (syn_cncfin (syn_cvv)))))
      (syn_cplc (syn_cncfin
          (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
        (syn_cncfin (syn_csn (syn_cncfin (syn_cvv)))))
      (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) p0002 p0037 p0059
  exact p0060


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part027`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_vinf : Nominal.NPrf (.neg (.classMem (syn_cvv) (syn_cfin))) :=
  by
  have p0000 := @g_noel (syn_cncfin (syn_cspfin))
  have p0001 := @g_spfinex
  have p0002 := @g_ncfinprop (syn_cspfin) (syn_cvv)
  have p0003 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cspfin) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc))
        (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin))))
      p0001 p0002
  have p0004 := @g_ne0i (syn_cncfin (syn_cspfin)) (syn_cspfin)
  have p0005 :=
    @g_anim2i (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin)))
      (syn_wne (syn_cncfin (syn_cspfin)) (syn_c0))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc)) p0004
  have p0006 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin))
      (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc))
        (.classMem (syn_cspfin) (syn_cncfin (syn_cspfin))))
      (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc))
        (syn_wne (syn_cncfin (syn_cspfin)) (syn_c0)))
      p0003 p0005
  have p0007 := @g_eldifsn (syn_cncfin (syn_cspfin)) (syn_cnnc) (syn_c0)
  have p0008 :=
    @g_sylibr (.classMem (syn_cvv) (syn_cfin))
      (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cnnc))
        (syn_wne (syn_cncfin (syn_cspfin)) (syn_c0)))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0006
      p0007
  have p0009 := @g_evenoddnnnul
  have p0010 :=
    @g_syl6eleqr (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cspfin))
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cun (syn_cevenfin) (syn_coddfin))
      p0008 p0009
  have p0011 := @g_vfinncsp
  have p0012 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_cncfin (syn_cspfin))
        (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) p0011
  have p0013 := @g_eventfin (syn_cncfin (syn_cspfin))
  have p0014 :=
    @g_adantl (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))
      (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_cevenfin))
      (.classMem (syn_cvv) (syn_cfin)) p0013
  have p0015 := @g_evennnul (syn_cncfin (syn_cspfin))
  have p0016 :=
    @g_adantl (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))
      (syn_wne (syn_cncfin (syn_cspfin)) (syn_c0)) (.classMem (syn_cvv) (syn_cfin)) p0015
  have p0017 :=
    @g_eqnetrrd
      (syn_wa (.classMem (syn_cvv) (syn_cfin))
        (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)))
      (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c))
      (syn_c0) p0012 p0016
  have p0018 := @g_sucevenodd (syn_ctfin (syn_cncfin (syn_cspfin)))
  have p0019 :=
    @g_syl2anc
      (syn_wa (.classMem (syn_cvv) (syn_cfin))
        (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)))
      (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_cevenfin))
      (syn_wne (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_c0))
      (.classMem (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_coddfin))
      p0014 p0017 p0018
  have p0020 :=
    @g_eqeltrd
      (syn_wa (.classMem (syn_cvv) (syn_cfin))
        (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)))
      (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c))
      (syn_coddfin) p0012 p0019
  have p0021 :=
    @g_ex (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) p0020
  have p0022 :=
    @g_ancld (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) p0021
  have p0024 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_cncfin (syn_cspfin))
        (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) p0011
  have p0025 := @g_oddtfin (syn_cncfin (syn_cspfin))
  have p0026 :=
    @g_adantl (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin))
      (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_coddfin))
      (.classMem (syn_cvv) (syn_cfin)) p0025
  have p0027 := @g_oddnnul (syn_cncfin (syn_cspfin))
  have p0028 :=
    @g_adantl (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin))
      (syn_wne (syn_cncfin (syn_cspfin)) (syn_c0)) (.classMem (syn_cvv) (syn_cfin)) p0027
  have p0029 :=
    @g_eqnetrrd
      (syn_wa (.classMem (syn_cvv) (syn_cfin))
        (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)))
      (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c))
      (syn_c0) p0024 p0028
  have p0030 := @g_sucoddeven (syn_ctfin (syn_cncfin (syn_cspfin)))
  have p0031 :=
    @g_syl2anc
      (syn_wa (.classMem (syn_cvv) (syn_cfin))
        (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)))
      (.classMem (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_coddfin))
      (syn_wne (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_c0))
      (.classMem (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c)) (syn_cevenfin))
      p0026 p0029 p0030
  have p0032 :=
    @g_eqeltrd
      (syn_wa (.classMem (syn_cvv) (syn_cfin))
        (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)))
      (syn_cncfin (syn_cspfin)) (syn_cplc (syn_ctfin (syn_cncfin (syn_cspfin))) (syn_c1c))
      (syn_cevenfin) p0024 p0031
  have p0033 :=
    @g_ex (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) p0032
  have p0034 :=
    @g_ancrd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin)) p0033
  have p0035 :=
    @g_jaod (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))
      (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))
        (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)) p0022 p0034
  have p0036 := @g_elun (syn_cncfin (syn_cspfin)) (syn_cevenfin) (syn_coddfin)
  have p0037 := @g_elin (syn_cncfin (syn_cspfin)) (syn_cevenfin) (syn_coddfin)
  have p0038 :=
    @g_n_3imtr4g (.classMem (syn_cvv) (syn_cfin))
      (syn_wo (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))
        (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)))
      (syn_wa (.classMem (syn_cncfin (syn_cspfin)) (syn_cevenfin))
        (.classMem (syn_cncfin (syn_cspfin)) (syn_coddfin)))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cin (syn_cevenfin) (syn_coddfin))) p0035
      p0036 p0037
  have p0039 :=
    @g_mpd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cun (syn_cevenfin) (syn_coddfin)))
      (.classMem (syn_cncfin (syn_cspfin)) (syn_cin (syn_cevenfin) (syn_coddfin))) p0010
      p0038
  have p0040 := @g_evenodddisj
  have p0041 :=
    @g_syl6eleq (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cspfin))
      (syn_cin (syn_cevenfin) (syn_coddfin)) (syn_c0) p0039 p0040
  have p0042 :=
    @g_mto (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cspfin)) (syn_c0))
      p0000 p0041
  exact p0042

@[expose]
noncomputable def g_nulnnn : Nominal.NPrf (.neg (.classMem (syn_c0) (syn_cnnc))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let n : Var := freshVar proofSupport 1
  let m : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  have fresh_x_ne_n : x ≠ n :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_n_ne_x : n ≠ x := Ne.symm fresh_x_ne_n
  have fresh_x_ne_m : x ≠ m :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_n_ne_m : n ≠ m :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_m_ne_n : m ≠ n := Ne.symm fresh_n_ne_m
  have fresh_m_ne_a : m ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_m : a ≠ m := Ne.symm fresh_m_ne_a
  have dv_cache_0001 : n ∉ ((syn_c0)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : a ∉ ((Class.cv m)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_m, not_false_eq_true])
  have dv_cache_0003 : x ∉ ((syn_ccompl (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_a,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0005 : x ∉ ((syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_x_ne_m, fresh_x_ne_a, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0006 : a ∉ ((syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
  have dv_cache_0007 : a ∉ ((Wff.classMem (.cv m) (syn_cnnc))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 : n ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_x, not_false_eq_true])
  have dv_cache_0009 : n ∉ ((syn_wne (.cv m) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0010 : m ∉ ((syn_wne (.cv n) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_m_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0011 : n ∉ ((syn_wne (syn_c0c) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : n ∉ ((syn_wne (.cv x) (syn_c0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0013 : n ∉ ((syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 : n ≠ m :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact (show n ≠ m from (by exact fresh_n_ne_m))
  have dv_cache_0015 : x ∉ ((syn_c0)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((syn_cnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have p0000 := @g_complab (.classEq (.cv n) (syn_c0)) n
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sn n (syn_c0)
      dv_cache_0001
  have p0002 := @g_compleqi (syn_csn (syn_c0)) (.cab n (.classEq (.cv n) (syn_c0))) p0001
  have p0003 := (Nominal.biimpRefl (syn_wne (.cv n) (syn_c0)))
  have p0004 :=
    @g_abbii (syn_wne (.cv n) (syn_c0)) (.neg (.classEq (.cv n) (syn_c0))) n p0003
  have p0005 :=
    @g_n_3eqtr4ri (syn_ccompl (.cab n (.classEq (.cv n) (syn_c0))))
      (.cab n (.neg (.classEq (.cv n) (syn_c0)))) (syn_ccompl (syn_csn (syn_c0)))
      (.cab n (syn_wne (.cv n) (syn_c0))) p0000 p0002 p0004
  have p0006 := @g_snex (syn_c0)
  have p0007 := @g_complex (syn_csn (syn_c0)) p0006
  have p0008 :=
    @g_eqeltri (.cab n (syn_wne (.cv n) (syn_c0))) (syn_ccompl (syn_csn (syn_c0)))
      (syn_cvv) p0005 p0007
  have p0009 := @g_neeq1 (.cv n) (syn_c0c) (syn_c0)
  have p0010 := @g_neeq1 (.cv n) (.cv m) (syn_c0)
  have p0011 := @g_neeq1 (.cv n) (syn_cplc (.cv m) (syn_c1c)) (syn_c0)
  have p0012 := @g_neeq1 (.cv n) (.cv x) (syn_c0)
  have p0013 := @g_nulel0c
  have p0014 := @g_ne0i (syn_c0c) (syn_c0)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @g_n0 a (.cv m) dv_cache_0002
  have p0017 := @g_vinf
  have p0018 := @g_elunii (syn_cvv) (.cv m) (syn_cnnc)
  have p0019 :=
    @g_ancoms (.classMem (syn_cvv) (.cv m)) (.classMem (.cv m) (syn_cnnc))
      (.classMem (syn_cvv) (syn_cuni (syn_cnnc))) p0018
  have p0020 := (Nominal.classEqRefl (syn_cfin))
  have p0021 :=
    @g_syl6eleqr (syn_wa (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cvv) (.cv m)))
      (syn_cvv) (syn_cuni (syn_cnnc)) (syn_cfin) p0019 p0020
  have p0022 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cvv) (.cv m))
      (.classMem (syn_cvv) (syn_cfin)) p0021
  have p0023 :=
    @g_mtoi (.classMem (.cv m) (syn_cnnc)) (.classMem (syn_cvv) (.cv m))
      (.classMem (syn_cvv) (syn_cfin)) p0017 p0022
  have p0024 := @g_eleq1 (.cv a) (syn_cvv) (.cv m)
  have p0025_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (syn_cvv))
        (syn_wb (.objMem a m) (.classMem (syn_cvv) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cvv syn_wb
        simp (config := { failIfUnchanged := false }) only []
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
      p0024
  have p0025 :=
    @g_notbid (.classEq (.cv a) (syn_cvv)) (.objMem a m) (.classMem (syn_cvv) (.cv m))
      p0025_e00_recanon
  have p0026 :=
    @g_syl5ibrcom (.classMem (.cv m) (syn_cnnc)) (.neg (.objMem a m))
      (.classEq (.cv a) (syn_cvv)) (.neg (.classMem (syn_cvv) (.cv m))) p0023 p0025
  have p0027 :=
    @g_necon2ad (.classMem (.cv m) (syn_cnnc)) (.objMem a m) (.cv a) (syn_cvv) p0026
  have p0028 :=
    @g_imp (.classMem (.cv m) (syn_cnnc)) (.objMem a m) (syn_wne (.cv a) (syn_cvv)) p0027
  have p0029 := @g_compleqb (.cv a) (syn_cvv)
  have p0030 :=
    @g_necon3bii (.cv a) (syn_cvv) (syn_ccompl (.cv a)) (syn_ccompl (syn_cvv)) p0029
  have p0031 :=
    @g_sylib (syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m))
      (syn_wne (.cv a) (syn_cvv)) (syn_wne (syn_ccompl (.cv a)) (syn_ccompl (syn_cvv)))
      p0028 p0030
  have p0032 := @g_complV
  have p0033 := @g_neeq2i (syn_ccompl (syn_cvv)) (syn_c0) (syn_ccompl (.cv a)) p0032
  have p0034 :=
    @g_sylib (syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m))
      (syn_wne (syn_ccompl (.cv a)) (syn_ccompl (syn_cvv)))
      (syn_wne (syn_ccompl (.cv a)) (syn_c0)) p0031 p0033
  have p0035 := @g_n0 x (syn_ccompl (.cv a)) dv_cache_0003
  have p0036 := @g_vex x
  have p0037 := @g_elcompl (.cv x) (.cv a) p0036
  have p0038 := @g_elsuci (.cv a) (.cv m) (.cv x) p0036
  have p0039 := @g_ne0i (syn_cplc (.cv m) (syn_c1c)) (syn_cun (.cv a) (syn_csn (.cv x)))
  have p0040_e00_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.objMem a m) (.neg (.objMem x a)))
        (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cun syn_cnin syn_wnan syn_ccompl syn_csn syn_cplc syn_wrex
          syn_wex syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0038
  have p0040 :=
    @g_syl (syn_wa (.objMem a m) (.neg (.objMem x a)))
      (.classMem (syn_cun (.cv a) (syn_csn (.cv x))) (syn_cplc (.cv m) (syn_c1c)))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0040_e00_recanon p0039
  have p0041_e00_recanon :
    Nominal.NPrf (syn_wb (.classMem (.cv x) (syn_ccompl (.cv a))) (.neg (.objMem x a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_ccompl syn_cnin syn_wnan syn_wa
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0037
  have p0041 :=
    @g_sylan2b (.classMem (.cv x) (syn_ccompl (.cv a))) (.objMem a m) (.neg (.objMem x a))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0041_e00_recanon p0040
  have p0042 :=
    @g_ex (.objMem a m) (.classMem (.cv x) (syn_ccompl (.cv a)))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0041
  have p0043 :=
    @g_adantl (.objMem a m)
      (.imp (.classMem (.cv x) (syn_ccompl (.cv a)))
        (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)))
      (.classMem (.cv m) (syn_cnnc)) p0042
  have p0044 :=
    @g_exlimdv (syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m))
      (.classMem (.cv x) (syn_ccompl (.cv a)))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) x dv_cache_0004 dv_cache_0005 p0043
  have p0045 :=
    @g_syl5bi (syn_wne (syn_ccompl (.cv a)) (syn_c0))
      (syn_wex x (.classMem (.cv x) (syn_ccompl (.cv a))))
      (syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0035 p0044
  have p0046 :=
    @g_mpd (syn_wa (.classMem (.cv m) (syn_cnnc)) (.objMem a m))
      (syn_wne (syn_ccompl (.cv a)) (syn_c0))
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0034 p0045
  have p0047 :=
    @g_ex (.classMem (.cv m) (syn_cnnc)) (.objMem a m)
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) p0046
  have p0048 :=
    @g_exlimdv (.classMem (.cv m) (syn_cnnc)) (.objMem a m)
      (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0)) a dv_cache_0006 dv_cache_0007 p0047
  have p0049_e00_recanon :
    Nominal.NPrf (syn_wb (syn_wne (.cv m) (syn_c0)) (syn_wex a (.objMem a m))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cvv syn_wex
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.neg
            exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0016
  have p0049 :=
    @g_syl5bi (syn_wne (.cv m) (syn_c0)) (syn_wex a (.objMem a m))
      (.classMem (.cv m) (syn_cnnc)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      p0049_e00_recanon p0048
  have p0050_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (syn_wb (syn_wne (.cv n) (syn_c0)) (syn_wne (.cv m) (syn_c0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wne syn_c0 syn_cdif syn_cin syn_ccompl syn_cnin syn_wnan syn_wa
          syn_cvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0050 :=
    @g_finds (syn_wne (.cv n) (syn_c0)) (syn_wne (syn_c0c) (syn_c0))
      (syn_wne (.cv m) (syn_c0)) (syn_wne (syn_cplc (.cv m) (syn_c1c)) (syn_c0))
      (syn_wne (.cv x) (syn_c0)) n m (.cv x) dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0008 p0009
      p0050_e02_recanon p0011 p0012 p0015 p0049
  have p0051 := @g_neneqd (.classMem (.cv x) (syn_cnnc)) (.cv x) (syn_c0) p0050
  have p0052 := @g_nrex (.classEq (.cv x) (syn_c0)) x (syn_cnnc) p0051
  have p0053 := @g_risset x (syn_c0) (syn_cnnc) dv_cache_0015 dv_cache_0016
  have p0054 :=
    @g_mtbir (.classMem (syn_c0) (syn_cnnc))
      (syn_wrex x (syn_cnnc) (.classEq (.cv x) (syn_c0))) p0052 p0053
  exact p0054

@[expose]
noncomputable def g_peano4 (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
          (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))) (.classEq M N)) :=
  by
  have p0000 :=
    @g_n_3simpa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))
  have p0001 :=
    @g_simp3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))
  have p0002 := @g_peano2 M
  have p0003 := @g_nulnnn
  have p0004 := @g_eleq1 (syn_cplc M (syn_c1c)) (syn_c0) (syn_cnnc)
  have p0005 :=
    @g_mtbiri (.classEq (syn_cplc M (syn_c1c)) (syn_c0))
      (.classMem (syn_cplc M (syn_c1c)) (syn_cnnc)) (.classMem (syn_c0) (syn_cnnc)) p0003
      p0004
  have p0006 :=
    @g_necon2ai (.classMem (syn_cplc M (syn_c1c)) (syn_cnnc)) (syn_cplc M (syn_c1c))
      (syn_c0) p0005
  have p0007 :=
    @g_syl (.classMem M (syn_cnnc)) (.classMem (syn_cplc M (syn_c1c)) (syn_cnnc))
      (syn_wne (syn_cplc M (syn_c1c)) (syn_c0)) p0002 p0006
  have p0008 :=
    @g_n_3ad2ant1 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wne (syn_cplc M (syn_c1c)) (syn_c0))
      (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) p0007
  have p0009 := @g_prepeano4 M N
  have p0010 :=
    @g_syl12anc
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
        (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))))
      (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c)))
      (syn_wne (syn_cplc M (syn_c1c)) (syn_c0)) (.classEq M N) p0000 p0001 p0008 p0009
  exact p0010

@[expose]
noncomputable def g_suc11nnc (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
        (syn_wb (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (.classEq M N))) :=
  by
  have p0000 := @g_peano4 M N
  have p0001 :=
    @g_n_3expia (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (.classEq M N) p0000
  have p0002 := @g_addceq1 M N (syn_c1c)
  have p0003 :=
    @g_impbid1 (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classEq (syn_cplc M (syn_c1c)) (syn_cplc N (syn_c1c))) (.classEq M N) p0001 p0002
  exact p0003

@[expose]
noncomputable def g_addccan2 (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wb (.classEq (syn_cplc M N) (syn_cplc M P)) (.classEq N P))) :=
  by
  have p0000 := @g_nncaddccl M N
  have p0001 := @g_nulnnn
  have p0002 := @g_eleq1 (syn_cplc M N) (syn_c0) (syn_cnnc)
  have p0003 :=
    @g_mtbiri (.classEq (syn_cplc M N) (syn_c0)) (.classMem (syn_cplc M N) (syn_cnnc))
      (.classMem (syn_c0) (syn_cnnc)) p0001 p0002
  have p0004 :=
    @g_necon2ai (.classMem (syn_cplc M N) (syn_cnnc)) (syn_cplc M N) (syn_c0) p0003
  have p0005 :=
    @g_syl (syn_wa (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)))
      (.classMem (syn_cplc M N) (syn_cnnc)) (syn_wne (syn_cplc M N) (syn_c0)) p0000 p0004
  have p0006 :=
    @g_n_3adant3 (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wne (syn_cplc M N) (syn_c0)) (.classMem P (syn_cnnc)) p0005
  have p0007 := @g_preaddccan2 P M N
  have p0008 :=
    @g_mpdan
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))
      (syn_wne (syn_cplc M N) (syn_c0))
      (syn_wb (.classEq (syn_cplc M N) (syn_cplc M P)) (.classEq N P)) p0006 p0007
  exact p0008

@[expose]
noncomputable def g_addccan1 (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))
        (syn_wb (.classEq (syn_cplc M P) (syn_cplc N P)) (.classEq M N))) :=
  by
  have p0000 := @g_addccom M P
  have p0001 := @g_addccom N P
  have p0002 :=
    @g_eqeq12i (syn_cplc M P) (syn_cplc P M) (syn_cplc N P) (syn_cplc P N) p0000 p0001
  have p0003 := @g_addccan2 N P M
  have p0004 :=
    @g_n_3coml (.classMem P (syn_cnnc)) (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc))
      (syn_wb (.classEq (syn_cplc P M) (syn_cplc P N)) (.classEq M N)) p0003
  have p0005 :=
    @g_syl5bb (.classEq (syn_cplc M P) (syn_cplc N P))
      (.classEq (syn_cplc P M) (syn_cplc P N))
      (syn_w3a (.classMem M (syn_cnnc)) (.classMem N (syn_cnnc)) (.classMem P (syn_cnnc)))
      (.classEq M N) p0002 p0004
  exact p0005


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part028`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_dfphi2 (A : Class) :
    Nominal.NPrf
      (.classEq (syn_cphi A) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                    (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
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
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (h)
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
  have dv_cache_0001 : y ∉ ((Wff.objEq z x)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_ne_x, or_false, not_false_eq_true])
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
  have dv_cache_0003 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0004 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0005 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0006 :
    z ∉
      ((syn_wrex y A (.classEq (.cv x)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c))
              (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x,
          fresh_z_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((syn_cphi A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, fresh_x_not_A,
          not_false_eq_true])
  have dv_cache_0010 :
    x ∉
      ((syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    @g_iftrue (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)
  have p0001 :=
    @g_eqeq2d (.classMem (.cv y) (syn_cnnc))
      (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))
      (syn_cplc (.cv y) (syn_c1c)) (.cv x) p0000
  have p0002 :=
    @g_iba (.classMem (.cv y) (syn_cnnc)) (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
  have p0003 := @g_simpr (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))
  have p0004 :=
    @g_con2i (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))
      (.classMem (.cv y) (syn_cnnc)) p0003
  have p0005 :=
    @g_biorf (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
  have p0006 :=
    @g_syl (.classMem (.cv y) (syn_cnnc))
      (.neg (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))))
      (syn_wb (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
          (.classMem (.cv y) (syn_cnnc)))
        (syn_wo (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))
          (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
            (.classMem (.cv y) (syn_cnnc)))))
      p0004 p0005
  have p0007 :=
    @g_orcom (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
  have p0008 :=
    @g_syl6bb (.classMem (.cv y) (syn_cnnc))
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
      (syn_wo (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))
        (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc))))
      (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
          (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))))
      p0006 p0007
  have p0009 :=
    @g_n_3bitrd (.classMem (.cv y) (syn_cnnc))
      (.classEq (.cv x)
        (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
      (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
      (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
          (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))))
      p0001 p0002 p0008
  have p0010 :=
    @g_iffalse (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)
  have p0011 :=
    @g_eqeq2d (.neg (.classMem (.cv y) (syn_cnnc)))
      (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))
      (.cv y) (.cv x) p0010
  have p0012 := @g_iba (.neg (.classMem (.cv y) (syn_cnnc))) (.objEq x y)
  have p0013 :=
    @g_simpr (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
      (.classMem (.cv y) (syn_cnnc))
  have p0014 :=
    @g_con3i
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (.cv y) (syn_cnnc)) p0013
  have p0015 :=
    @g_biorf
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
      (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))
  have p0016 :=
    @g_syl (.neg (.classMem (.cv y) (syn_cnnc)))
      (.neg (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
          (.classMem (.cv y) (syn_cnnc))))
      (syn_wb (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))) (syn_wo
          (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
            (.classMem (.cv y) (syn_cnnc)))
          (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))))
      p0014 p0015
  have p0017_e00_recanon :
    Nominal.NPrf
      (.imp (.neg (.classMem (.cv y) (syn_cnnc))) (syn_wb (.classEq (.cv x)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
          (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cnnc syn_cint syn_wa syn_c0c syn_csn syn_c0 syn_cdif syn_cin syn_ccompl
          syn_cnin syn_wnan syn_cvv syn_wral syn_cplc syn_wrex syn_wex syn_c1c syn_wb
          syn_cif syn_wo
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0017 :=
    @g_n_3bitrd (.neg (.classMem (.cv y) (syn_cnnc)))
      (.classEq (.cv x)
        (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
      (.objEq x y) (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))
      (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
          (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))))
      p0017_e00_recanon p0012 p0016
  have p0018 :=
    @g_pm2_61i (.classMem (.cv y) (syn_cnnc))
      (syn_wb (.classEq (.cv x)
          (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))) (syn_wo
          (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
            (.classMem (.cv y) (syn_cnnc)))
          (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))))
      p0009 p0017
  have p0019 := @g_equcom y x
  have p0020 := @g_vex y
  have p0021 := @g_elcompl (.cv y) (syn_cnnc) p0020
  have p0022 :=
    @g_anbi12i (.objEq y x) (.objEq x y) (.classMem (.cv y) (syn_ccompl (syn_cnnc)))
      (.neg (.classMem (.cv y) (syn_cnnc))) p0019 p0021
  have p0023 :=
    @g_orbi2i (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc))))
      (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc))))
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
      p0022
  have p0024 :=
    @g_bitr4i
      (.classEq (.cv x)
        (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
      (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
          (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (.objEq x y) (.neg (.classMem (.cv y) (syn_cnnc)))))
      (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
          (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc)))))
      p0018 p0023
  have p0025 :=
    @g_elun (syn_copk (.cv y) (.cv x))
      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))
  have p0026 :=
    @g_elin (syn_copk (.cv y) (.cv x))
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cxpk (syn_cnnc) (syn_cvv))
  have p0027 := @g_vex x
  have p0028 :=
    @g_opkelimagek (.cv y) (.cv x)
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0020 p0027
  have p0029 := @g_dfaddc2 (.cv y) (syn_c1c)
  have p0030 :=
    @g_eqeq2i (syn_cplc (.cv y) (syn_c1c))
      (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv y))
      (.cv x) p0029
  have p0031 :=
    @g_bitr4i
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv x) (syn_cimak (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.cv y)))
      (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) p0028 p0030
  have p0032 := @g_opkelxpk (.cv y) (.cv x) (syn_cnnc) (syn_cvv) p0020 p0027
  have p0033 :=
    @g_mpbiran2 (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_cnnc) (syn_cvv)))
      (.classMem (.cv y) (syn_cnnc)) (.classMem (.cv x) (syn_cvv)) p0027 p0032
  have p0034 :=
    @g_anbi12i
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_cnnc) (syn_cvv)))
      (.classMem (.cv y) (syn_cnnc)) p0031 p0033
  have p0035 :=
    @g_bitri
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))))
      (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_cnnc) (syn_cvv))))
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
      p0026 p0034
  have p0036 :=
    @g_elin (syn_copk (.cv y) (.cv x)) (syn_cidk)
      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))
  have p0037 := @g_opkelidkg (.cv y) (.cv x) (syn_cvv) (syn_cvv)
  have p0038_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)))
        (syn_wb (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.objEq y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wa syn_cvv syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_ccompl
          syn_csn syn_cidk syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0037
  have p0038 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.objEq y x)) p0020 p0027
      p0038_e02_recanon
  have p0039 := @g_opkelxpk (.cv y) (.cv x) (syn_ccompl (syn_cnnc)) (syn_cvv) p0020 p0027
  have p0040 :=
    @g_mpbiran2
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))
      (.classMem (.cv y) (syn_ccompl (syn_cnnc))) (.classMem (.cv x) (syn_cvv)) p0027
      p0039
  have p0041 :=
    @g_anbi12i (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.objEq y x)
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))
      (.classMem (.cv y) (syn_ccompl (syn_cnnc))) p0038 p0040
  have p0042 :=
    @g_bitri
      (.classMem (syn_copk (.cv y) (.cv x))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
      (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk))
        (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
      (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc)))) p0036 p0041
  have p0043 :=
    @g_orbi12i
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))))
      (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c))) (.classMem (.cv y) (syn_cnnc)))
      (.classMem (syn_copk (.cv y) (.cv x))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
      (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc)))) p0035 p0042
  have p0044 :=
    @g_bitri
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                  (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))
      (syn_wo (.classMem (syn_copk (.cv y) (.cv x)) (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                  (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))))
        (.classMem (syn_copk (.cv y) (.cv x))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))
      (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
          (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc)))))
      p0025 p0043
  have p0045 :=
    @g_bitr4i
      (.classEq (.cv x)
        (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
      (syn_wo (syn_wa (.classEq (.cv x) (syn_cplc (.cv y) (syn_c1c)))
          (.classMem (.cv y) (syn_cnnc)))
        (syn_wa (.objEq y x) (.classMem (.cv y) (syn_ccompl (syn_cnnc)))))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                  (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))
      p0024 p0044
  have p0046 :=
    @g_rexbii
      (.classEq (.cv x)
        (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                  (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))
      y A p0045
  have p0047 :=
    @g_eqeq1 (.cv z) (.cv x)
      (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))
  have p0048_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z x) (syn_wb (.classEq (.cv z)
            (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
          (.classEq (.cv x) (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c))
              (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cif syn_wo syn_wa syn_cnnc syn_cint syn_cplc syn_wrex syn_wex
          syn_c1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0047
  have p0048 :=
    @g_rexbidv (.objEq z x)
      (.classEq (.cv z)
        (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
      (.classEq (.cv x)
        (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y)))
      y A dv_cache_0001 p0048_e00_recanon
  have p0049 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_phi y z A
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0050_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv x)) (syn_wb (syn_wrex y A (.classEq (.cv z)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
          (syn_wrex y A (.classEq (.cv x)
              (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c))
                (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_cif, syn_wo, syn_cnnc, syn_cint,
          syn_cplc, syn_c1c]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0048
  have p0050 :=
    @g_elab2
      (syn_wrex y A (.classEq (.cv z)
          (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
      (syn_wrex y A (.classEq (.cv x)
          (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
      z (.cv x) (syn_cphi A) dv_cache_0005 dv_cache_0006 p0027 p0050_e01_recanon p0049
  have p0051 :=
    @g_elimak y
      (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
      A (.cv x) dv_cache_0007 dv_cache_0002 dv_cache_0008 p0027
  have p0052 :=
    @g_n_3bitr4i
      (syn_wrex y A (.classEq (.cv x)
          (syn_cif (.classMem (.cv y) (syn_cnnc)) (syn_cplc (.cv y) (syn_c1c)) (.cv y))))
      (syn_wrex y A (.classMem (syn_copk (.cv y) (.cv x)) (syn_cun (syn_cin (syn_cimagek
                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
      (.classMem (.cv x) (syn_cphi A))
      (.classMem (.cv x) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                    (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A))
      p0046 p0050 p0051
  have p0053 :=
    @g_eqriv x (syn_cphi A)
      (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A)
      dv_cache_0009 dv_cache_0010 p0052
  exact p0053

@[expose]
noncomputable def g_phieq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (syn_cphi A) (syn_cphi B))) :=
  by
  have p0000 :=
    @g_imakeq2 A B
      (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
  have p0001 := @g_dfphi2 A
  have p0002 := @g_dfphi2 B
  have p0003 :=
    @g_n_3eqtr4g (.classEq A B)
      (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A)
      (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) B)
      (syn_cphi A) (syn_cphi B) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_phiexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (syn_cphi A) (syn_cvv))) :=
  by
  have p0000 := @g_dfphi2 A
  have p0001 := @g_addcexlem
  have p0002 := @g_n_1cex
  have p0003 := @g_pw1ex (syn_c1c) p0002
  have p0004 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0003
  have p0005 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0001 p0004
  have p0006 :=
    @g_imagekex
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0005
  have p0007 := @g_nncex
  have p0008 := @g_vvex
  have p0009 := @g_xpkex (syn_cnnc) (syn_cvv) p0007 p0008
  have p0010 :=
    @g_inex
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cxpk (syn_cnnc) (syn_cvv)) p0006 p0009
  have p0011 := @g_idkex
  have p0013 := @g_complex (syn_cnnc) p0007
  have p0015 := @g_xpkex (syn_ccompl (syn_cnnc)) (syn_cvv) p0013 p0008
  have p0016 :=
    @g_inex (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)) p0011 p0015
  have p0017 :=
    @g_unex
      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))) p0010 p0016
  have p0018 :=
    @g_imakexg
      (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
      A (syn_cvv) V
  have p0019 :=
    @g_mpan
      (.classMem (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (syn_cvv))
      (.classMem A V)
      (.classMem (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A) (syn_cvv))
      p0017 p0018
  have p0020 :=
    @g_syl5eqel (.classMem A V) (syn_cphi A)
      (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) A)
      (syn_cvv) p0000 p0019
  exact p0020

@[expose]
noncomputable def g_phiex (A : Class)
    (hyp_phiex_1 : Nominal.NPrf (.classMem A (syn_cvv))) :
    Nominal.NPrf (.classMem (syn_cphi A) (syn_cvv)) :=
  by
  have p0000 := @g_phiexg A (syn_cvv)
  have p0001 := Nominal.mp hyp_phiex_1 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part029`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_dfop2lem1 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                        (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                    (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classEq (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var)
  let z : Var := freshVar proofSupport 0
  let t : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_t_ne_y : t ≠ y := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have dv_cache_0001 :
    t ∉
      ((syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                  (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_copk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0005 :
    z ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                    (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                  (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_x, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv z))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
          not_false_eq_true])
  have dv_cache_0007 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                    (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                  (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_x, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((syn_csn (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_z,
          not_false_eq_true])
  have dv_cache_0009 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0010 :
    y ∉
      ((syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                        (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : y ∉ ((syn_cssetk)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((syn_cphi (.cv x))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0014 : z ∉ ((Class.cv y)).fv :=
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
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0015 : z ∉ ((syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 := @g_opkex (.cv x) (.cv y)
  have p0001 :=
    @g_elimak t
      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                              (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
              (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv x) (.cv y)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0000
  have p0002 := @g_elpw121c z (.cv t) dv_cache_0004
  have p0003 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                  (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))
      p0002
  have p0004 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                  (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))
      z dv_cache_0005
  have p0005 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                    (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                  (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))))
      (syn_wa (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                    (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                  (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                  (syn_cins3k (syn_ccompl (syn_cimak
                                        (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))))
      p0003 p0004
  have p0006 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                    (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                  (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                  (syn_cins3k (syn_ccompl (syn_cimak
                                        (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))))
      t p0005
  have p0007 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                    (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                  (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))))
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                    (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                  (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))))
      z t
  have p0009 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                  (syn_cins3k (syn_ccompl (syn_cimak
                                        (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))))
      (syn_wex t (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                        (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                    (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                    (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                  (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                        (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                    (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))))))
      p0006 p0007 p0008
  have p0010 := @g_snex (syn_csn (syn_csn (.cv z)))
  have p0011 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y))
  have p0012 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
      (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                              (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
              (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
      p0011
  have p0013 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                  (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                  (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))
      t (syn_csn (syn_csn (syn_csn (.cv z)))) dv_cache_0006 dv_cache_0007 p0010 p0012
  have p0014 :=
    @g_elsymdif
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
      (syn_cins2k (syn_cssetk))
      (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))
  have p0015 := @g_snex (.cv z)
  have p0016 := @g_vex x
  have p0017 := @g_vex y
  have p0018 :=
    @g_otkelins2k (syn_csn (.cv z)) (.cv x) (.cv y) (syn_cssetk) p0015 p0016 p0017
  have p0019 := @g_vex z
  have p0020 := @g_elssetk (.cv z) (.cv y) p0019 p0017
  have p0021_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
      p0020
  have p0021 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
        (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)) (.objMem z y) p0018
      p0021_e01_recanon
  have p0022 :=
    @g_otkelins3k (syn_csn (.cv z)) (.cv x) (.cv y)
      (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
          (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))
      p0015 p0016 p0017
  have p0023 :=
    @g_elun (syn_copk (syn_csn (.cv z)) (.cv x))
      (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                      (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))
  have p0024 :=
    @g_ancom (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
  have p0025 :=
    @g_opkelimagek (.cv x) (.cv y)
      (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
      p0016 p0017
  have p0026 :=
    @g_opkelcnvk (.cv y) (.cv x)
      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))
      p0017 p0016
  have p0027 := @g_dfphi2 (.cv x)
  have p0028 :=
    @g_eqeq2i (syn_cphi (.cv x))
      (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (.cv x))
      (.cv y) p0027
  have p0029 :=
    @g_n_3bitr4i
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
      (.classEq (.cv y) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                    (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (.cv x)))
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      (.classEq (.cv y) (syn_cphi (.cv x))) p0025 p0026 p0028
  have p0030_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_copk syn_cpr syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_csn
          syn_cssetk syn_wex
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
      p0020
  have p0030 :=
    @g_anbi12i
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      (.classEq (.cv y) (syn_cphi (.cv x)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)) (.objMem z y) p0029
      p0030_e01_recanon
  have p0031 :=
    @g_bitri
      (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk))
        (.classMem (syn_copk (.cv y) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
        (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk)))
      (syn_wa (.classEq (.cv y) (syn_cphi (.cv x))) (.objMem z y)) p0024 p0030
  have p0032 :=
    @g_exbii
      (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk))
        (.classMem (syn_copk (.cv y) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      (syn_wa (.classEq (.cv y) (syn_cphi (.cv x))) (.objMem z y)) y p0031
  have p0033 :=
    @g_opkelcok y (syn_csn (.cv z)) (.cv x)
      (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                      (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
      (syn_cssetk) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0015 p0016
  have p0034 := @g_phiex (.cv x) p0016
  have p0035 := @g_clel3 y (.cv z) (syn_cphi (.cv x)) dv_cache_0012 dv_cache_0013 p0034
  have p0036_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv z) (syn_cphi (.cv x)))
        (syn_wex y (syn_wa (.classEq (.cv y) (syn_cphi (.cv x))) (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cphi syn_wrex syn_wex syn_wa syn_cif syn_wo syn_cnnc syn_cint
          syn_cplc syn_c1c
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0035
  have p0036 :=
    @g_n_3bitr4i
      (syn_wex y (syn_wa (.classMem (syn_copk (syn_csn (.cv z)) (.cv y)) (syn_cssetk))
          (.classMem (syn_copk (.cv y) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_cphi (.cv x))) (.objMem z y)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv x)) (syn_ccomk (syn_ccnvk (syn_cimagek
              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
          (syn_cssetk)))
      (.classMem (.cv z) (syn_cphi (.cv x))) p0032 p0033 p0036_e02_recanon
  have p0037 :=
    @g_opkelxpk (syn_csn (.cv z)) (.cv x) (syn_csn (syn_csn (syn_c0c))) (syn_cvv) p0015
      p0016
  have p0038 :=
    @g_mpbiran2
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv x))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))
      (.classMem (syn_csn (.cv z)) (syn_csn (syn_csn (syn_c0c))))
      (.classMem (.cv x) (syn_cvv)) p0016 p0037
  have p0039 := @g_sneqb (.cv z) (syn_c0c) p0019
  have p0040 := @g_elsnc (syn_csn (.cv z)) (syn_csn (syn_c0c)) p0015
  have p0041 := @g_elsnc (.cv z) (syn_c0c) p0019
  have p0042 :=
    @g_n_3bitr4ri (.classEq (syn_csn (.cv z)) (syn_csn (syn_c0c)))
      (.classEq (.cv z) (syn_c0c))
      (.classMem (syn_csn (.cv z)) (syn_csn (syn_csn (syn_c0c))))
      (.classMem (.cv z) (syn_csn (syn_c0c))) p0039 p0040 p0041
  have p0043 :=
    @g_bitr4i
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv x))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))
      (.classMem (syn_csn (.cv z)) (syn_csn (syn_csn (syn_c0c))))
      (.classMem (.cv z) (syn_csn (syn_c0c))) p0038 p0042
  have p0044 :=
    @g_orbi12i
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv x)) (syn_ccomk (syn_ccnvk (syn_cimagek
              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
          (syn_cssetk)))
      (.classMem (.cv z) (syn_cphi (.cv x)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv x))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))
      (.classMem (.cv z) (syn_csn (syn_c0c))) p0036 p0043
  have p0045 := @g_elun (.cv z) (syn_cphi (.cv x)) (syn_csn (syn_c0c))
  have p0046 :=
    @g_bitr4i
      (syn_wo (.classMem (syn_copk (syn_csn (.cv z)) (.cv x)) (syn_ccomk (syn_ccnvk (syn_cimagek
                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
            (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv z)) (.cv x))
          (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))
      (syn_wo (.classMem (.cv z) (syn_cphi (.cv x))) (.classMem (.cv z) (syn_csn (syn_c0c))))
      (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0044 p0045
  have p0047 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
              (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv x)) (syn_cun (syn_ccomk (syn_ccnvk
              (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                            (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))
      (syn_wo (.classMem (syn_copk (syn_csn (.cv z)) (.cv x)) (syn_ccomk (syn_ccnvk (syn_cimagek
                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
            (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv z)) (.cv x))
          (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))
      (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0022 p0023
      p0046
  have p0048 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
        (syn_cins2k (syn_cssetk)))
      (.objMem z y)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
              (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
      (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0021 p0047
  have p0049 :=
    @g_notbii
      (syn_wb (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
          (syn_cins2k (syn_cssetk))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
          (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                          (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                    (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))
      (syn_wb (.objMem z y)
        (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))
      p0048
  have p0050 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                  (syn_cins3k (syn_ccompl (syn_cimak
                                        (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                  (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))
      (.neg (syn_wb (.classMem
            (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
            (syn_cins2k (syn_cssetk))) (.classMem
            (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (.cv x) (.cv y)))
            (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                          (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                      (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))))
      (.neg (syn_wb (.objMem z y)
          (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      p0013 p0014 p0049
  have p0051 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                  (syn_cins3k (syn_ccompl (syn_cimak
                                        (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))))))
      (.neg (syn_wb (.objMem z y)
          (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      z p0050
  have p0052 :=
    @g_n_3bitri
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                          (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                      (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                    (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                  (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                        (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                    (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))))))
      (syn_wex z (.neg (syn_wb (.objMem z y)
            (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))))
      p0001 p0009 p0051
  have p0053 :=
    @g_notbii
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                          (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                      (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                  (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex z (.neg (syn_wb (.objMem z y)
            (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))))
      p0052
  have p0054 :=
    @g_elcompl (syn_copk (.cv x) (.cv y))
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                              (syn_cins3k (syn_ccompl (syn_cimak
                                    (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0000
  have p0055 :=
    @g_dfcleq z (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))) dv_cache_0014
      dv_cache_0015
  have p0056 :=
    @g_alex
      (syn_wb (.objMem z y)
        (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))
      z
  have p0057_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) (.all z
          (syn_wb (.objMem z y)
            (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cun syn_cnin syn_wnan syn_wa syn_ccompl syn_cphi syn_wrex
          syn_wex syn_cif syn_wo syn_cnnc syn_cint syn_cplc syn_c1c syn_csn syn_c0c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
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
      p0055
  have p0057 :=
    @g_bitri (.classEq (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
      (.all z (syn_wb (.objMem z y)
          (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      (.neg (syn_wex z (.neg (syn_wb (.objMem z y)
              (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))))
      p0057_e00_recanon p0056
  have p0058 :=
    @g_n_3bitr4i
      (.neg (.classMem (syn_copk (.cv x) (.cv y)) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                  (syn_cins3k (syn_ccompl (syn_cimak
                                        (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.neg (syn_wex z (.neg (syn_wb (.objMem z y)
              (.classMem (.cv z) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))))
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
                      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                  (syn_cins3k (syn_ccompl (syn_cimak
                                        (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                  (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0053 p0054
      p0057
  exact p0058


end NFChoice.DirectNominalPrf.WPPReplay

end
