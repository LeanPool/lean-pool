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

/-- Checked nominal proof certificate identified upstream as `g_vfinncsp`. -/
@[expose]
noncomputable def gVfinncsp :
    Nominal.NPrf
      (.imp (.classMem (synCvv) (synCfin)) (.classEq (synCncfin (synCspfin))
          (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c)))) :=
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
  have dv_cache_0003 : t ∉ ((synCpw1 (synCspfin))).fv :=
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
  have dv_cache_0006 : x ∉ ((synCspfin)).fv :=
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
  have dv_cache_0008 : t ∉ ((synCspfin)).fv :=
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
  have dv_cache_0010 : t ∉ ((synCsn (.cv x))).fv :=
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
  have dv_cache_0013 : a ∉ ((synCspfin)).fv :=
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
  have dv_cache_0014 : a ∉ ((synCncfin (synCspfin))).fv :=
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
  have dv_cache_0015 : x ∉ ((synCncfin (synCspfin))).fv :=
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
  have p0000 := @gVfinspeqtncv x a dv_cache_0001
  have p0001 :=
    @gNcfineq (synCspfin)
      (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCsn (synCncfin (synCvv))))
  have p0002 :=
    @gSyl (.classMem (synCvv) (synCfin))
      (.classEq (synCspfin)
        (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))))
      (.classEq (synCncfin (synCspfin)) (synCncfin (synCun
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCncfin (synCvv))))))
      p0000 p0001
  have p0003 := @gVfinncvntsp x a dv_cache_0001
  have p0004 :=
    @gDisjsn (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCncfin (synCvv))
  have p0005 :=
    @gSylibr (.classMem (synCvv) (synCfin))
      (.neg (.classMem (synCncfin (synCvv))
          (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))))
      (.classEq
        (synCin (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))) (synC0))
      p0003 p0004
  have p0006 := @gVex a
  have p0007 :=
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
      (synCpw1 (synCspfin)) (.cv a) dv_cache_0002 dv_cache_0003 dv_cache_0004 p0006
  have p0008 :=
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
  have p0009 := @gElpw1 x (.cv t) (synCspfin) dv_cache_0005 dv_cache_0006
  have p0010 :=
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
      p0009
  have p0011 :=
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
      x (synCspfin) dv_cache_0007
  have p0012 :=
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
      p0010 p0011
  have p0013 :=
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
      t p0012
  have p0014 :=
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
      x t (synCspfin) dv_cache_0008 dv_cache_0009
  have p0015 :=
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
      p0013 p0014
  have p0016 :=
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
      p0008 p0015
  have p0017 :=
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
      p0007 p0016
  have p0018 := @gSnex (.cv x)
  have p0019 := @gOpkeq1 (.cv t) (synCsn (.cv x)) (.cv a)
  have p0020 :=
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
      p0019
  have p0021 :=
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
      t (synCsn (.cv x)) dv_cache_0010 dv_cache_0011 p0018 p0020
  have p0022 := @gVex x
  have p0023 := @gEqtfinrelk (.cv x) (.cv a) p0022 p0006
  have p0024 :=
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
      (.classEq (.cv a) (synCtfin (.cv x))) p0021 p0023
  have p0025 :=
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
      (.classEq (.cv a) (synCtfin (.cv x))) x (synCspfin) p0024
  have p0026 :=
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
      (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))) p0017 p0025
  have p0027 :=
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
      dv_cache_0012 p0026
  have p0028 := @gTfinrelkex
  have p0029 := @gSpfinex
  have p0030 := @gPw1ex (synCspfin) p0029
  have p0031 :=
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
      (synCpw1 (synCspfin)) p0028 p0030
  have p0032 :=
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
      p0027 p0031
  have p0033 := @gSnex (synCncfin (synCvv))
  have p0034 :=
    @gNcfindi (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCsn (synCncfin (synCvv))) (synCvv) (synCvv)
  have p0035 :=
    @gMp3an2
      (synWa (.classMem (synCvv) (synCfin)) (.classMem
          (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))) (synCvv)))
      (.classMem (synCsn (synCncfin (synCvv))) (synCvv))
      (.classEq
        (synCin (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))) (synC0))
      (.classEq (synCncfin (synCun
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCncfin (synCvv))))) (synCplc (synCncfin
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
          (synCncfin (synCsn (synCncfin (synCvv))))))
      p0033 p0034
  have p0036 :=
    @gMpanl2 (.classMem (synCvv) (synCfin))
      (.classMem (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCvv))
      (.classEq
        (synCin (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))) (synC0))
      (.classEq (synCncfin (synCun
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCncfin (synCvv))))) (synCplc (synCncfin
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
          (synCncfin (synCsn (synCncfin (synCvv))))))
      p0032 p0035
  have p0037 :=
    @gMpdan (.classMem (synCvv) (synCfin))
      (.classEq
        (synCin (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))) (synC0))
      (.classEq (synCncfin (synCun
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
            (synCsn (synCncfin (synCvv))))) (synCplc (synCncfin
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
          (synCncfin (synCsn (synCncfin (synCvv))))))
      p0005 p0036
  have p0038 :=
    @gNcfinprop (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCvv)
  have p0039 :=
    @gMpan2 (.classMem (synCvv) (synCfin))
      (.classMem (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCvv))
      (synWa (.classMem (synCncfin
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
          (synCnnc)) (.classMem
          (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))) (synCncfin
            (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))))
      p0032 p0038
  have p0040 :=
    @gSimpld (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin
          (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))) (synCnnc))
      (.classMem (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCncfin (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))))
      p0039
  have p0042 := @gNcfinprop (synCspfin) (synCvv)
  have p0043 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCspfin) (synCvv))
      (synWa (.classMem (synCncfin (synCspfin)) (synCnnc))
        (.classMem (synCspfin) (synCncfin (synCspfin))))
      p0029 p0042
  have p0044 :=
    @gSimpld (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCspfin)) (synCnnc))
      (.classMem (synCspfin) (synCncfin (synCspfin))) p0043
  have p0045 := @gTfincl (synCncfin (synCspfin))
  have p0046 :=
    @gSyl (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCspfin)) (synCnnc))
      (.classMem (synCtfin (synCncfin (synCspfin))) (synCnnc)) p0044 p0045
  have p0047 :=
    @gSimprd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin
          (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))) (synCnnc))
      (.classMem (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCncfin (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))))
      p0039
  have p0048 := @gVfinspnn
  have p0049 := @gDifss (synCnnc) (synCsn (synC0))
  have p0050 :=
    @gSyl6ss (.classMem (synCvv) (synCfin)) (synCspfin)
      (synCdif (synCnnc) (synCsn (synC0))) (synCnnc) p0048 p0049
  have p0051 :=
    @gSimprd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCspfin)) (synCnnc))
      (.classMem (synCspfin) (synCncfin (synCspfin))) p0043
  have p0052 :=
    @gTfinnn x (synCspfin) (synCncfin (synCspfin)) a dv_cache_0013 dv_cache_0006
      dv_cache_0014 dv_cache_0015 dv_cache_0001
  have p0053 :=
    @gSyl3anc (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCspfin)) (synCnnc)) (synWss (synCspfin) (synCnnc))
      (.classMem (synCspfin) (synCncfin (synCspfin)))
      (.classMem (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (synCncfin (synCspfin))))
      p0044 p0050 p0051 p0052
  have p0054 :=
    @gNnceleq (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
      (synCncfin (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
      (synCtfin (synCncfin (synCspfin)))
  have p0055 :=
    @gSyl22anc (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin
          (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))) (synCnnc))
      (.classMem (synCtfin (synCncfin (synCspfin))) (synCnnc))
      (.classMem (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCncfin (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))))
      (.classMem (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
        (synCtfin (synCncfin (synCspfin))))
      (.classEq (synCncfin
          (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
        (synCtfin (synCncfin (synCspfin))))
      p0040 p0046 p0047 p0053 p0054
  have p0056 := @gNcfinex (synCvv)
  have p0057 := @gNcfinsn (synCncfin (synCvv)) (synCvv)
  have p0058 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCncfin (synCvv)) (synCvv))
      (.classEq (synCncfin (synCsn (synCncfin (synCvv)))) (synC1c)) p0056 p0057
  have p0059 :=
    @gAddceq12d (.classMem (synCvv) (synCfin))
      (synCncfin (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
      (synCtfin (synCncfin (synCspfin))) (synCncfin (synCsn (synCncfin (synCvv))))
      (synC1c) p0055 p0058
  have p0060 :=
    @gN3eqtrd (.classMem (synCvv) (synCfin)) (synCncfin (synCspfin))
      (synCncfin
        (synCun (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))
          (synCsn (synCncfin (synCvv)))))
      (synCplc (synCncfin
          (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
        (synCncfin (synCsn (synCncfin (synCvv)))))
      (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c)) p0002 p0037 p0059
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

/-- Checked nominal proof certificate identified upstream as `g_vinf`. -/
@[expose]
noncomputable def gVinf : Nominal.NPrf (.neg (.classMem (synCvv) (synCfin))) :=
  by
  have p0000 := @gNoel (synCncfin (synCspfin))
  have p0001 := @gSpfinex
  have p0002 := @gNcfinprop (synCspfin) (synCvv)
  have p0003 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCspfin) (synCvv))
      (synWa (.classMem (synCncfin (synCspfin)) (synCnnc))
        (.classMem (synCspfin) (synCncfin (synCspfin))))
      p0001 p0002
  have p0004 := @gNe0i (synCncfin (synCspfin)) (synCspfin)
  have p0005 :=
    @gAnim2i (.classMem (synCspfin) (synCncfin (synCspfin)))
      (synWne (synCncfin (synCspfin)) (synC0))
      (.classMem (synCncfin (synCspfin)) (synCnnc)) p0004
  have p0006 :=
    @gSyl (.classMem (synCvv) (synCfin))
      (synWa (.classMem (synCncfin (synCspfin)) (synCnnc))
        (.classMem (synCspfin) (synCncfin (synCspfin))))
      (synWa (.classMem (synCncfin (synCspfin)) (synCnnc))
        (synWne (synCncfin (synCspfin)) (synC0)))
      p0003 p0005
  have p0007 := @gEldifsn (synCncfin (synCspfin)) (synCnnc) (synC0)
  have p0008 :=
    @gSylibr (.classMem (synCvv) (synCfin))
      (synWa (.classMem (synCncfin (synCspfin)) (synCnnc))
        (synWne (synCncfin (synCspfin)) (synC0)))
      (.classMem (synCncfin (synCspfin)) (synCdif (synCnnc) (synCsn (synC0)))) p0006
      p0007
  have p0009 := @gEvenoddnnnul
  have p0010 :=
    @gSyl6eleqr (.classMem (synCvv) (synCfin)) (synCncfin (synCspfin))
      (synCdif (synCnnc) (synCsn (synC0))) (synCun (synCevenfin) (synCoddfin))
      p0008 p0009
  have p0011 := @gVfinncsp
  have p0012 :=
    @gAdantr (.classMem (synCvv) (synCfin))
      (.classEq (synCncfin (synCspfin))
        (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c)))
      (.classMem (synCncfin (synCspfin)) (synCevenfin)) p0011
  have p0013 := @gEventfin (synCncfin (synCspfin))
  have p0014 :=
    @gAdantl (.classMem (synCncfin (synCspfin)) (synCevenfin))
      (.classMem (synCtfin (synCncfin (synCspfin))) (synCevenfin))
      (.classMem (synCvv) (synCfin)) p0013
  have p0015 := @gEvennnul (synCncfin (synCspfin))
  have p0016 :=
    @gAdantl (.classMem (synCncfin (synCspfin)) (synCevenfin))
      (synWne (synCncfin (synCspfin)) (synC0)) (.classMem (synCvv) (synCfin)) p0015
  have p0017 :=
    @gEqnetrrd
      (synWa (.classMem (synCvv) (synCfin))
        (.classMem (synCncfin (synCspfin)) (synCevenfin)))
      (synCncfin (synCspfin)) (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c))
      (synC0) p0012 p0016
  have p0018 := @gSucevenodd (synCtfin (synCncfin (synCspfin)))
  have p0019 :=
    @gSyl2anc
      (synWa (.classMem (synCvv) (synCfin))
        (.classMem (synCncfin (synCspfin)) (synCevenfin)))
      (.classMem (synCtfin (synCncfin (synCspfin))) (synCevenfin))
      (synWne (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c)) (synC0))
      (.classMem (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c)) (synCoddfin))
      p0014 p0017 p0018
  have p0020 :=
    @gEqeltrd
      (synWa (.classMem (synCvv) (synCfin))
        (.classMem (synCncfin (synCspfin)) (synCevenfin)))
      (synCncfin (synCspfin)) (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c))
      (synCoddfin) p0012 p0019
  have p0021 :=
    @gEx (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCspfin)) (synCevenfin))
      (.classMem (synCncfin (synCspfin)) (synCoddfin)) p0020
  have p0022 :=
    @gAncld (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCspfin)) (synCevenfin))
      (.classMem (synCncfin (synCspfin)) (synCoddfin)) p0021
  have p0024 :=
    @gAdantr (.classMem (synCvv) (synCfin))
      (.classEq (synCncfin (synCspfin))
        (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c)))
      (.classMem (synCncfin (synCspfin)) (synCoddfin)) p0011
  have p0025 := @gOddtfin (synCncfin (synCspfin))
  have p0026 :=
    @gAdantl (.classMem (synCncfin (synCspfin)) (synCoddfin))
      (.classMem (synCtfin (synCncfin (synCspfin))) (synCoddfin))
      (.classMem (synCvv) (synCfin)) p0025
  have p0027 := @gOddnnul (synCncfin (synCspfin))
  have p0028 :=
    @gAdantl (.classMem (synCncfin (synCspfin)) (synCoddfin))
      (synWne (synCncfin (synCspfin)) (synC0)) (.classMem (synCvv) (synCfin)) p0027
  have p0029 :=
    @gEqnetrrd
      (synWa (.classMem (synCvv) (synCfin))
        (.classMem (synCncfin (synCspfin)) (synCoddfin)))
      (synCncfin (synCspfin)) (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c))
      (synC0) p0024 p0028
  have p0030 := @gSucoddeven (synCtfin (synCncfin (synCspfin)))
  have p0031 :=
    @gSyl2anc
      (synWa (.classMem (synCvv) (synCfin))
        (.classMem (synCncfin (synCspfin)) (synCoddfin)))
      (.classMem (synCtfin (synCncfin (synCspfin))) (synCoddfin))
      (synWne (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c)) (synC0))
      (.classMem (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c)) (synCevenfin))
      p0026 p0029 p0030
  have p0032 :=
    @gEqeltrd
      (synWa (.classMem (synCvv) (synCfin))
        (.classMem (synCncfin (synCspfin)) (synCoddfin)))
      (synCncfin (synCspfin)) (synCplc (synCtfin (synCncfin (synCspfin))) (synC1c))
      (synCevenfin) p0024 p0031
  have p0033 :=
    @gEx (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCspfin)) (synCoddfin))
      (.classMem (synCncfin (synCspfin)) (synCevenfin)) p0032
  have p0034 :=
    @gAncrd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCspfin)) (synCoddfin))
      (.classMem (synCncfin (synCspfin)) (synCevenfin)) p0033
  have p0035 :=
    @gJaod (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCspfin)) (synCevenfin))
      (synWa (.classMem (synCncfin (synCspfin)) (synCevenfin))
        (.classMem (synCncfin (synCspfin)) (synCoddfin)))
      (.classMem (synCncfin (synCspfin)) (synCoddfin)) p0022 p0034
  have p0036 := @gElun (synCncfin (synCspfin)) (synCevenfin) (synCoddfin)
  have p0037 := @gElin (synCncfin (synCspfin)) (synCevenfin) (synCoddfin)
  have p0038 :=
    @gN3imtr4g (.classMem (synCvv) (synCfin))
      (synWo (.classMem (synCncfin (synCspfin)) (synCevenfin))
        (.classMem (synCncfin (synCspfin)) (synCoddfin)))
      (synWa (.classMem (synCncfin (synCspfin)) (synCevenfin))
        (.classMem (synCncfin (synCspfin)) (synCoddfin)))
      (.classMem (synCncfin (synCspfin)) (synCun (synCevenfin) (synCoddfin)))
      (.classMem (synCncfin (synCspfin)) (synCin (synCevenfin) (synCoddfin))) p0035
      p0036 p0037
  have p0039 :=
    @gMpd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCspfin)) (synCun (synCevenfin) (synCoddfin)))
      (.classMem (synCncfin (synCspfin)) (synCin (synCevenfin) (synCoddfin))) p0010
      p0038
  have p0040 := @gEvenodddisj
  have p0041 :=
    @gSyl6eleq (.classMem (synCvv) (synCfin)) (synCncfin (synCspfin))
      (synCin (synCevenfin) (synCoddfin)) (synC0) p0039 p0040
  have p0042 :=
    @gMto (.classMem (synCvv) (synCfin)) (.classMem (synCncfin (synCspfin)) (synC0))
      p0000 p0041
  exact p0042

/-- Checked nominal proof certificate identified upstream as `g_nulnnn`. -/
@[expose]
noncomputable def gNulnnn : Nominal.NPrf (.neg (.classMem (synC0) (synCnnc))) :=
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
  have dv_cache_0001 : n ∉ ((synC0)).fv := by
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
  have dv_cache_0003 : x ∉ ((synCcompl (.cv a))).fv :=
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
  have dv_cache_0004 : x ∉ ((synWne (synCplc (.cv m) (synC1c)) (synC0))).fv :=
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
  have dv_cache_0005 : x ∉ ((synWa (.classMem (.cv m) (synCnnc)) (.objMem a m))).fv :=
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
  have dv_cache_0006 : a ∉ ((synWne (synCplc (.cv m) (synC1c)) (synC0))).fv :=
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
  have dv_cache_0007 : a ∉ ((Wff.classMem (.cv m) (synCnnc))).fv :=
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
  have dv_cache_0009 : n ∉ ((synWne (.cv m) (synC0))).fv :=
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
  have dv_cache_0010 : m ∉ ((synWne (.cv n) (synC0))).fv :=
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
  have dv_cache_0011 : n ∉ ((synWne (synC0c) (synC0))).fv :=
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
  have dv_cache_0012 : n ∉ ((synWne (.cv x) (synC0))).fv :=
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
  have dv_cache_0013 : n ∉ ((synWne (synCplc (.cv m) (synC1c)) (synC0))).fv :=
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
  have dv_cache_0015 : x ∉ ((synC0)).fv :=
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
  have dv_cache_0016 : x ∉ ((synCnnc)).fv :=
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
  have p0000 := @gComplab (.classEq (.cv n) (synC0)) n
  have p0001 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSn n (synC0)
      dv_cache_0001
  have p0002 := @gCompleqi (synCsn (synC0)) (.cab n (.classEq (.cv n) (synC0))) p0001
  have p0003 := (Nominal.biimpRefl (synWne (.cv n) (synC0)))
  have p0004 :=
    @gAbbii (synWne (.cv n) (synC0)) (.neg (.classEq (.cv n) (synC0))) n p0003
  have p0005 :=
    @gN3eqtr4ri (synCcompl (.cab n (.classEq (.cv n) (synC0))))
      (.cab n (.neg (.classEq (.cv n) (synC0)))) (synCcompl (synCsn (synC0)))
      (.cab n (synWne (.cv n) (synC0))) p0000 p0002 p0004
  have p0006 := @gSnex (synC0)
  have p0007 := @gComplex (synCsn (synC0)) p0006
  have p0008 :=
    @gEqeltri (.cab n (synWne (.cv n) (synC0))) (synCcompl (synCsn (synC0)))
      (synCvv) p0005 p0007
  have p0009 := @gNeeq1 (.cv n) (synC0c) (synC0)
  have p0010 := @gNeeq1 (.cv n) (.cv m) (synC0)
  have p0011 := @gNeeq1 (.cv n) (synCplc (.cv m) (synC1c)) (synC0)
  have p0012 := @gNeeq1 (.cv n) (.cv x) (synC0)
  have p0013 := @gNulel0c
  have p0014 := @gNe0i (synC0c) (synC0)
  have p0015 := Nominal.mp p0013 p0014
  have p0016 := @gN0 a (.cv m) dv_cache_0002
  have p0017 := @gVinf
  have p0018 := @gElunii (synCvv) (.cv m) (synCnnc)
  have p0019 :=
    @gAncoms (.classMem (synCvv) (.cv m)) (.classMem (.cv m) (synCnnc))
      (.classMem (synCvv) (synCuni (synCnnc))) p0018
  have p0020 := (Nominal.classEqRefl (synCfin))
  have p0021 :=
    @gSyl6eleqr (synWa (.classMem (.cv m) (synCnnc)) (.classMem (synCvv) (.cv m)))
      (synCvv) (synCuni (synCnnc)) (synCfin) p0019 p0020
  have p0022 :=
    @gEx (.classMem (.cv m) (synCnnc)) (.classMem (synCvv) (.cv m))
      (.classMem (synCvv) (synCfin)) p0021
  have p0023 :=
    @gMtoi (.classMem (.cv m) (synCnnc)) (.classMem (synCvv) (.cv m))
      (.classMem (synCvv) (synCfin)) p0017 p0022
  have p0024 := @gEleq1 (.cv a) (synCvv) (.cv m)
  have p0025_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (synCvv))
        (synWb (.objMem a m) (.classMem (synCvv) (.cv m)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCvv synWb
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
    @gNotbid (.classEq (.cv a) (synCvv)) (.objMem a m) (.classMem (synCvv) (.cv m))
      p0025_e00_recanon
  have p0026 :=
    @gSyl5ibrcom (.classMem (.cv m) (synCnnc)) (.neg (.objMem a m))
      (.classEq (.cv a) (synCvv)) (.neg (.classMem (synCvv) (.cv m))) p0023 p0025
  have p0027 :=
    @gNecon2ad (.classMem (.cv m) (synCnnc)) (.objMem a m) (.cv a) (synCvv) p0026
  have p0028 :=
    @gImp (.classMem (.cv m) (synCnnc)) (.objMem a m) (synWne (.cv a) (synCvv)) p0027
  have p0029 := @gCompleqb (.cv a) (synCvv)
  have p0030 :=
    @gNecon3bii (.cv a) (synCvv) (synCcompl (.cv a)) (synCcompl (synCvv)) p0029
  have p0031 :=
    @gSylib (synWa (.classMem (.cv m) (synCnnc)) (.objMem a m))
      (synWne (.cv a) (synCvv)) (synWne (synCcompl (.cv a)) (synCcompl (synCvv)))
      p0028 p0030
  have p0032 := @gComplV
  have p0033 := @gNeeq2i (synCcompl (synCvv)) (synC0) (synCcompl (.cv a)) p0032
  have p0034 :=
    @gSylib (synWa (.classMem (.cv m) (synCnnc)) (.objMem a m))
      (synWne (synCcompl (.cv a)) (synCcompl (synCvv)))
      (synWne (synCcompl (.cv a)) (synC0)) p0031 p0033
  have p0035 := @gN0 x (synCcompl (.cv a)) dv_cache_0003
  have p0036 := @gVex x
  have p0037 := @gElcompl (.cv x) (.cv a) p0036
  have p0038 := @gElsuci (.cv a) (.cv m) (.cv x) p0036
  have p0039 := @gNe0i (synCplc (.cv m) (synC1c)) (synCun (.cv a) (synCsn (.cv x)))
  have p0040_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.objMem a m) (.neg (.objMem x a)))
        (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCun synCnin synWnan synCcompl synCsn synCplc synWrex
          synWex synC1c
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
    @gSyl (synWa (.objMem a m) (.neg (.objMem x a)))
      (.classMem (synCun (.cv a) (synCsn (.cv x))) (synCplc (.cv m) (synC1c)))
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) p0040_e00_recanon p0039
  have p0041_e00_recanon :
    Nominal.NPrf (synWb (.classMem (.cv x) (synCcompl (.cv a))) (.neg (.objMem x a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCcompl synCnin synWnan synWa
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
    @gSylan2b (.classMem (.cv x) (synCcompl (.cv a))) (.objMem a m) (.neg (.objMem x a))
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) p0041_e00_recanon p0040
  have p0042 :=
    @gEx (.objMem a m) (.classMem (.cv x) (synCcompl (.cv a)))
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) p0041
  have p0043 :=
    @gAdantl (.objMem a m)
      (.imp (.classMem (.cv x) (synCcompl (.cv a)))
        (synWne (synCplc (.cv m) (synC1c)) (synC0)))
      (.classMem (.cv m) (synCnnc)) p0042
  have p0044 :=
    @gExlimdv (synWa (.classMem (.cv m) (synCnnc)) (.objMem a m))
      (.classMem (.cv x) (synCcompl (.cv a)))
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) x dv_cache_0004 dv_cache_0005 p0043
  have p0045 :=
    @gSyl5bi (synWne (synCcompl (.cv a)) (synC0))
      (synWex x (.classMem (.cv x) (synCcompl (.cv a))))
      (synWa (.classMem (.cv m) (synCnnc)) (.objMem a m))
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) p0035 p0044
  have p0046 :=
    @gMpd (synWa (.classMem (.cv m) (synCnnc)) (.objMem a m))
      (synWne (synCcompl (.cv a)) (synC0))
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) p0034 p0045
  have p0047 :=
    @gEx (.classMem (.cv m) (synCnnc)) (.objMem a m)
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) p0046
  have p0048 :=
    @gExlimdv (.classMem (.cv m) (synCnnc)) (.objMem a m)
      (synWne (synCplc (.cv m) (synC1c)) (synC0)) a dv_cache_0006 dv_cache_0007 p0047
  have p0049_e00_recanon :
    Nominal.NPrf (synWb (synWne (.cv m) (synC0)) (synWex a (.objMem a m))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne synC0 synCdif synCin synCcompl synCnin synWnan synWa
          synCvv synWex
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
    @gSyl5bi (synWne (.cv m) (synC0)) (synWex a (.objMem a m))
      (.classMem (.cv m) (synCnnc)) (synWne (synCplc (.cv m) (synC1c)) (synC0))
      p0049_e00_recanon p0048
  have p0050_e02_recanon :
    Nominal.NPrf
      (.imp (.objEq n m) (synWb (synWne (.cv n) (synC0)) (synWne (.cv m) (synC0)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWne synC0 synCdif synCin synCcompl synCnin synWnan synWa
          synCvv
        simp (config := { failIfUnchanged := false }) only []
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0010
  have p0050 :=
    @gFinds (synWne (.cv n) (synC0)) (synWne (synC0c) (synC0))
      (synWne (.cv m) (synC0)) (synWne (synCplc (.cv m) (synC1c)) (synC0))
      (synWne (.cv x) (synC0)) n m (.cv x) dv_cache_0008 dv_cache_0009 dv_cache_0010
      dv_cache_0011 dv_cache_0012 dv_cache_0013 dv_cache_0014 p0008 p0009
      p0050_e02_recanon p0011 p0012 p0015 p0049
  have p0051 := @gNeneqd (.classMem (.cv x) (synCnnc)) (.cv x) (synC0) p0050
  have p0052 := @gNrex (.classEq (.cv x) (synC0)) x (synCnnc) p0051
  have p0053 := @gRisset x (synC0) (synCnnc) dv_cache_0015 dv_cache_0016
  have p0054 :=
    @gMtbir (.classMem (synC0) (synCnnc))
      (synWrex x (synCnnc) (.classEq (.cv x) (synC0))) p0052 p0053
  exact p0054

/-- Checked nominal proof certificate identified upstream as `g_peano4`. -/
@[expose]
noncomputable def gPeano4 (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
          (.classEq (synCplc M (synC1c)) (synCplc N (synC1c)))) (.classEq M N)) :=
  by
  have p0000 :=
    @gN3simpa (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classEq (synCplc M (synC1c)) (synCplc N (synC1c)))
  have p0001 :=
    @gSimp3 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classEq (synCplc M (synC1c)) (synCplc N (synC1c)))
  have p0002 := @gPeano2 M
  have p0003 := @gNulnnn
  have p0004 := @gEleq1 (synCplc M (synC1c)) (synC0) (synCnnc)
  have p0005 :=
    @gMtbiri (.classEq (synCplc M (synC1c)) (synC0))
      (.classMem (synCplc M (synC1c)) (synCnnc)) (.classMem (synC0) (synCnnc)) p0003
      p0004
  have p0006 :=
    @gNecon2ai (.classMem (synCplc M (synC1c)) (synCnnc)) (synCplc M (synC1c))
      (synC0) p0005
  have p0007 :=
    @gSyl (.classMem M (synCnnc)) (.classMem (synCplc M (synC1c)) (synCnnc))
      (synWne (synCplc M (synC1c)) (synC0)) p0002 p0006
  have p0008 :=
    @gN3ad2ant1 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWne (synCplc M (synC1c)) (synC0))
      (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))) p0007
  have p0009 := @gPrepeano4 M N
  have p0010 :=
    @gSyl12anc
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc))
        (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))))
      (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classEq (synCplc M (synC1c)) (synCplc N (synC1c)))
      (synWne (synCplc M (synC1c)) (synC0)) (.classEq M N) p0000 p0001 p0008 p0009
  exact p0010

/-- Checked nominal proof certificate identified upstream as `g_suc11nnc`. -/
@[expose]
noncomputable def gSuc11nnc (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
        (synWb (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))) (.classEq M N))) :=
  by
  have p0000 := @gPeano4 M N
  have p0001 :=
    @gN3expia (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))) (.classEq M N) p0000
  have p0002 := @gAddceq1 M N (synC1c)
  have p0003 :=
    @gImpbid1 (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classEq (synCplc M (synC1c)) (synCplc N (synC1c))) (.classEq M N) p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_addccan2`. -/
@[expose]
noncomputable def gAddccan2 (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (.classMem P (synCnnc)))
        (synWb (.classEq (synCplc M N) (synCplc M P)) (.classEq N P))) :=
  by
  have p0000 := @gNncaddccl M N
  have p0001 := @gNulnnn
  have p0002 := @gEleq1 (synCplc M N) (synC0) (synCnnc)
  have p0003 :=
    @gMtbiri (.classEq (synCplc M N) (synC0)) (.classMem (synCplc M N) (synCnnc))
      (.classMem (synC0) (synCnnc)) p0001 p0002
  have p0004 :=
    @gNecon2ai (.classMem (synCplc M N) (synCnnc)) (synCplc M N) (synC0) p0003
  have p0005 :=
    @gSyl (synWa (.classMem M (synCnnc)) (.classMem N (synCnnc)))
      (.classMem (synCplc M N) (synCnnc)) (synWne (synCplc M N) (synC0)) p0000 p0004
  have p0006 :=
    @gN3adant3 (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWne (synCplc M N) (synC0)) (.classMem P (synCnnc)) p0005
  have p0007 := @gPreaddccan2 P M N
  have p0008 :=
    @gMpdan
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (.classMem P (synCnnc)))
      (synWne (synCplc M N) (synC0))
      (synWb (.classEq (synCplc M N) (synCplc M P)) (.classEq N P)) p0006 p0007
  exact p0008

/-- Checked nominal proof certificate identified upstream as `g_addccan1`. -/
@[expose]
noncomputable def gAddccan1 (P : Class) (M : Class) (N : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (.classMem P (synCnnc)))
        (synWb (.classEq (synCplc M P) (synCplc N P)) (.classEq M N))) :=
  by
  have p0000 := @gAddccom M P
  have p0001 := @gAddccom N P
  have p0002 :=
    @gEqeq12i (synCplc M P) (synCplc P M) (synCplc N P) (synCplc P N) p0000 p0001
  have p0003 := @gAddccan2 N P M
  have p0004 :=
    @gN3coml (.classMem P (synCnnc)) (.classMem M (synCnnc)) (.classMem N (synCnnc))
      (synWb (.classEq (synCplc P M) (synCplc P N)) (.classEq M N)) p0003
  have p0005 :=
    @gSyl5bb (.classEq (synCplc M P) (synCplc N P))
      (.classEq (synCplc P M) (synCplc P N))
      (synW3a (.classMem M (synCnnc)) (.classMem N (synCnnc)) (.classMem P (synCnnc)))
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

/-- Checked nominal proof certificate identified upstream as `g_dfphi2`. -/
@[expose]
noncomputable def gDfphi2 (A : Class) :
    Nominal.NPrf
      (.classEq (synCphi A) (synCimak (synCun (synCin (synCimagek (synCimak (synCdif
                    (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) A)) :=
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
      ((synWrex y A (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
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
      ((synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))).fv :=
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
  have dv_cache_0009 : x ∉ ((synCphi A)).fv :=
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
      ((synCimak (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) A)).fv :=
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
    @gIftrue (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)
  have p0001 :=
    @gEqeq2d (.classMem (.cv y) (synCnnc))
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (synCplc (.cv y) (synC1c)) (.cv x) p0000
  have p0002 :=
    @gIba (.classMem (.cv y) (synCnnc)) (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
  have p0003 := @gSimpr (.objEq x y) (.neg (.classMem (.cv y) (synCnnc)))
  have p0004 :=
    @gCon2i (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc))))
      (.classMem (.cv y) (synCnnc)) p0003
  have p0005 :=
    @gBiorf (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc))))
      (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.classMem (.cv y) (synCnnc)))
  have p0006 :=
    @gSyl (.classMem (.cv y) (synCnnc))
      (.neg (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc)))))
      (synWb (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
          (.classMem (.cv y) (synCnnc)))
        (synWo (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc))))
          (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
            (.classMem (.cv y) (synCnnc)))))
      p0004 p0005
  have p0007 :=
    @gOrcom (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc))))
      (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.classMem (.cv y) (synCnnc)))
  have p0008 :=
    @gSyl6bb (.classMem (.cv y) (synCnnc))
      (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.classMem (.cv y) (synCnnc)))
      (synWo (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc))))
        (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.classMem (.cv y) (synCnnc))))
      (synWo (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
          (.classMem (.cv y) (synCnnc)))
        (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc)))))
      p0006 p0007
  have p0009 :=
    @gN3bitrd (.classMem (.cv y) (synCnnc))
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
      (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.classMem (.cv y) (synCnnc)))
      (synWo (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
          (.classMem (.cv y) (synCnnc)))
        (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc)))))
      p0001 p0002 p0008
  have p0010 :=
    @gIffalse (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)
  have p0011 :=
    @gEqeq2d (.neg (.classMem (.cv y) (synCnnc)))
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (.cv y) (.cv x) p0010
  have p0012 := @gIba (.neg (.classMem (.cv y) (synCnnc))) (.objEq x y)
  have p0013 :=
    @gSimpr (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
      (.classMem (.cv y) (synCnnc))
  have p0014 :=
    @gCon3i
      (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.classMem (.cv y) (synCnnc)))
      (.classMem (.cv y) (synCnnc)) p0013
  have p0015 :=
    @gBiorf
      (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.classMem (.cv y) (synCnnc)))
      (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc))))
  have p0016 :=
    @gSyl (.neg (.classMem (.cv y) (synCnnc)))
      (.neg (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
          (.classMem (.cv y) (synCnnc))))
      (synWb (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc)))) (synWo
          (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
            (.classMem (.cv y) (synCnnc)))
          (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc))))))
      p0014 p0015
  have p0017_e00_recanon :
    Nominal.NPrf
      (.imp (.neg (.classMem (.cv y) (synCnnc))) (synWb (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
          (.objEq x y))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCnnc synCint synWa synC0c synCsn synC0 synCdif synCin synCcompl
          synCnin synWnan synCvv synWral synCplc synWrex synWex synC1c synWb
          synCif synWo
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
    @gN3bitrd (.neg (.classMem (.cv y) (synCnnc)))
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.objEq x y) (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc))))
      (synWo (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
          (.classMem (.cv y) (synCnnc)))
        (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc)))))
      p0017_e00_recanon p0012 p0016
  have p0018 :=
    @gPm261i (.classMem (.cv y) (synCnnc))
      (synWb (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))) (synWo
          (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
            (.classMem (.cv y) (synCnnc)))
          (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc))))))
      p0009 p0017
  have p0019 := @gEqucom y x
  have p0020 := @gVex y
  have p0021 := @gElcompl (.cv y) (synCnnc) p0020
  have p0022 :=
    @gAnbi12i (.objEq y x) (.objEq x y) (.classMem (.cv y) (synCcompl (synCnnc)))
      (.neg (.classMem (.cv y) (synCnnc))) p0019 p0021
  have p0023 :=
    @gOrbi2i (synWa (.objEq y x) (.classMem (.cv y) (synCcompl (synCnnc))))
      (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc))))
      (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.classMem (.cv y) (synCnnc)))
      p0022
  have p0024 :=
    @gBitr4i
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (synWo (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
          (.classMem (.cv y) (synCnnc)))
        (synWa (.objEq x y) (.neg (.classMem (.cv y) (synCnnc)))))
      (synWo (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
          (.classMem (.cv y) (synCnnc)))
        (synWa (.objEq y x) (.classMem (.cv y) (synCcompl (synCnnc)))))
      p0018 p0023
  have p0025 :=
    @gElun (synCopk (.cv y) (.cv x))
      (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))
  have p0026 :=
    @gElin (synCopk (.cv y) (.cv x))
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCxpk (synCnnc) (synCvv))
  have p0027 := @gVex x
  have p0028 :=
    @gOpkelimagek (.cv y) (.cv x)
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0020 p0027
  have p0029 := @gDfaddc2 (.cv y) (synC1c)
  have p0030 :=
    @gEqeq2i (synCplc (.cv y) (synC1c))
      (synCimak (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))) (.cv y))
      (.cv x) p0029
  have p0031 :=
    @gBitr4i
      (.classMem (synCopk (.cv y) (.cv x)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv x) (synCimak (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c)))) (.cv y)))
      (.classEq (.cv x) (synCplc (.cv y) (synC1c))) p0028 p0030
  have p0032 := @gOpkelxpk (.cv y) (.cv x) (synCnnc) (synCvv) p0020 p0027
  have p0033 :=
    @gMpbiran2 (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCnnc) (synCvv)))
      (.classMem (.cv y) (synCnnc)) (.classMem (.cv x) (synCvv)) p0027 p0032
  have p0034 :=
    @gAnbi12i
      (.classMem (synCopk (.cv y) (.cv x)) (synCimagek (synCimak (synCdif (synCins3k
                (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
      (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCnnc) (synCvv)))
      (.classMem (.cv y) (synCnnc)) p0031 p0033
  have p0035 :=
    @gBitri
      (.classMem (synCopk (.cv y) (.cv x)) (synCin (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))))
      (synWa (.classMem (synCopk (.cv y) (.cv x)) (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))))
        (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCnnc) (synCvv))))
      (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.classMem (.cv y) (synCnnc)))
      p0026 p0034
  have p0036 :=
    @gElin (synCopk (.cv y) (.cv x)) (synCidk)
      (synCxpk (synCcompl (synCnnc)) (synCvv))
  have p0037 := @gOpkelidkg (.cv y) (.cv x) (synCvv) (synCvv)
  have p0038_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCvv)))
        (synWb (.classMem (synCopk (.cv y) (.cv x)) (synCidk)) (.objEq y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCvv synWb synCopk synCpr synCun synCnin synWnan synCcompl
          synCsn synCidk synWex
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
    @gMp2an (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCvv))
      (synWb (.classMem (synCopk (.cv y) (.cv x)) (synCidk)) (.objEq y x)) p0020 p0027
      p0038_e02_recanon
  have p0039 := @gOpkelxpk (.cv y) (.cv x) (synCcompl (synCnnc)) (synCvv) p0020 p0027
  have p0040 :=
    @gMpbiran2
      (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCcompl (synCnnc)) (synCvv)))
      (.classMem (.cv y) (synCcompl (synCnnc))) (.classMem (.cv x) (synCvv)) p0027
      p0039
  have p0041 :=
    @gAnbi12i (.classMem (synCopk (.cv y) (.cv x)) (synCidk)) (.objEq y x)
      (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCcompl (synCnnc)) (synCvv)))
      (.classMem (.cv y) (synCcompl (synCnnc))) p0038 p0040
  have p0042 :=
    @gBitri
      (.classMem (synCopk (.cv y) (.cv x))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      (synWa (.classMem (synCopk (.cv y) (.cv x)) (synCidk))
        (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      (synWa (.objEq y x) (.classMem (.cv y) (synCcompl (synCnnc)))) p0036 p0041
  have p0043 :=
    @gOrbi12i
      (.classMem (synCopk (.cv y) (.cv x)) (synCin (synCimagek (synCimak (synCdif
                (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))))
      (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c))) (.classMem (.cv y) (synCnnc)))
      (.classMem (synCopk (.cv y) (.cv x))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      (synWa (.objEq y x) (.classMem (.cv y) (synCcompl (synCnnc)))) p0035 p0042
  have p0044 :=
    @gBitri
      (.classMem (synCopk (.cv y) (.cv x)) (synCun (synCin (synCimagek (synCimak (synCdif
                  (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      (synWo (.classMem (synCopk (.cv y) (.cv x)) (synCin (synCimagek (synCimak (synCdif
                  (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))))
        (.classMem (synCopk (.cv y) (.cv x))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      (synWo (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
          (.classMem (.cv y) (synCnnc)))
        (synWa (.objEq y x) (.classMem (.cv y) (synCcompl (synCnnc)))))
      p0025 p0043
  have p0045 :=
    @gBitr4i
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (synWo (synWa (.classEq (.cv x) (synCplc (.cv y) (synC1c)))
          (.classMem (.cv y) (synCnnc)))
        (synWa (.objEq y x) (.classMem (.cv y) (synCcompl (synCnnc)))))
      (.classMem (synCopk (.cv y) (.cv x)) (synCun (synCin (synCimagek (synCimak (synCdif
                  (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      p0024 p0044
  have p0046 :=
    @gRexbii
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classMem (synCopk (.cv y) (.cv x)) (synCun (synCin (synCimagek (synCimak (synCdif
                  (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      y A p0045
  have p0047 :=
    @gEqeq1 (.cv z) (.cv x)
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
  have p0048_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq z x) (synWb (.classEq (.cv z)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
          (.classEq (.cv x) (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
              (.cv y))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCif synWo synWa synCnnc synCint synCplc synWrex synWex
          synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0047
  have p0048 :=
    @gRexbidv (.objEq z x)
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      y A dv_cache_0001 p0048_e00_recanon
  have p0049 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPhi y z A
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0050_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv z) (.cv x)) (synWb (synWrex y A (.classEq (.cv z)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
          (synWrex y A (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
                (.cv y)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synCif, synWo, synCnnc, synCint,
          synCplc, synC1c]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0048
  have p0050 :=
    @gElab2
      (synWrex y A (.classEq (.cv z)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synWrex y A (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      z (.cv x) (synCphi A) dv_cache_0005 dv_cache_0006 p0027 p0050_e01_recanon p0049
  have p0051 :=
    @gElimak y
      (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      A (.cv x) dv_cache_0007 dv_cache_0002 dv_cache_0008 p0027
  have p0052 :=
    @gN3bitr4i
      (synWrex y A (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) (synCun (synCin (synCimagek
                (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
      (.classMem (.cv x) (synCphi A))
      (.classMem (.cv x) (synCimak (synCun (synCin (synCimagek (synCimak (synCdif
                    (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) A))
      p0046 p0050 p0051
  have p0053 :=
    @gEqriv x (synCphi A)
      (synCimak (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) A)
      dv_cache_0009 dv_cache_0010 p0052
  exact p0053

/-- Checked nominal proof certificate identified upstream as `g_phieq`. -/
@[expose]
noncomputable def gPhieq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCphi A) (synCphi B))) :=
  by
  have p0000 :=
    @gImakeq2 A B
      (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
  have p0001 := @gDfphi2 A
  have p0002 := @gDfphi2 B
  have p0003 :=
    @gN3eqtr4g (.classEq A B)
      (synCimak (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) A)
      (synCimak (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) B)
      (synCphi A) (synCphi B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_phiexg`. -/
@[expose]
noncomputable def gPhiexg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCphi A) (synCvv))) :=
  by
  have p0000 := @gDfphi2 A
  have p0001 := @gAddcexlem
  have p0002 := @gN1cex
  have p0003 := @gPw1ex (synC1c) p0002
  have p0004 := @gPw1ex (synCpw1 (synC1c)) p0003
  have p0005 :=
    @gImakex
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synC1c))) p0001 p0004
  have p0006 :=
    @gImagekex
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0005
  have p0007 := @gNncex
  have p0008 := @gVvex
  have p0009 := @gXpkex (synCnnc) (synCvv) p0007 p0008
  have p0010 :=
    @gInex
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCxpk (synCnnc) (synCvv)) p0006 p0009
  have p0011 := @gIdkex
  have p0013 := @gComplex (synCnnc) p0007
  have p0015 := @gXpkex (synCcompl (synCnnc)) (synCvv) p0013 p0008
  have p0016 :=
    @gInex (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)) p0011 p0015
  have p0017 :=
    @gUnex
      (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))) p0010 p0016
  have p0018 :=
    @gImakexg
      (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      A (synCvv) V
  have p0019 :=
    @gMpan
      (.classMem (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) (synCvv))
      (.classMem A V)
      (.classMem (synCimak (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) A) (synCvv))
      p0017 p0018
  have p0020 :=
    @gSyl5eqel (.classMem A V) (synCphi A)
      (synCimak (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) A)
      (synCvv) p0000 p0019
  exact p0020

/-- Checked nominal proof certificate identified upstream as `g_phiex`. -/
@[expose]
noncomputable def gPhiex (A : Class)
    (hyp_phiex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCphi A) (synCvv)) :=
  by
  have p0000 := @gPhiexg A (synCvv)
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

/-- Checked nominal proof certificate identified upstream as `g_dfop2lem1`. -/
@[expose]
noncomputable def gDfop2lem1 (x : Var) (y : Var) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (.cv x) (.cv y)) (synCcompl (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                        (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                    (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c))))))
        (.classEq (.cv y) (synCun (synCphi (.cv x)) (synCsn (synC0c))))) :=
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
      ((synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                  (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))).fv :=
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
  have dv_cache_0002 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
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
  have dv_cache_0003 : t ∉ ((synCopk (.cv x) (.cv y))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))).fv :=
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
  have dv_cache_0006 : t ∉ ((synCsn (synCsn (synCsn (.cv z))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))).fv :=
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
  have dv_cache_0008 : y ∉ ((synCsn (.cv z))).fv :=
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
      ((synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))).fv :=
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
  have dv_cache_0011 : y ∉ ((synCssetk)).fv :=
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
  have dv_cache_0013 : y ∉ ((synCphi (.cv x))).fv :=
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
  have dv_cache_0015 : z ∉ ((synCun (synCphi (.cv x)) (synCsn (synC0c)))).fv :=
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
  have p0000 := @gOpkex (.cv x) (.cv y)
  have p0001 :=
    @gElimak t
      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                              (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                    (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
              (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (.cv x) (.cv y)) dv_cache_0001
      dv_cache_0002 dv_cache_0003 p0000
  have p0002 := @gElpw121c z (.cv t) dv_cache_0004
  have p0003 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
      (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                  (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))
      p0002
  have p0004 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                  (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))
      z dv_cache_0005
  have p0005 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))))
      (synWa (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                  (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                  (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))))
      p0003 p0004
  have p0006 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                  (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                  (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))))
      t p0005
  have p0007 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))))
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))))
      z t
  have p0009 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                  (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                  (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))))
      (synWex t (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                        (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                    (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                        (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                    (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))))))
      p0006 p0007 p0008
  have p0010 := @gSnex (synCsn (synCsn (.cv z)))
  have p0011 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y))
  have p0012 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                              (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                    (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
              (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
      p0011
  have p0013 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                  (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                  (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))
      t (synCsn (synCsn (synCsn (.cv z)))) dv_cache_0006 dv_cache_0007 p0010 p0012
  have p0014 :=
    @gElsymdif
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
      (synCins2k (synCssetk))
      (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                      (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
            (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))
  have p0015 := @gSnex (.cv z)
  have p0016 := @gVex x
  have p0017 := @gVex y
  have p0018 :=
    @gOtkelins2k (synCsn (.cv z)) (.cv x) (.cv y) (synCssetk) p0015 p0016 p0017
  have p0019 := @gVex z
  have p0020 := @gElssetk (.cv z) (.cv y) p0019 p0017
  have p0021_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
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
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
        (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)) (.objMem z y) p0018
      p0021_e01_recanon
  have p0022 :=
    @gOtkelins3k (synCsn (.cv z)) (.cv x) (.cv y)
      (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
          (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))
      p0015 p0016 p0017
  have p0023 :=
    @gElun (synCopk (synCsn (.cv z)) (.cv x))
      (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
      (synCxpk (synCsn (synCsn (synC0c))) (synCvv))
  have p0024 :=
    @gAncom (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk))
      (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
  have p0025 :=
    @gOpkelimagek (.cv x) (.cv y)
      (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      p0016 p0017
  have p0026 :=
    @gOpkelcnvk (.cv y) (.cv x)
      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      p0017 p0016
  have p0027 := @gDfphi2 (.cv x)
  have p0028 :=
    @gEqeq2i (synCphi (.cv x))
      (synCimak (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) (.cv x))
      (.cv y) p0027
  have p0029 :=
    @gN3bitr4i
      (.classMem (synCopk (.cv x) (.cv y)) (synCimagek (synCun (synCin (synCimagek
                (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
      (.classEq (.cv y) (synCimak (synCun (synCin (synCimagek (synCimak (synCdif
                    (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) (.cv x)))
      (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      (.classEq (.cv y) (synCphi (.cv x))) p0025 p0026 p0028
  have p0030_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)) (.objMem z y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCopk synCpr synCun synCnin synWnan synWa synCcompl synCsn
          synCssetk synWex
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
    @gAnbi12i
      (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      (.classEq (.cv y) (synCphi (.cv x)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)) (.objMem z y) p0029
      p0030_e01_recanon
  have p0031 :=
    @gBitri
      (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk))
        (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                  (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      (synWa (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                  (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
        (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk)))
      (synWa (.classEq (.cv y) (synCphi (.cv x))) (.objMem z y)) p0024 p0030
  have p0032 :=
    @gExbii
      (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk))
        (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                  (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      (synWa (.classEq (.cv y) (synCphi (.cv x))) (.objMem z y)) y p0031
  have p0033 :=
    @gOpkelcok y (synCsn (.cv z)) (.cv x)
      (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
      (synCssetk) dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011 p0015 p0016
  have p0034 := @gPhiex (.cv x) p0016
  have p0035 := @gClel3 y (.cv z) (synCphi (.cv x)) dv_cache_0012 dv_cache_0013 p0034
  have p0036_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv z) (synCphi (.cv x)))
        (synWex y (synWa (.classEq (.cv y) (synCphi (.cv x))) (.objMem z y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCphi synWrex synWex synWa synCif synWo synCnnc synCint
          synCplc synC1c
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
    @gN3bitr4i
      (synWex y (synWa (.classMem (synCopk (synCsn (.cv z)) (.cv y)) (synCssetk))
          (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCimagek (synCun (synCin
                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      (synWex y (synWa (.classEq (.cv y) (synCphi (.cv x))) (.objMem z y)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv x)) (synCcomk (synCcnvk (synCimagek
              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                            (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
          (synCssetk)))
      (.classMem (.cv z) (synCphi (.cv x))) p0032 p0033 p0036_e02_recanon
  have p0037 :=
    @gOpkelxpk (synCsn (.cv z)) (.cv x) (synCsn (synCsn (synC0c))) (synCvv) p0015
      p0016
  have p0038 :=
    @gMpbiran2
      (.classMem (synCopk (synCsn (.cv z)) (.cv x))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))
      (.classMem (synCsn (.cv z)) (synCsn (synCsn (synC0c))))
      (.classMem (.cv x) (synCvv)) p0016 p0037
  have p0039 := @gSneqb (.cv z) (synC0c) p0019
  have p0040 := @gElsnc (synCsn (.cv z)) (synCsn (synC0c)) p0015
  have p0041 := @gElsnc (.cv z) (synC0c) p0019
  have p0042 :=
    @gN3bitr4ri (.classEq (synCsn (.cv z)) (synCsn (synC0c)))
      (.classEq (.cv z) (synC0c))
      (.classMem (synCsn (.cv z)) (synCsn (synCsn (synC0c))))
      (.classMem (.cv z) (synCsn (synC0c))) p0039 p0040 p0041
  have p0043 :=
    @gBitr4i
      (.classMem (synCopk (synCsn (.cv z)) (.cv x))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))
      (.classMem (synCsn (.cv z)) (synCsn (synCsn (synC0c))))
      (.classMem (.cv z) (synCsn (synC0c))) p0038 p0042
  have p0044 :=
    @gOrbi12i
      (.classMem (synCopk (synCsn (.cv z)) (.cv x)) (synCcomk (synCcnvk (synCimagek
              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                            (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
          (synCssetk)))
      (.classMem (.cv z) (synCphi (.cv x)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv x))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))
      (.classMem (.cv z) (synCsn (synC0c))) p0036 p0043
  have p0045 := @gElun (.cv z) (synCphi (.cv x)) (synCsn (synC0c))
  have p0046 :=
    @gBitr4i
      (synWo (.classMem (synCopk (synCsn (.cv z)) (.cv x)) (synCcomk (synCcnvk (synCimagek
                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                              (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
            (synCssetk))) (.classMem (synCopk (synCsn (.cv z)) (.cv x))
          (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))
      (synWo (.classMem (.cv z) (synCphi (.cv x))) (.classMem (.cv z) (synCsn (synC0c))))
      (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c)))) p0044 p0045
  have p0047 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                        (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
              (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
      (.classMem (synCopk (synCsn (.cv z)) (.cv x)) (synCun (synCcomk (synCcnvk
              (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                            (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
            (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))
      (synWo (.classMem (synCopk (synCsn (.cv z)) (.cv x)) (synCcomk (synCcnvk (synCimagek
                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                              (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
            (synCssetk))) (.classMem (synCopk (synCsn (.cv z)) (.cv x))
          (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))
      (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c)))) p0022 p0023
      p0046
  have p0048 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
        (synCins2k (synCssetk)))
      (.objMem z y)
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                        (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
              (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
      (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c)))) p0021 p0047
  have p0049 :=
    @gNotbii
      (synWb (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
          (synCins2k (synCssetk))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
          (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                          (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                    (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))
      (synWb (.objMem z y)
        (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c)))))
      p0048
  have p0050 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                  (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                  (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                  (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))
      (.neg (synWb (.classMem
            (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
            (synCins2k (synCssetk))) (.classMem
            (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (.cv x) (.cv y)))
            (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                          (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))))
      (.neg (synWb (.objMem z y)
          (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c))))))
      p0013 p0014 p0049
  have p0051 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                  (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                  (synCxpk (synCsn (synCsn (synC0c))) (synCvv))))))))
      (.neg (synWb (.objMem z y)
          (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c))))))
      z p0050
  have p0052 :=
    @gN3bitri
      (.classMem (synCopk (.cv x) (.cv y)) (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                          (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                        (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                    (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))))))
      (synWex z (.neg (synWb (.objMem z y)
            (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c)))))))
      p0001 p0009 p0051
  have p0053 :=
    @gNotbii
      (.classMem (synCopk (.cv x) (.cv y)) (synCimak (synCsymdif (synCins2k (synCssetk))
            (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                          (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                  (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWex z (.neg (synWb (.objMem z y)
            (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c)))))))
      p0052
  have p0054 :=
    @gElcompl (synCopk (.cv x) (.cv y))
      (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk
                (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                              (synCins3k (synCcompl (synCimak
                                    (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c))))
      p0000
  have p0055 :=
    @gDfcleq z (.cv y) (synCun (synCphi (.cv x)) (synCsn (synC0c))) dv_cache_0014
      dv_cache_0015
  have p0056 :=
    @gAlex
      (synWb (.objMem z y)
        (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c)))))
      z
  have p0057_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv y) (synCun (synCphi (.cv x)) (synCsn (synC0c)))) (.all z
          (synWb (.objMem z y)
            (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCun synCnin synWnan synWa synCcompl synCphi synWrex
          synWex synCif synWo synCnnc synCint synCplc synC1c synCsn synC0c
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
    @gBitri (.classEq (.cv y) (synCun (synCphi (.cv x)) (synCsn (synC0c))))
      (.all z (synWb (.objMem z y)
          (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c))))))
      (.neg (synWex z (.neg (synWb (.objMem z y)
              (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c))))))))
      p0057_e00_recanon p0056
  have p0058 :=
    @gN3bitr4i
      (.neg (.classMem (synCopk (.cv x) (.cv y)) (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                  (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                  (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.neg (synWex z (.neg (synWb (.objMem z y)
              (.classMem (.cv z) (synCun (synCphi (.cv x)) (synCsn (synC0c))))))))
      (.classMem (synCopk (.cv x) (.cv y)) (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
                      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                  (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                  (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv y) (synCun (synCphi (.cv x)) (synCsn (synC0c)))) p0053 p0054
      p0057
  exact p0058


end NFChoice.DirectNominalPrf.WPPReplay

end
