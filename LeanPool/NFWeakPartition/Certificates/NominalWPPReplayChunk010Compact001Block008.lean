/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block007

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part020`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_spfinex`. -/
@[expose]
noncomputable def gSpfinex : Nominal.NPrf (.classMem (synCspfin) (synCvv)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have dv_cache_0001 : a ≠ x := by exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0002 : a ≠ z := by
    clear dv_cache_0001
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0003 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0004 :
    t ∉
      ((synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                  (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                          (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : t ∉ ((synC1c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_a, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((Wff.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
                (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                        (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_a, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0009 : t ∉ ((synCsn (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0010 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCin (synCssetk) (synCimak
              (synCdif (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc))
                      (synCimak (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_a, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0011 :
    t ∉
      ((synCdif (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                  (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCins2k (synCssetk)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0013 : t ∉ ((synCopk (synCsn (.cv x)) (.cv a))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_a, or_false, not_false_eq_true])
  have dv_cache_0014 : z ∉ ((Class.cv t)).fv :=
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
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0015 :
    z ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
            (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                      (synCins3k (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCins2k (synCssetk))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_x, fresh_z_ne_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((synCsn (synCsn (synCsn (.cv z))))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
          not_false_eq_true])
  have dv_cache_0017 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
            (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k (synCsik
                (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                        (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCins2k (synCssetk))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_x, fresh_t_ne_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0018 :
    a ∉
      ((synCcompl (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                      (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                              (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
            (synC1c)))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0019 : a ∉ ((synCncfin (synCvv))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSpfin x z a
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @gVex a
  have p0002 :=
    @gElimak t
      (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                        (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synC1c) (.cv a) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0001
  have p0003 := @gEl1c x (.cv t) dv_cache_0007
  have p0004 :=
    @gAnbi1i (.classMem (.cv t) (synC1c))
      (synWex x (.classEq (.cv t) (synCsn (.cv x))))
      (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      p0003
  have p0005 :=
    @gN1941v (.classEq (.cv t) (synCsn (.cv x)))
      (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      x dv_cache_0008
  have p0006 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv a))
          (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                    (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (synWex x (.classEq (.cv t) (synCsn (.cv x))))
        (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
                (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                        (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
                  (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                          (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))))
      p0004 p0005
  have p0007 :=
    @gExbii
      (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv a))
          (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                    (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
                  (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                          (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))))
      t p0006
  have p0008 :=
    (Nominal.biimpRefl (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv a))
          (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                    (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))))
  have p0009 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (.cv x))) (.classMem (synCopk (.cv t) (.cv a))
          (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                    (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))
      x t
  have p0010 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synC1c)) (.classMem (synCopk (.cv t) (.cv a))
            (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                      (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                              (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
                    (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                            (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
        (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak
                                  (synCin (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk)
            (synCimak (synCdif (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc))
                      (synCimak (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
                    (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                            (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
        (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak
                                  (synCin (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))))
      p0007 p0008 p0009
  have p0011 := @gSnex (.cv x)
  have p0012 := @gOpkeq1 (.cv t) (synCsn (.cv x)) (.cv a)
  have p0013 :=
    @gEleq1d (.classEq (.cv t) (synCsn (.cv x))) (synCopk (.cv t) (.cv a))
      (synCopk (synCsn (.cv x)) (.cv a))
      (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                        (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      p0012
  have p0014 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      t (synCsn (.cv x)) dv_cache_0009 dv_cache_0010 p0011 p0013
  have p0015 :=
    @gElin (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk)
      (synCimak (synCdif (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc))
                (synCimak (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
  have p0016 := @gVex x
  have p0017 := @gElssetk (.cv x) (.cv a) p0016 p0001
  have p0018 := @gOpkex (synCsn (.cv x)) (.cv a)
  have p0019 :=
    @gElimak t
      (synCdif (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                            (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                    (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (synCsn (.cv x)) (.cv a)) dv_cache_0011
      dv_cache_0012 dv_cache_0013 p0018
  have p0020 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k
              (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                      (synCins3k (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))))
  have p0021 := @gElpw121c z (.cv t) dv_cache_0014
  have p0022 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k
            (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                      (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))
      p0021
  have p0023 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k
            (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                      (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))
      z dv_cache_0015
  have p0024 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k
              (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                      (synCins3k (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      (synWa (synWex z (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k
              (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                      (synCins3k (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      p0022 p0023
  have p0025 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k
              (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                      (synCins3k (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      t p0024
  have p0026 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k
              (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                      (synCins3k (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      z t
  have p0027 :=
    @gBitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      (synWex t (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
                (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                        (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk)))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
                (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                        (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk)))))))
      p0025 p0026
  have p0028 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCimak (synCdif (synCins3k (synCsik
                (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                        (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k
              (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                      (synCins3k (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))))
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
                (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                        (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk)))))))
      p0019 p0020 p0027
  have p0029 := @gSnex (synCsn (synCsn (.cv z)))
  have p0030 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv z))))
      (synCopk (synCsn (.cv x)) (.cv a))
  have p0031 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
      (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a)))
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn (.cv x)) (.cv a)))
      (synCdif (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                            (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                    (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
      p0030
  have p0032 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k
            (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                      (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k (synCsik
              (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                      (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))
      t (synCsn (synCsn (synCsn (.cv z)))) dv_cache_0016 dv_cache_0017 p0029 p0031
  have p0033 :=
    @gEldif
      (synCopk (synCsn (synCsn (synCsn (.cv z)))) (synCopk (synCsn (.cv x)) (.cv a)))
      (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                (synCins3k (synCimak (synCin (synCins3k (synCsik
                          (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                      (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                  (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCins2k (synCssetk))
  have p0034 := @gSnex (.cv z)
  have p0035 :=
    @gOtkelins3k (synCsn (.cv z)) (synCsn (.cv x)) (.cv a)
      (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                (synCimak (synCin (synCins3k (synCsik
                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0034 p0011 p0001
  have p0036 := @gVex z
  have p0037 :=
    @gOpksnelsik (.cv z) (.cv x)
      (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k (synCimak
                (synCin (synCins3k (synCsik
                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0036 p0016
  have p0038 := @gSrelk (.cv z) (.cv x) p0036 p0016
  have p0039 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv x)) (.cv a))) (synCins3k (synCsik
            (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k (synCimak
                      (synCin (synCins3k (synCsik
                            (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                    (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (.cv z)) (synCsn (.cv x))) (synCsik
          (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k (synCimak
                    (synCin (synCins3k (synCsik
                          (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                      (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                  (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (.cv z) (.cv x)) (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
            (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWsfin (.cv z) (.cv x)) p0035 p0037 p0038
  have p0040 :=
    @gOtkelins2k (synCsn (.cv z)) (synCsn (.cv x)) (.cv a) (synCssetk) p0034 p0011
      p0001
  have p0041 := @gElssetk (.cv z) (.cv a) p0036 p0001
  have p0042_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv z)) (.cv a)) (synCssetk)) (.objMem z a)) :=
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
      p0041
  have p0042 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv x)) (.cv a))) (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv z)) (.cv a)) (synCssetk)) (.objMem z a) p0040
      p0042_e01_recanon
  have p0043 :=
    @gNotbii
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv x)) (.cv a))) (synCins2k (synCssetk)))
      (.objMem z a) p0042
  have p0044 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv x)) (.cv a))) (synCins3k (synCsik
            (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k (synCimak
                      (synCin (synCins3k (synCsik
                            (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                    (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWsfin (.cv z) (.cv x))
      (.neg (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
            (synCopk (synCsn (.cv x)) (.cv a))) (synCins2k (synCssetk))))
      (.neg (.objMem z a)) p0039 p0043
  have p0045 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
          (synCopk (synCsn (.cv x)) (.cv a))) (synCdif (synCins3k (synCsik
              (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                      (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk))))
      (synWa (.classMem (synCopk (synCsn (synCsn (synCsn (.cv z))))
            (synCopk (synCsn (.cv x)) (.cv a))) (synCins3k (synCsik
              (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                      (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (.neg (.classMem
            (synCopk (synCsn (synCsn (synCsn (.cv z))))
              (synCopk (synCsn (.cv x)) (.cv a))) (synCins2k (synCssetk)))))
      (synWa (synWsfin (.cv z) (.cv x)) (.neg (.objMem z a))) p0032 p0033 p0044
  have p0046 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCins2k (synCssetk))))))
      (synWa (synWsfin (.cv z) (.cv x)) (.neg (.objMem z a))) z p0045
  have p0047 := @gExanali (synWsfin (.cv z) (.cv x)) (.objMem z a) z
  have p0048 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCimak (synCdif (synCins3k (synCsik
                (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                        (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv z)))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv x)) (.cv a))) (synCdif
                (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                        (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk)))))))
      (synWex z (synWa (synWsfin (.cv z) (.cv x)) (.neg (.objMem z a))))
      (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))) p0028 p0046 p0047
  have p0049_e00_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk)) (.objMem x a)) :=
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
      p0017
  have p0049 :=
    @gAnbi12i (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk)) (.objMem x a)
      (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCimak (synCdif (synCins3k (synCsik
                (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                        (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))) p0049_e00_recanon
      p0048
  have p0050 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
                  (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                          (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
              (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                      (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synWa (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk))
        (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCimak (synCdif (synCins3k
                (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                        (synCins3k (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synWa (.objMem x a) (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))
      p0014 p0015 p0049
  have p0051 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
          (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
                  (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                          (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))))
      (synWa (.objMem x a) (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))
      x p0050
  have p0052 :=
    @gN3bitri
      (.classMem (.cv a) (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k
                  (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                          (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c)))
      (synWrex t (synC1c) (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk)
            (synCimak (synCdif (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc))
                      (synCimak (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (.cv x)))
            (.classMem (synCopk (.cv t) (.cv a)) (synCin (synCssetk) (synCimak (synCdif
                    (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                            (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
        (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak
                                  (synCin (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex x (synWa (.objMem x a)
          (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))))
      p0002 p0010 p0051
  have p0053 :=
    (Nominal.biimpRefl (synWrex x (.cv a)
        (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))))
  have p0054_e01_recanon :
    Nominal.NPrf
      (synWb (synWrex x (.cv a)
          (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))) (synWex x
          (synWa (.objMem x a)
            (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synWsfin, synW3a, synCnnc,
          synCint]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0053
  have p0054 :=
    @gBitr4i
      (.classMem (.cv a) (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k
                  (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                          (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c)))
      (synWex x (synWa (.objMem x a)
          (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))))
      (synWrex x (.cv a) (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))
      p0052 p0054_e01_recanon
  have p0055 :=
    @gNotbii
      (.classMem (.cv a) (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k
                  (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                          (synCins3k (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c)))
      (synWrex x (.cv a) (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))
      p0054
  have p0056 :=
    @gElcompl (.cv a)
      (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                  (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                          (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synC1c))
      p0001
  have p0057 :=
    @gDfral2 (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))) x (.cv a)
  have p0058 :=
    @gN3bitr4i
      (.neg (.classMem (.cv a) (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k
                    (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                            (synCins3k (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c))))
      (.neg (synWrex x (.cv a)
          (.neg (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))))
      (.classMem (.cv a) (synCcompl (synCimak (synCin (synCssetk) (synCimak (synCdif
                  (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                          (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c))))
      (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))) p0055
      p0056 p0057
  have p0059 :=
    @gEqabi
      (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))) a
      (synCcompl (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                    (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c)))
      dv_cache_0018 p0058
  have p0060 :=
    @gIneq2i
      (synCcompl (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                    (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c)))
      (.cab a (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))
      (.cab a (.classMem (synCncfin (synCvv)) (.cv a))) p0059
  have p0061 :=
    @gInab (.classMem (synCncfin (synCvv)) (.cv a))
      (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))) a
  have p0062 :=
    @gEqtri
      (synCin (.cab a (.classMem (synCncfin (synCvv)) (.cv a))) (synCcompl (synCimak
            (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                      (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                              (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c))))
      (synCin (.cab a (.classMem (synCncfin (synCvv)) (.cv a))) (.cab a
          (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))))
      (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a))
          (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))))
      p0060 p0061
  have p0063 :=
    @gInteqi
      (synCin (.cab a (.classMem (synCncfin (synCvv)) (.cv a))) (synCcompl (synCimak
            (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                      (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                              (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c))))
      (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a))
          (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))))
      p0062
  have p0064 :=
    @gEqtr4i (synCspfin)
      (synCint (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral x (.cv a)
              (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))))
      (synCint (synCin (.cab a (.classMem (synCncfin (synCvv)) (.cv a))) (synCcompl
            (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                        (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                              (synCins3k (synCimak (synCin (synCins3k (synCsik
                                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
        (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak
                                  (synCin (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c)))))
      p0000 p0063
  have p0065 := @gSetswithex a (synCncfin (synCvv)) dv_cache_0019
  have p0066 := @gSsetkex
  have p0067 := @gSrelkex
  have p0068 :=
    @gSikex
      (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k (synCimak
                (synCin (synCins3k (synCsik
                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
              (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins3k (synCssetk))
                            (synCins2k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0067
  have p0069 :=
    @gIns3kex
      (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                (synCimak (synCin (synCins3k (synCsik
                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins3k (synCssetk))
                              (synCins2k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0068
  have p0071 := @gIns2kex (synCssetk) p0066
  have p0072 :=
    @gDifex
      (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                (synCins3k (synCimak (synCin (synCins3k (synCsik
                          (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                      (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                  (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins3k (synCssetk))
                                (synCins2k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCins2k (synCssetk)) p0069 p0071
  have p0073 := @gN1cex
  have p0074 := @gPw1ex (synC1c) p0073
  have p0075 := @gPw1ex (synCpw1 (synC1c)) p0074
  have p0076 :=
    @gImakex
      (synCdif (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak
                (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                            (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins2k
                    (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins3k (synCssetk))
                                  (synCins2k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0072 p0075
  have p0077 :=
    @gInex (synCssetk)
      (synCimak (synCdif (synCins3k (synCsik (synCin (synCxpk (synCnnc) (synCnnc))
                (synCimak (synCin (synCins3k (synCimak (synCin (synCins3k (synCsik
                              (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk))
                                    (synCins2k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0066 p0076
  have p0079 :=
    @gImakex
      (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                        (synCimak (synCin (synCins3k (synCsik
                                (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                    (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins3k (synCssetk))
                                      (synCins2k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c)))))))
                            (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synC1c) p0077 p0073
  have p0080 :=
    @gComplex
      (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                  (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                          (synCimak (synCin (synCins3k (synCsik
                                  (synCdif (synCxpk (synCpw (synC1c)) (synCvv)) (synCimak
                                      (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins3k (synCssetk))
                                        (synCins2k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c)))))))
                              (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synC1c))
      p0079
  have p0081 :=
    @gInex (.cab a (.classMem (synCncfin (synCvv)) (.cv a)))
      (synCcompl (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                    (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                            (synCimak (synCin (synCins3k (synCsik
                                    (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                          (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c)))
      p0065 p0080
  have p0082 :=
    @gIntex
      (synCin (.cab a (.classMem (synCncfin (synCvv)) (.cv a))) (synCcompl (synCimak
            (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                      (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin (synCins3k
                              (synCimak (synCin (synCins3k (synCsik
                                      (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                            (synCins2k (synCimak (synCin (synCins3k (synCsik (synCcompl
                                        (synCimak (synCsymdif (synCins3k (synCssetk))
        (synCins2k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c))))
      p0081
  have p0083 :=
    @gEqeltri (synCspfin)
      (synCint (synCin (.cab a (.classMem (synCncfin (synCvv)) (.cv a))) (synCcompl
            (synCimak (synCin (synCssetk) (synCimak (synCdif (synCins3k (synCsik
                        (synCin (synCxpk (synCnnc) (synCnnc)) (synCimak (synCin
                              (synCins3k (synCimak (synCin (synCins3k (synCsik
                                        (synCdif (synCxpk (synCpw (synC1c)) (synCvv))
        (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))) (synCins2k (synCimak
                                  (synCin (synCins3k (synCsik (synCcompl (synCimak
        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))))) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))))
                            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synC1c)))))
      (synCvv) p0064 p0082
  exact p0083


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part021`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_ncvspfin`. -/
@[expose]
noncomputable def gNcvspfin :
    Nominal.NPrf (.classMem (synCncfin (synCvv)) (synCspfin)) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_a_ne_z : a ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_a_ne_x : a ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have dv_cache_0001 : a ∉ ((synCncfin (synCvv))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0002 : a ≠ x := by
    clear dv_cache_0001
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0003 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0004 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have p0000 := @gNcfinex (synCvv)
  have p0001 :=
    @gElintab
      (synWa (.classMem (synCncfin (synCvv)) (.cv a))
        (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))
      a (synCncfin (synCvv)) dv_cache_0001 p0000
  have p0002 :=
    @gSimpl (.classMem (synCncfin (synCvv)) (.cv a))
      (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))
  have p0003 :=
    @gMpgbir
      (.classMem (synCncfin (synCvv)) (synCint (.cab a
            (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral x (.cv a)
                (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))))))
      (.imp (synWa (.classMem (synCncfin (synCvv)) (.cv a))
          (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))
        (.classMem (synCncfin (synCvv)) (.cv a)))
      a p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSpfin x z a
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @gEleqtrri (synCncfin (synCvv))
      (synCint (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral x (.cv a)
              (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))))
      (synCspfin) p0003 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_spfinsfincl`. -/
@[expose]
noncomputable def gSpfinsfincl (X : Class) (Z : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem X (synCspfin)) (synWsfin Z X)) (.classMem Z (synCspfin))) :=
  by
  let proofSupport : Finset Var := X.fv ∪ Z.fv
  let y : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  let a : Var := freshVar proofSupport 3
  let q : Var := freshVar proofSupport 4
  let p : Var := freshVar proofSupport 5
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_X : y ∉ X.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_Z : y ∉ Z.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_z_not_Z : z ∉ Z.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_X : x ∉ X.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_Z : x ∉ Z.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_a : z ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_a_ne_z : a ≠ z := Ne.symm fresh_z_ne_a
  have fresh_z_ne_q : z ≠ q :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_q_ne_z : q ≠ z := Ne.symm fresh_z_ne_q
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_a_ne_x : a ≠ x := Ne.symm fresh_x_ne_a
  have fresh_x_ne_q : x ≠ q :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_q_ne_x : q ≠ x := Ne.symm fresh_x_ne_q
  have fresh_x_ne_p : x ≠ p :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_p_ne_x : p ≠ x := Ne.symm fresh_x_ne_p
  have fresh_a_ne_q : a ≠ q :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_q_ne_a : q ≠ a := Ne.symm fresh_a_ne_q
  have fresh_a_ne_p : a ≠ p :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_p_ne_a : p ≠ a := Ne.symm fresh_a_ne_p
  have fresh_q_ne_p : q ≠ p :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_p_ne_q : p ≠ q := Ne.symm fresh_q_ne_p
  have dv_cache_0001 : y ∉ (Z).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_Z, not_false_eq_true])
  have dv_cache_0002 : y ∉ (X).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_X, not_false_eq_true])
  have dv_cache_0003 : q ∉ ((Wff.objEq p x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_q_ne_p, fresh_q_ne_x, or_false, not_false_eq_true])
  have dv_cache_0004 : p ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_x, not_false_eq_true])
  have dv_cache_0005 : p ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_p_ne_a, not_false_eq_true])
  have dv_cache_0006 :
    p ∉ ((Wff.all q (.imp (synWsfin (.cv q) (.cv x)) (.objMem q a)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : p ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_erase,
          Finset.mem_insert, Finset.mem_singleton, fresh_p_ne_q, fresh_p_ne_x,
          fresh_p_ne_a, or_false, and_false, not_false_eq_true])
  have dv_cache_0007 : q ∉ ((Wff.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : q ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_objMem, Finset.mem_union, Finset.mem_insert,
          Finset.mem_singleton, fresh_q_ne_z, fresh_q_ne_x, fresh_q_ne_a, or_false,
          not_false_eq_true])
  have dv_cache_0008 : a ∉ ((synWsfin (.cv z) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_z, fresh_a_ne_x, or_false, not_false_eq_true])
  have dv_cache_0009 : a ≠ p :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact (show a ≠ p from (by exact fresh_a_ne_p))
  have dv_cache_0010 : a ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show a ≠ q from (by exact fresh_a_ne_q))
  have dv_cache_0011 : p ≠ q :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show p ≠ q from (by exact fresh_p_ne_q))
  have dv_cache_0012 : a ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_x, not_false_eq_true])
  have dv_cache_0013 : a ∉ ((Class.cv z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_z, not_false_eq_true])
  have dv_cache_0014 : z ∉ (Z).fv :=
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
        simp only [fresh_z_not_Z, not_false_eq_true])
  have dv_cache_0015 : x ∉ (Z).fv :=
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
        simp only [fresh_x_not_Z, not_false_eq_true])
  have dv_cache_0016 : x ∉ (X).fv :=
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
        simp only [fresh_x_not_X, not_false_eq_true])
  have dv_cache_0017 :
    x ∉
      ((Wff.imp (synWsfin Z X)
          (.imp (.classMem X (synCspfin)) (.classMem Z (synCspfin))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          fresh_x_not_Z, fresh_x_not_X, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0018 :
    z ∉
      ((Wff.imp (synWsfin Z (.cv x))
          (.imp (.classMem (.cv x) (synCspfin)) (.classMem Z (synCspfin))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_Z, fresh_z_ne_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin Z X y
      dv_cache_0001 dv_cache_0002
  have p0001 := @gSfineq1 (.cv z) Z (.cv x)
  have p0002 := @gEleq1 (.cv z) Z (synCspfin)
  have p0003 :=
    @gImbi2d (.classEq (.cv z) Z) (.classMem (.cv z) (synCspfin))
      (.classMem Z (synCspfin)) (.classMem (.cv x) (synCspfin)) p0002
  have p0004 :=
    @gImbi12d (.classEq (.cv z) Z) (synWsfin (.cv z) (.cv x)) (synWsfin Z (.cv x))
      (.imp (.classMem (.cv x) (synCspfin)) (.classMem (.cv z) (synCspfin)))
      (.imp (.classMem (.cv x) (synCspfin)) (.classMem Z (synCspfin))) p0001 p0003
  have p0005 := @gSfineq2 (.cv x) X Z
  have p0006 := @gEleq1 (.cv x) X (synCspfin)
  have p0007 :=
    @gImbi1d (.classEq (.cv x) X) (.classMem (.cv x) (synCspfin))
      (.classMem X (synCspfin)) (.classMem Z (synCspfin)) p0006
  have p0008 :=
    @gImbi12d (.classEq (.cv x) X) (synWsfin Z (.cv x)) (synWsfin Z X)
      (.imp (.classMem (.cv x) (synCspfin)) (.classMem Z (synCspfin)))
      (.imp (.classMem X (synCspfin)) (.classMem Z (synCspfin))) p0005 p0007
  have p0009 := @gSfineq2 (.cv p) (.cv x) (.cv q)
  have p0010_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p x) (synWb (synWsfin (.cv q) (.cv p)) (synWsfin (.cv q) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsfin synW3a synWa synCnnc synCint synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @gImbi1d (.objEq p x) (synWsfin (.cv q) (.cv p)) (synWsfin (.cv q) (.cv x))
      (.objMem q a) p0010_e00_recanon
  have p0011 :=
    @gAlbidv (.objEq p x) (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))
      (.imp (synWsfin (.cv q) (.cv x)) (.objMem q a)) q dv_cache_0003 p0010
  have p0012_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv p) (.cv x))
        (synWb (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))
          (.all q (.imp (synWsfin (.cv q) (.cv x)) (.objMem q a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsfin synW3a synWa synCnnc synCint synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @gRspcv (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))
      (.all q (.imp (synWsfin (.cv q) (.cv x)) (.objMem q a))) p (.cv x) (.cv a)
      dv_cache_0004 dv_cache_0005 dv_cache_0006 p0012_e00_recanon
  have p0013 := @gSfineq1 (.cv q) (.cv z) (.cv x)
  have p0014 := @gEleq1 (.cv q) (.cv z) (.cv a)
  have p0015_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq q z) (synWb (synWsfin (.cv q) (.cv x)) (synWsfin (.cv z) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synWsfin synW3a synWa synCnnc synCint synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0015_e01_recanon :
    Nominal.NPrf (.imp (.objEq q z) (synWb (.objMem q a) (.objMem z a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _)
      p0014
  have p0015 :=
    @gImbi12d (.objEq q z) (synWsfin (.cv q) (.cv x)) (synWsfin (.cv z) (.cv x))
      (.objMem q a) (.objMem z a) p0015_e00_recanon p0015_e01_recanon
  have p0016 :=
    @gSpv (.imp (synWsfin (.cv q) (.cv x)) (.objMem q a))
      (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)) q z dv_cache_0007 p0015
  have p0017 :=
    @gCom12 (.all q (.imp (synWsfin (.cv q) (.cv x)) (.objMem q a)))
      (synWsfin (.cv z) (.cv x)) (.objMem z a) p0016
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (.objMem x a) (.imp
          (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))
          (.all q (.imp (synWsfin (.cv q) (.cv x)) (.objMem q a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWral synWsfin synW3a synWa synCnnc synCint synWex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0018 :=
    @gSyl9r (.objMem x a)
      (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))
      (.all q (.imp (synWsfin (.cv q) (.cv x)) (.objMem q a)))
      (synWsfin (.cv z) (.cv x)) (.objMem z a) p0018_e00_recanon p0017
  have p0019 :=
    @gCom23 (synWsfin (.cv z) (.cv x)) (.objMem x a)
      (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))
      (.objMem z a) p0018
  have p0020 :=
    @gAdantld (synWsfin (.cv z) (.cv x))
      (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))
      (.imp (.objMem x a) (.objMem z a)) (.classMem (synCncfin (synCvv)) (.cv a)) p0019
  have p0021 :=
    @gA2d (synWsfin (.cv z) (.cv x))
      (synWa (.classMem (synCncfin (synCvv)) (.cv a))
        (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))))
      (.objMem x a) (.objMem z a) p0020
  have p0022 :=
    @gAlimdv (synWsfin (.cv z) (.cv x))
      (.imp (synWa (.classMem (synCncfin (synCvv)) (.cv a))
          (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))))
        (.objMem x a))
      (.imp (synWa (.classMem (synCncfin (synCvv)) (.cv a))
          (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))))
        (.objMem z a))
      a dv_cache_0008 p0021
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSpfin p q a
      dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0024 :=
    @gEleq2i (synCspfin)
      (synCint (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral p (.cv a)
              (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))))))
      (.cv x) p0023
  have p0025 := @gVex x
  have p0026 :=
    @gElintab
      (synWa (.classMem (synCncfin (synCvv)) (.cv a))
        (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))))
      a (.cv x) dv_cache_0012 p0025
  have p0027_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) (synCint (.cab a
              (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral p (.cv a)
                  (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))))))) (.all a (.imp
            (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral p (.cv a)
                (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCint synWa synCncfin synCio synCuni synWex synCsn synCvv
          synWral synWsfin synW3a synCnnc
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0026
  have p0027 :=
    @gBitri (.classMem (.cv x) (synCspfin))
      (.classMem (.cv x) (synCint (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a))
              (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))))))
      (.all a (.imp (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral p (.cv a)
              (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a)))
      p0024 p0027_e01_recanon
  have p0028 :=
    @gEleq2i (synCspfin)
      (synCint (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral p (.cv a)
              (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))))))
      (.cv z) p0023
  have p0029 := @gVex z
  have p0030 :=
    @gElintab
      (synWa (.classMem (synCncfin (synCvv)) (.cv a))
        (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))))
      a (.cv z) dv_cache_0013 p0029
  have p0031_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv z) (synCint (.cab a
              (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral p (.cv a)
                  (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a)))))))) (.all a (.imp
            (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral p (.cv a)
                (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem z a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCint synWa synCncfin synCio synCuni synWex synCsn synCvv
          synWral synWsfin synW3a synCnnc
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cint,
          NFChoice.Compiler.CoreFVSimp.fv_class_cab,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.all
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0030
  have p0031 :=
    @gBitri (.classMem (.cv z) (synCspfin))
      (.classMem (.cv z) (synCint (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a))
              (synWral p (.cv a) (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))))))
      (.all a (.imp (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral p (.cv a)
              (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem z a)))
      p0028 p0031_e01_recanon
  have p0032 :=
    @gN3imtr4g (synWsfin (.cv z) (.cv x))
      (.all a (.imp (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral p (.cv a)
              (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a)))
      (.all a (.imp (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral p (.cv a)
              (.all q (.imp (synWsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem z a)))
      (.classMem (.cv x) (synCspfin)) (.classMem (.cv z) (synCspfin)) p0022 p0027 p0031
  have p0033 :=
    @gVtocl2g
      (.imp (synWsfin (.cv z) (.cv x))
        (.imp (.classMem (.cv x) (synCspfin)) (.classMem (.cv z) (synCspfin))))
      (.imp (synWsfin Z (.cv x))
        (.imp (.classMem (.cv x) (synCspfin)) (.classMem Z (synCspfin))))
      (.imp (synWsfin Z X) (.imp (.classMem X (synCspfin)) (.classMem Z (synCspfin))))
      z x Z X (synCnnc) (synCnnc) dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 p0004 p0008 p0032
  have p0034 :=
    @gN3adant3 (.classMem Z (synCnnc)) (.classMem X (synCnnc))
      (.imp (synWsfin Z X) (.imp (.classMem X (synCspfin)) (.classMem Z (synCspfin))))
      (synWex y (synWa (.classMem (synCpw1 (.cv y)) Z) (.classMem (synCpw (.cv y)) X)))
      p0033
  have p0035 :=
    @gSylbi (synWsfin Z X)
      (synW3a (.classMem Z (synCnnc)) (.classMem X (synCnnc)) (synWex y
          (synWa (.classMem (synCpw1 (.cv y)) Z) (.classMem (synCpw (.cv y)) X))))
      (.imp (synWsfin Z X) (.imp (.classMem X (synCspfin)) (.classMem Z (synCspfin))))
      p0000 p0034
  have p0036 :=
    @gPm243i (synWsfin Z X)
      (.imp (.classMem X (synCspfin)) (.classMem Z (synCspfin))) p0035
  have p0037 :=
    @gImpcom (synWsfin Z X) (.classMem X (synCspfin)) (.classMem Z (synCspfin)) p0036
  exact p0037

/-- Checked nominal proof certificate identified upstream as `g_spfininduct`. -/
@[expose]
noncomputable def gSpfininduct (x : Var) (z : Var) (B : Class) (V : Class)
    (dv_B_x : x ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (synW3a (.classMem B V) (.classMem (synCncfin (synCvv)) B)
          (synWral x (synCspfin) (.all z
              (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
                (.classMem (.cv z) B))))) (synWss (synCspfin) B)) :=
  by
  let proofSupport : Finset Var :=
    ({ x } : Finset Var) ∪ ({ z } : Finset Var) ∪ B.fv ∪ V.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_ne_x : a ≠ x := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_a : x ≠ a := Ne.symm fresh_a_ne_x
  have fresh_a_ne_z : a ≠ z := by
    intro h
    exact
      fresh_a
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_z_ne_a : z ≠ a := Ne.symm fresh_a_ne_z
  have fresh_a_not_B : a ∉ B.fv := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have dv_cache_0001 : z ∉ ((Wff.classMem (.cv x) (synCspfin))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_z), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0002 : z ∉ ((Wff.classMem (.cv x) (synCin (synCspfin) B))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_x_z), dv_B_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0003 : a ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show a ≠ x from (by exact fresh_a_ne_x))
  have dv_cache_0004 : a ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show a ≠ z from (by exact fresh_a_ne_z))
  have dv_cache_0005 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ z from (by exact dv_x_z))
  have dv_cache_0006 : z ∉ ((Wff.classEq (.cv a) (synCin (synCspfin) B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_a, dv_B_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv a)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_a, not_false_eq_true])
  have dv_cache_0008 : x ∉ ((synCin (synCspfin) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          dv_B_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0009 : a ∉ ((synCin (synCspfin) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin, Finset.mem_union,
          fresh_a_not_B, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    a ∉
      ((synWa (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B))
          (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
                (.classMem (.cv z) (synCin (synCspfin) B))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CoreFVSimp.fv_wff_all,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wsfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, fresh_a_not_B, fresh_a_ne_z, fresh_a_ne_x,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @gSpfinex
  have p0001 := @gInexg (synCspfin) B (synCvv) V
  have p0002 :=
    @gMpan (.classMem (synCspfin) (synCvv)) (.classMem B V)
      (.classMem (synCin (synCspfin) B) (synCvv)) p0000 p0001
  have p0003 := @gNcvspfin
  have p0004 := @gElin (synCncfin (synCvv)) (synCspfin) B
  have p0005 :=
    @gBiimpri (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B))
      (synWa (.classMem (synCncfin (synCvv)) (synCspfin))
        (.classMem (synCncfin (synCvv)) B))
      p0004
  have p0006 :=
    @gMpan (.classMem (synCncfin (synCvv)) (synCspfin))
      (.classMem (synCncfin (synCvv)) B)
      (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B)) p0003 p0005
  have p0007 := @gElin (.cv x) (synCspfin) B
  have p0008 := @gSpfinsfincl (.cv x) (.cv z)
  have p0009 :=
    @gAdantrl (.classMem (.cv x) (synCspfin)) (synWsfin (.cv z) (.cv x))
      (.classMem (.cv z) (synCspfin)) (.classMem (.cv x) B) p0008
  have p0010 :=
    @gA1d
      (synWa (.classMem (.cv x) (synCspfin))
        (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))))
      (.classMem (.cv z) (synCspfin)) (.classMem (.cv z) B) p0009
  have p0011 :=
    @gAncrd
      (synWa (.classMem (.cv x) (synCspfin))
        (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))))
      (.classMem (.cv z) B) (.classMem (.cv z) (synCspfin)) p0010
  have p0012 := @gElin (.cv z) (synCspfin) B
  have p0013 :=
    @gSyl6ibr
      (synWa (.classMem (.cv x) (synCspfin))
        (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))))
      (.classMem (.cv z) B)
      (synWa (.classMem (.cv z) (synCspfin)) (.classMem (.cv z) B))
      (.classMem (.cv z) (synCin (synCspfin) B)) p0011 p0012
  have p0014 :=
    @gEx (.classMem (.cv x) (synCspfin))
      (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
      (.imp (.classMem (.cv z) B) (.classMem (.cv z) (synCin (synCspfin) B))) p0013
  have p0015 :=
    @gA2d (.classMem (.cv x) (synCspfin))
      (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))) (.classMem (.cv z) B)
      (.classMem (.cv z) (synCin (synCspfin) B)) p0014
  have p0016 :=
    @gExp4a (.classMem (.cv x) (synCspfin))
      (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))) (.classMem (.cv z) B))
      (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))
      (.classMem (.cv z) (synCin (synCspfin) B)) p0015
  have p0017 :=
    @gA2i (.classMem (.cv x) (synCspfin))
      (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))) (.classMem (.cv z) B))
      (.imp (.classMem (.cv x) B)
        (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B))))
      p0016
  have p0018 :=
    @gImp3a
      (.imp (.classMem (.cv x) (synCspfin))
        (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))
      (.classMem (.cv x) (synCspfin)) (.classMem (.cv x) B)
      (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B)))
      p0017
  have p0019 :=
    @gSyl5bi (.classMem (.cv x) (synCin (synCspfin) B))
      (synWa (.classMem (.cv x) (synCspfin)) (.classMem (.cv x) B))
      (.imp (.classMem (.cv x) (synCspfin))
        (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))
      (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B)))
      p0007 p0018
  have p0020 :=
    @gN2alimi
      (.imp (.classMem (.cv x) (synCspfin))
        (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))
      (.imp (.classMem (.cv x) (synCin (synCspfin) B))
        (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B))))
      x z p0019
  have p0021 :=
    (Nominal.biimpRefl (synWral x (synCspfin) (.all z
          (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B)))))
  have p0022 :=
    @gN1921v (.classMem (.cv x) (synCspfin))
      (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x))) (.classMem (.cv z) B))
      z dv_cache_0001
  have p0023 :=
    @gAlbii
      (.all z (.imp (.classMem (.cv x) (synCspfin))
          (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B))))
      (.imp (.classMem (.cv x) (synCspfin)) (.all z
          (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B))))
      x p0022
  have p0024 :=
    @gBitr4i
      (synWral x (synCspfin) (.all z
          (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B))))
      (.all x (.imp (.classMem (.cv x) (synCspfin)) (.all z
            (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
              (.classMem (.cv z) B)))))
      (.all x (.all z (.imp (.classMem (.cv x) (synCspfin))
            (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
              (.classMem (.cv z) B)))))
      p0021 p0023
  have p0025 :=
    (Nominal.biimpRefl (synWral x (synCin (synCspfin) B) (.all z
          (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B))))))
  have p0026 :=
    @gN1921v (.classMem (.cv x) (synCin (synCspfin) B))
      (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B))) z
      dv_cache_0002
  have p0027 :=
    @gAlbii
      (.all z (.imp (.classMem (.cv x) (synCin (synCspfin) B))
          (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B)))))
      (.imp (.classMem (.cv x) (synCin (synCspfin) B)) (.all z
          (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B)))))
      x p0026
  have p0028 :=
    @gBitr4i
      (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
            (.classMem (.cv z) (synCin (synCspfin) B)))))
      (.all x (.imp (.classMem (.cv x) (synCin (synCspfin) B)) (.all z
            (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B))))))
      (.all x (.all z (.imp (.classMem (.cv x) (synCin (synCspfin) B))
            (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B))))))
      p0025 p0027
  have p0029 :=
    @gN3imtr4i
      (.all x (.all z (.imp (.classMem (.cv x) (synCspfin))
            (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
              (.classMem (.cv z) B)))))
      (.all x (.all z (.imp (.classMem (.cv x) (synCin (synCspfin) B))
            (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B))))))
      (synWral x (synCspfin) (.all z
          (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B))))
      (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
            (.classMem (.cv z) (synCin (synCspfin) B)))))
      p0020 p0024 p0028
  have p0030 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSpfin x z a
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0031 := @gEleq2 (.cv a) (synCin (synCspfin) B) (synCncfin (synCvv))
  have p0032 := @gEleq2 (.cv a) (synCin (synCspfin) B) (.cv z)
  have p0033_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (synCin (synCspfin) B))
        (synWb (.objMem z a) (.classMem (.cv z) (synCin (synCspfin) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCin synCcompl synCnin synWnan synWa synCspfin synCint synWb
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
      p0032
  have p0033 :=
    @gImbi2d (.classEq (.cv a) (synCin (synCspfin) B)) (.objMem z a)
      (.classMem (.cv z) (synCin (synCspfin) B)) (synWsfin (.cv z) (.cv x))
      p0033_e00_recanon
  have p0034 :=
    @gAlbidv (.classEq (.cv a) (synCin (synCspfin) B))
      (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))
      (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B))) z
      dv_cache_0006 p0033
  have p0035 :=
    @gRaleqbi1dv (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))
      (.all z (.imp (synWsfin (.cv z) (.cv x)) (.classMem (.cv z) (synCin (synCspfin) B))))
      x (.cv a) (synCin (synCspfin) B) dv_cache_0007 dv_cache_0008 p0034
  have p0036 :=
    @gAnbi12d (.classEq (.cv a) (synCin (synCspfin) B))
      (.classMem (synCncfin (synCvv)) (.cv a))
      (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B))
      (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))
      (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
            (.classMem (.cv z) (synCin (synCspfin) B)))))
      p0031 p0035
  have p0037 :=
    @gElabg
      (synWa (.classMem (synCncfin (synCvv)) (.cv a))
        (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))
      (synWa (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B))
        (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
              (.classMem (.cv z) (synCin (synCspfin) B))))))
      a (synCin (synCspfin) B) (synCvv) dv_cache_0009 dv_cache_0010 p0036
  have p0038 :=
    @gBiimprd (.classMem (synCin (synCspfin) B) (synCvv))
      (.classMem (synCin (synCspfin) B) (.cab a
          (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral x (.cv a)
              (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))))
      (synWa (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B))
        (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
              (.classMem (.cv z) (synCin (synCspfin) B))))))
      p0037
  have p0039 :=
    @gN3impib (.classMem (synCin (synCspfin) B) (synCvv))
      (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B))
      (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
            (.classMem (.cv z) (synCin (synCspfin) B)))))
      (.classMem (synCin (synCspfin) B) (.cab a
          (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral x (.cv a)
              (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))))
      p0038
  have p0040 :=
    @gIntss1 (synCin (synCspfin) B)
      (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a))
          (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a))))))
  have p0041 :=
    @gSyl
      (synW3a (.classMem (synCin (synCspfin) B) (synCvv))
        (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B))
        (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
              (.classMem (.cv z) (synCin (synCspfin) B))))))
      (.classMem (synCin (synCspfin) B) (.cab a
          (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral x (.cv a)
              (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))))
      (synWss (synCint (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a))
              (synWral x (.cv a) (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))))
        (synCin (synCspfin) B))
      p0039 p0040
  have p0042 :=
    @gSyl5eqss
      (synW3a (.classMem (synCin (synCspfin) B) (synCvv))
        (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B))
        (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
              (.classMem (.cv z) (synCin (synCspfin) B))))))
      (synCspfin)
      (synCint (.cab a (synWa (.classMem (synCncfin (synCvv)) (.cv a)) (synWral x (.cv a)
              (.all z (.imp (synWsfin (.cv z) (.cv x)) (.objMem z a)))))))
      (synCin (synCspfin) B) p0030 p0041
  have p0043 := @gInss2 (synCspfin) B
  have p0044 :=
    @gSyl6ss
      (synW3a (.classMem (synCin (synCspfin) B) (synCvv))
        (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B))
        (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
              (.classMem (.cv z) (synCin (synCspfin) B))))))
      (synCspfin) (synCin (synCspfin) B) B p0042 p0043
  have p0045 :=
    @gSyl3an (.classMem B V) (.classMem (synCin (synCspfin) B) (synCvv))
      (.classMem (synCncfin (synCvv)) B)
      (.classMem (synCncfin (synCvv)) (synCin (synCspfin) B))
      (synWral x (synCspfin) (.all z
          (.imp (synWa (.classMem (.cv x) B) (synWsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B))))
      (synWral x (synCin (synCspfin) B) (.all z (.imp (synWsfin (.cv z) (.cv x))
            (.classMem (.cv z) (synCin (synCspfin) B)))))
      (synWss (synCspfin) B) p0002 p0006 p0029 p0044
  exact p0045


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part022`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_vfinspnn`. -/
@[expose]
noncomputable def gVfinspnn :
    Nominal.NPrf
      (.imp (.classMem (synCvv) (synCfin))
        (synWss (synCspfin) (synCdif (synCnnc) (synCsn (synC0))))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let z : Var := freshVar proofSupport 1
  let y : Var := freshVar proofSupport 2
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have dv_cache_0001 : y ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((synWne (.cv z) (synC0))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : x ∉ ((synCdif (synCnnc) (synCsn (synC0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 : z ∉ ((synCdif (synCnnc) (synCsn (synC0)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have p0000 := @gVvex
  have p0001 := @gNcfinprop (synCvv) (synCvv)
  have p0002 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCvv) (synCvv))
      (synWa (.classMem (synCncfin (synCvv)) (synCnnc))
        (.classMem (synCvv) (synCncfin (synCvv))))
      p0000 p0001
  have p0003 := @gNe0i (synCncfin (synCvv)) (synCvv)
  have p0004 :=
    @gAnim2i (.classMem (synCvv) (synCncfin (synCvv)))
      (synWne (synCncfin (synCvv)) (synC0))
      (.classMem (synCncfin (synCvv)) (synCnnc)) p0003
  have p0005 :=
    @gSyl (.classMem (synCvv) (synCfin))
      (synWa (.classMem (synCncfin (synCvv)) (synCnnc))
        (.classMem (synCvv) (synCncfin (synCvv))))
      (synWa (.classMem (synCncfin (synCvv)) (synCnnc))
        (synWne (synCncfin (synCvv)) (synC0)))
      p0002 p0004
  have p0006 := @gEldifsn (synCncfin (synCvv)) (synCnnc) (synC0)
  have p0007 :=
    @gSylibr (.classMem (synCvv) (synCfin))
      (synWa (.classMem (synCncfin (synCvv)) (synCnnc))
        (synWne (synCncfin (synCvv)) (synC0)))
      (.classMem (synCncfin (synCvv)) (synCdif (synCnnc) (synCsn (synC0)))) p0005
      p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin (.cv z) (.cv x)
      y dv_cache_0001 dv_cache_0002
  have p0009 := @gNe0i (.cv z) (synCpw1 (.cv y))
  have p0010 :=
    @gAdantr (.classMem (synCpw1 (.cv y)) (.cv z)) (synWne (.cv z) (synC0))
      (.classMem (synCpw (.cv y)) (.cv x)) p0009
  have p0011 :=
    @gExlimiv
      (synWa (.classMem (synCpw1 (.cv y)) (.cv z)) (.classMem (synCpw (.cv y)) (.cv x)))
      (synWne (.cv z) (synC0)) y dv_cache_0003 p0010
  have p0012 := @gEldifsn (.cv z) (synCnnc) (synC0)
  have p0013 :=
    @gBiimpri (.classMem (.cv z) (synCdif (synCnnc) (synCsn (synC0))))
      (synWa (.classMem (.cv z) (synCnnc)) (synWne (.cv z) (synC0))) p0012
  have p0014 :=
    @gSylan2
      (synWex y (synWa (.classMem (synCpw1 (.cv y)) (.cv z))
          (.classMem (synCpw (.cv y)) (.cv x))))
      (.classMem (.cv z) (synCnnc)) (synWne (.cv z) (synC0))
      (.classMem (.cv z) (synCdif (synCnnc) (synCsn (synC0)))) p0011 p0013
  have p0015 :=
    @gN3adant2 (.classMem (.cv z) (synCnnc))
      (synWex y (synWa (.classMem (synCpw1 (.cv y)) (.cv z))
          (.classMem (synCpw (.cv y)) (.cv x))))
      (.classMem (.cv z) (synCdif (synCnnc) (synCsn (synC0))))
      (.classMem (.cv x) (synCnnc)) p0014
  have p0016 :=
    @gSylbi (synWsfin (.cv z) (.cv x))
      (synW3a (.classMem (.cv z) (synCnnc)) (.classMem (.cv x) (synCnnc)) (synWex y
          (synWa (.classMem (synCpw1 (.cv y)) (.cv z))
            (.classMem (synCpw (.cv y)) (.cv x)))))
      (.classMem (.cv z) (synCdif (synCnnc) (synCsn (synC0)))) p0008 p0015
  have p0017 :=
    @gAdantl (synWsfin (.cv z) (.cv x))
      (.classMem (.cv z) (synCdif (synCnnc) (synCsn (synC0))))
      (.classMem (.cv x) (synCdif (synCnnc) (synCsn (synC0)))) p0016
  have p0018 := Nominal.gen p0017 z
  have p0019 :=
    @gRgenw
      (.all z (.imp (synWa (.classMem (.cv x) (synCdif (synCnnc) (synCsn (synC0))))
            (synWsfin (.cv z) (.cv x)))
          (.classMem (.cv z) (synCdif (synCnnc) (synCsn (synC0))))))
      x (synCspfin) p0018
  have p0020 := @gNncex
  have p0021 := @gSnex (synC0)
  have p0022 := @gDifex (synCnnc) (synCsn (synC0)) p0020 p0021
  have p0023 :=
    @gSpfininduct x z (synCdif (synCnnc) (synCsn (synC0))) (synCvv) dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0024 :=
    @gMp3an1 (.classMem (synCdif (synCnnc) (synCsn (synC0))) (synCvv))
      (.classMem (synCncfin (synCvv)) (synCdif (synCnnc) (synCsn (synC0))))
      (synWral x (synCspfin) (.all z (.imp
            (synWa (.classMem (.cv x) (synCdif (synCnnc) (synCsn (synC0))))
              (synWsfin (.cv z) (.cv x)))
            (.classMem (.cv z) (synCdif (synCnnc) (synCsn (synC0)))))))
      (synWss (synCspfin) (synCdif (synCnnc) (synCsn (synC0)))) p0022 p0023
  have p0025 :=
    @gSylancl (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCvv)) (synCdif (synCnnc) (synCsn (synC0))))
      (synWral x (synCspfin) (.all z (.imp
            (synWa (.classMem (.cv x) (synCdif (synCnnc) (synCsn (synC0))))
              (synWsfin (.cv z) (.cv x)))
            (.classMem (.cv z) (synCdif (synCnnc) (synCsn (synC0)))))))
      (synWss (synCspfin) (synCdif (synCnnc) (synCsn (synC0)))) p0007 p0019 p0024
  exact p0025

/-- Checked nominal proof certificate identified upstream as `g_n_1cvsfin`. -/
@[expose]
noncomputable def gN1cvsfin :
    Nominal.NPrf
      (.imp (.classMem (synCvv) (synCfin))
        (synWsfin (synCncfin (synC1c)) (synCncfin (synCvv)))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  have dv_cache_0001 : a ∉ ((synCvv)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 :
    a ∉
      ((synWa (.classMem (synC1c) (synCncfin (synC1c)))
          (.classMem (synCvv) (synCncfin (synCvv))))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 : a ∉ ((synCncfin (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0004 : a ∉ ((synCncfin (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have p0000 := @gN1cex
  have p0001 := @gNcfinprop (synC1c) (synCvv)
  have p0002 :=
    @gSimpld (synWa (.classMem (synCvv) (synCfin)) (.classMem (synC1c) (synCvv)))
      (.classMem (synCncfin (synC1c)) (synCnnc))
      (.classMem (synC1c) (synCncfin (synC1c))) p0001
  have p0003 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synC1c) (synCvv))
      (.classMem (synCncfin (synC1c)) (synCnnc)) p0000 p0002
  have p0004 := @gVvex
  have p0005 := @gNcfinprop (synCvv) (synCvv)
  have p0006 :=
    @gSimpld (synWa (.classMem (synCvv) (synCfin)) (.classMem (synCvv) (synCvv)))
      (.classMem (synCncfin (synCvv)) (synCnnc))
      (.classMem (synCvv) (synCncfin (synCvv))) p0005
  have p0007 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCvv) (synCvv))
      (.classMem (synCncfin (synCvv)) (synCnnc)) p0004 p0006
  have p0009 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synC1c) (synCvv))
      (synWa (.classMem (synCncfin (synC1c)) (synCnnc))
        (.classMem (synC1c) (synCncfin (synC1c))))
      p0000 p0001
  have p0010 :=
    @gSimprd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synC1c)) (synCnnc))
      (.classMem (synC1c) (synCncfin (synC1c))) p0009
  have p0012 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCvv) (synCvv))
      (synWa (.classMem (synCncfin (synCvv)) (synCnnc))
        (.classMem (synCvv) (synCncfin (synCvv))))
      p0004 p0005
  have p0013 :=
    @gSimprd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCvv)) (synCnnc))
      (.classMem (synCvv) (synCncfin (synCvv))) p0012
  have p0015 := @gPw1eq (.cv a) (synCvv)
  have p0016 := @gDf1c2
  have p0017 :=
    @gSyl6eqr (.classEq (.cv a) (synCvv)) (synCpw1 (.cv a)) (synCpw1 (synCvv))
      (synC1c) p0015 p0016
  have p0018 :=
    @gEleq1d (.classEq (.cv a) (synCvv)) (synCpw1 (.cv a)) (synC1c)
      (synCncfin (synC1c)) p0017
  have p0019 := @gPweq (.cv a) (synCvv)
  have p0020 := @gPwv
  have p0021 :=
    @gSyl6eq (.classEq (.cv a) (synCvv)) (synCpw (.cv a)) (synCpw (synCvv)) (synCvv)
      p0019 p0020
  have p0022 :=
    @gEleq1d (.classEq (.cv a) (synCvv)) (synCpw (.cv a)) (synCvv)
      (synCncfin (synCvv)) p0021
  have p0023 :=
    @gAnbi12d (.classEq (.cv a) (synCvv))
      (.classMem (synCpw1 (.cv a)) (synCncfin (synC1c)))
      (.classMem (synC1c) (synCncfin (synC1c)))
      (.classMem (synCpw (.cv a)) (synCncfin (synCvv)))
      (.classMem (synCvv) (synCncfin (synCvv))) p0018 p0022
  have p0024 :=
    @gSpcev
      (synWa (.classMem (synCpw1 (.cv a)) (synCncfin (synC1c)))
        (.classMem (synCpw (.cv a)) (synCncfin (synCvv))))
      (synWa (.classMem (synC1c) (synCncfin (synC1c)))
        (.classMem (synCvv) (synCncfin (synCvv))))
      a (synCvv) dv_cache_0001 dv_cache_0002 p0004 p0023
  have p0025 :=
    @gSyl2anc (.classMem (synCvv) (synCfin))
      (.classMem (synC1c) (synCncfin (synC1c)))
      (.classMem (synCvv) (synCncfin (synCvv)))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCncfin (synC1c)))
          (.classMem (synCpw (.cv a)) (synCncfin (synCvv)))))
      p0010 p0013 p0024
  have p0026 :=
    @gN3jca (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synC1c)) (synCnnc))
      (.classMem (synCncfin (synCvv)) (synCnnc))
      (synWex a (synWa (.classMem (synCpw1 (.cv a)) (synCncfin (synC1c)))
          (.classMem (synCpw (.cv a)) (synCncfin (synCvv)))))
      p0003 p0007 p0025
  have p0027 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSfin
      (synCncfin (synC1c)) (synCncfin (synCvv)) a dv_cache_0003 dv_cache_0004
  have p0028 :=
    @gSylibr (.classMem (synCvv) (synCfin))
      (synW3a (.classMem (synCncfin (synC1c)) (synCnnc))
        (.classMem (synCncfin (synCvv)) (synCnnc)) (synWex a
          (synWa (.classMem (synCpw1 (.cv a)) (synCncfin (synC1c)))
            (.classMem (synCpw (.cv a)) (synCncfin (synCvv))))))
      (synWsfin (synCncfin (synC1c)) (synCncfin (synCvv))) p0026 p0027
  exact p0028

/-- Checked nominal proof certificate identified upstream as `g_n_1cspfin`. -/
@[expose]
noncomputable def gN1cspfin :
    Nominal.NPrf
      (.imp (.classMem (synCvv) (synCfin)) (.classMem (synCncfin (synC1c)) (synCspfin))) :=
  by
  have p0000 := @gNcvspfin
  have p0001 := @gN1cvsfin
  have p0002 := @gSpfinsfincl (synCncfin (synCvv)) (synCncfin (synC1c))
  have p0003 :=
    @gSylancr (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCvv)) (synCspfin))
      (synWsfin (synCncfin (synC1c)) (synCncfin (synCvv)))
      (.classMem (synCncfin (synC1c)) (synCspfin)) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_tncveqnc1fin`. -/
@[expose]
noncomputable def gTncveqnc1fin :
    Nominal.NPrf
      (.imp (.classMem (synCvv) (synCfin))
        (.classEq (synCtfin (synCncfin (synCvv))) (synCncfin (synC1c)))) :=
  by
  have p0000 := @gVvex
  have p0001 := @gNcfintfin (synCvv) (synCvv)
  have p0002 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCvv) (synCvv))
      (.classEq (synCtfin (synCncfin (synCvv))) (synCncfin (synCpw1 (synCvv))))
      p0000 p0001
  have p0003 := @gDf1c2
  have p0004 := @gNcfineq (synC1c) (synCpw1 (synCvv))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @gSyl6eqr (.classMem (synCvv) (synCfin)) (synCtfin (synCncfin (synCvv)))
      (synCncfin (synCpw1 (synCvv))) (synCncfin (synC1c)) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_t1csfin1c`. -/
@[expose]
noncomputable def gT1csfin1c :
    Nominal.NPrf
      (.imp (.classMem (synCvv) (synCfin))
        (synWsfin (synCtfin (synCncfin (synC1c))) (synCncfin (synC1c)))) :=
  by
  have p0000 := @gN1cvsfin
  have p0001 := @gSfintfin (synCncfin (synC1c)) (synCncfin (synCvv))
  have p0002 :=
    @gSyl (.classMem (synCvv) (synCfin))
      (synWsfin (synCncfin (synC1c)) (synCncfin (synCvv)))
      (synWsfin (synCtfin (synCncfin (synC1c))) (synCtfin (synCncfin (synCvv))))
      p0000 p0001
  have p0003 := @gTncveqnc1fin
  have p0004 :=
    @gSfineq2 (synCtfin (synCncfin (synCvv))) (synCncfin (synC1c))
      (synCtfin (synCncfin (synC1c)))
  have p0005 :=
    @gSyl (.classMem (synCvv) (synCfin))
      (.classEq (synCtfin (synCncfin (synCvv))) (synCncfin (synC1c)))
      (synWb (synWsfin (synCtfin (synCncfin (synC1c))) (synCtfin (synCncfin (synCvv))))
        (synWsfin (synCtfin (synCncfin (synC1c))) (synCncfin (synC1c))))
      p0003 p0004
  have p0006 :=
    @gMpbid (.classMem (synCvv) (synCfin))
      (synWsfin (synCtfin (synCncfin (synC1c))) (synCtfin (synCncfin (synCvv))))
      (synWsfin (synCtfin (synCncfin (synC1c))) (synCncfin (synC1c))) p0002 p0005
  exact p0006

/-- Checked nominal proof certificate identified upstream as `g_vfintle`. -/
@[expose]
noncomputable def gVfintle (N : Class) :
    Nominal.NPrf
      (.imp (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
          (synWne N (synC0)))
        (.classMem (synCopk (synCtfin N) (synCncfin (synC1c))) (synClefin))) :=
  by
  let proofSupport : Finset Var := N.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (h)
  have dv_cache_0001 : a ∉ (N).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_N, not_false_eq_true])
  have dv_cache_0002 :
    a ∉ ((Wff.classMem (synCopk N (synCncfin (synCvv))) (synClefin))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_clefin, Finset.mem_union,
          fresh_a_not_N, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0003 :
    a ∉ ((synWa (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          fresh_a_not_N, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gN0 a N dv_cache_0001
  have p0001 :=
    @gSimp2 (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (.classMem (.cv a) N)
  have p0002 := @gNcfinprop (.cv a) N
  have p0003 :=
    @gN3adant2 (.classMem (synCvv) (synCfin)) (.classMem (.cv a) N)
      (synWa (.classMem (synCncfin (.cv a)) (synCnnc))
        (.classMem (.cv a) (synCncfin (.cv a))))
      (.classMem N (synCnnc)) p0002
  have p0004 :=
    @gSimpld
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (.classMem (.cv a) N))
      (.classMem (synCncfin (.cv a)) (synCnnc)) (.classMem (.cv a) (synCncfin (.cv a)))
      p0003
  have p0005 :=
    @gSimp3 (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (.classMem (.cv a) N)
  have p0006 :=
    @gSimprd
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (.classMem (.cv a) N))
      (.classMem (synCncfin (.cv a)) (synCnnc)) (.classMem (.cv a) (synCncfin (.cv a)))
      p0003
  have p0007 := @gNnceleq (.cv a) N (synCncfin (.cv a))
  have p0008 :=
    @gSyl22anc
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (.classMem (.cv a) N))
      (.classMem N (synCnnc)) (.classMem (synCncfin (.cv a)) (synCnnc))
      (.classMem (.cv a) N) (.classMem (.cv a) (synCncfin (.cv a)))
      (.classEq N (synCncfin (.cv a))) p0001 p0004 p0005 p0006 p0007
  have p0009 :=
    @gN3expia (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (.classMem (.cv a) N) (.classEq N (synCncfin (.cv a))) p0008
  have p0010 :=
    @gSimpr (.classMem (synCvv) (synCfin)) (.classEq N (synCncfin (.cv a)))
  have p0011 := @gUncompl (.cv a)
  have p0012 := @gNcfineq (synCun (.cv a) (synCcompl (.cv a))) (synCvv)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @gVex a
  have p0015 := @gComplex (.cv a) p0014
  have p0016 := @gIncompl (.cv a)
  have p0017 := @gNcfindi (.cv a) (synCcompl (.cv a)) (synCvv) (synCvv)
  have p0018 :=
    @gMp3an23 (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv a) (synCvv)))
      (.classMem (synCcompl (.cv a)) (synCvv))
      (.classEq (synCin (.cv a) (synCcompl (.cv a))) (synC0))
      (.classEq (synCncfin (synCun (.cv a) (synCcompl (.cv a))))
        (synCplc (synCncfin (.cv a)) (synCncfin (synCcompl (.cv a)))))
      p0015 p0016 p0017
  have p0019 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (.cv a) (synCvv))
      (.classEq (synCncfin (synCun (.cv a) (synCcompl (.cv a))))
        (synCplc (synCncfin (.cv a)) (synCncfin (synCcompl (.cv a)))))
      p0014 p0018
  have p0020 :=
    @gSyl5eqr (.classMem (synCvv) (synCfin)) (synCncfin (synCvv))
      (synCncfin (synCun (.cv a) (synCcompl (.cv a))))
      (synCplc (synCncfin (.cv a)) (synCncfin (synCcompl (.cv a)))) p0013 p0019
  have p0021 :=
    @gAdantr (.classMem (synCvv) (synCfin))
      (.classEq (synCncfin (synCvv))
        (synCplc (synCncfin (.cv a)) (synCncfin (synCcompl (.cv a)))))
      (.classEq N (synCncfin (.cv a))) p0020
  have p0022 :=
    @gOpkeq12d
      (synWa (.classMem (synCvv) (synCfin)) (.classEq N (synCncfin (.cv a)))) N
      (synCncfin (.cv a)) (synCncfin (synCvv))
      (synCplc (synCncfin (.cv a)) (synCncfin (synCcompl (.cv a)))) p0010 p0021
  have p0023 := @gNcfinex (.cv a)
  have p0024 := @gNcfinprop (synCcompl (.cv a)) (synCvv)
  have p0025 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCcompl (.cv a)) (synCvv))
      (synWa (.classMem (synCncfin (synCcompl (.cv a))) (synCnnc))
        (.classMem (synCcompl (.cv a)) (synCncfin (synCcompl (.cv a)))))
      p0015 p0024
  have p0026 :=
    @gSimpld (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCcompl (.cv a))) (synCnnc))
      (.classMem (synCcompl (.cv a)) (synCncfin (synCcompl (.cv a)))) p0025
  have p0027 :=
    @gLefinaddc (synCncfin (.cv a)) (synCncfin (synCcompl (.cv a))) (synCvv)
  have p0028 :=
    @gSylancr (.classMem (synCvv) (synCfin)) (.classMem (synCncfin (.cv a)) (synCvv))
      (.classMem (synCncfin (synCcompl (.cv a))) (synCnnc))
      (.classMem (synCopk (synCncfin (.cv a))
          (synCplc (synCncfin (.cv a)) (synCncfin (synCcompl (.cv a))))) (synClefin))
      p0023 p0026 p0027
  have p0029 :=
    @gAdantr (.classMem (synCvv) (synCfin))
      (.classMem (synCopk (synCncfin (.cv a))
          (synCplc (synCncfin (.cv a)) (synCncfin (synCcompl (.cv a))))) (synClefin))
      (.classEq N (synCncfin (.cv a))) p0028
  have p0030 :=
    @gEqeltrd (synWa (.classMem (synCvv) (synCfin)) (.classEq N (synCncfin (.cv a))))
      (synCopk N (synCncfin (synCvv)))
      (synCopk (synCncfin (.cv a))
        (synCplc (synCncfin (.cv a)) (synCncfin (synCcompl (.cv a)))))
      (synClefin) p0022 p0029
  have p0031 :=
    @gEx (.classMem (synCvv) (synCfin)) (.classEq N (synCncfin (.cv a)))
      (.classMem (synCopk N (synCncfin (synCvv))) (synClefin)) p0030
  have p0032 :=
    @gAdantr (.classMem (synCvv) (synCfin))
      (.imp (.classEq N (synCncfin (.cv a)))
        (.classMem (synCopk N (synCncfin (synCvv))) (synClefin)))
      (.classMem N (synCnnc)) p0031
  have p0033 :=
    @gSyld (synWa (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)))
      (.classMem (.cv a) N) (.classEq N (synCncfin (.cv a)))
      (.classMem (synCopk N (synCncfin (synCvv))) (synClefin)) p0009 p0032
  have p0034 :=
    @gExlimdv (synWa (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)))
      (.classMem (.cv a) N) (.classMem (synCopk N (synCncfin (synCvv))) (synClefin)) a
      dv_cache_0002 dv_cache_0003 p0033
  have p0035 :=
    @gSyl5bi (synWne N (synC0)) (synWex a (.classMem (.cv a) N))
      (synWa (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)))
      (.classMem (synCopk N (synCncfin (synCvv))) (synClefin)) p0000 p0034
  have p0036 :=
    @gN3impia (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (synWne N (synC0)) (.classMem (synCopk N (synCncfin (synCvv))) (synClefin))
      p0035
  have p0037 :=
    @gSimp2 (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (synWne N (synC0))
  have p0038 := @gVvex
  have p0039 := @gNcfinprop (synCvv) (synCvv)
  have p0040 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCvv) (synCvv))
      (synWa (.classMem (synCncfin (synCvv)) (synCnnc))
        (.classMem (synCvv) (synCncfin (synCvv))))
      p0038 p0039
  have p0041 :=
    @gN3ad2ant1 (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (synWa (.classMem (synCncfin (synCvv)) (synCnnc))
        (.classMem (synCvv) (synCncfin (synCvv))))
      (synWne N (synC0)) p0040
  have p0042 :=
    @gSimpld
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classMem (synCncfin (synCvv)) (synCnnc))
      (.classMem (synCvv) (synCncfin (synCvv))) p0041
  have p0043 := @gTfinlefin N (synCncfin (synCvv))
  have p0044 :=
    @gSyl2anc
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classMem N (synCnnc)) (.classMem (synCncfin (synCvv)) (synCnnc))
      (synWb (.classMem (synCopk N (synCncfin (synCvv))) (synClefin))
        (.classMem (synCopk (synCtfin N) (synCtfin (synCncfin (synCvv)))) (synClefin)))
      p0037 p0042 p0043
  have p0045 := @gTncveqnc1fin
  have p0046 :=
    @gN3ad2ant1 (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (.classEq (synCtfin (synCncfin (synCvv))) (synCncfin (synC1c)))
      (synWne N (synC0)) p0045
  have p0047 :=
    @gOpkeq2d
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (synCtfin (synCncfin (synCvv))) (synCncfin (synC1c)) (synCtfin N) p0046
  have p0048 :=
    @gEleq1d
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (synCopk (synCtfin N) (synCtfin (synCncfin (synCvv))))
      (synCopk (synCtfin N) (synCncfin (synC1c))) (synClefin) p0047
  have p0049 :=
    @gBitrd
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classMem (synCopk N (synCncfin (synCvv))) (synClefin))
      (.classMem (synCopk (synCtfin N) (synCtfin (synCncfin (synCvv)))) (synClefin))
      (.classMem (synCopk (synCtfin N) (synCncfin (synC1c))) (synClefin)) p0044 p0048
  have p0050 :=
    @gMpbid
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classMem (synCopk N (synCncfin (synCvv))) (synClefin))
      (.classMem (synCopk (synCtfin N) (synCncfin (synC1c))) (synClefin)) p0036 p0049
  exact p0050

/-- Checked nominal proof certificate identified upstream as `g_vfin1cltv`. -/
@[expose]
noncomputable def gVfin1cltv :
    Nominal.NPrf
      (.imp (.classMem (synCvv) (synCfin))
        (.classMem (synCopk (synCncfin (synC1c)) (synCncfin (synCvv))) (synCltfin))) :=
  by
  have p0000 := @gUncompl (synC1c)
  have p0001 := @gNcfineq (synCun (synC1c) (synCcompl (synC1c))) (synCvv)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @gN1cex
  have p0005 := @gComplex (synC1c) p0003
  have p0006 := @gIncompl (synC1c)
  have p0007 := @gNcfindi (synC1c) (synCcompl (synC1c)) (synCvv) (synCvv)
  have p0008 :=
    @gMp3an23 (synWa (.classMem (synCvv) (synCfin)) (.classMem (synC1c) (synCvv)))
      (.classMem (synCcompl (synC1c)) (synCvv))
      (.classEq (synCin (synC1c) (synCcompl (synC1c))) (synC0))
      (.classEq (synCncfin (synCun (synC1c) (synCcompl (synC1c))))
        (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
      p0005 p0006 p0007
  have p0009 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synC1c) (synCvv))
      (.classEq (synCncfin (synCun (synC1c) (synCcompl (synC1c))))
        (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
      p0003 p0008
  have p0010 :=
    @gSyl5reqr (.classMem (synCvv) (synCfin)) (synCncfin (synCvv))
      (synCncfin (synCun (synC1c) (synCcompl (synC1c))))
      (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))) p0002 p0009
  have p0011 :=
    @gOpkeq2d (.classMem (synCvv) (synCfin))
      (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))
      (synCncfin (synCvv)) (synCncfin (synC1c)) p0010
  have p0012 := @gN0nel1c
  have p0013 := @gN0ex
  have p0014 := @gElcompl (synC0) (synC1c) p0013
  have p0015 :=
    @gMpbir (.classMem (synC0) (synCcompl (synC1c)))
      (.neg (.classMem (synC0) (synC1c))) p0012 p0014
  have p0016 := @gN0i (synCcompl (synC1c)) (synC0)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @gNcfinprop (synCcompl (synC1c)) (synCvv)
  have p0019 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCcompl (synC1c)) (synCvv))
      (synWa (.classMem (synCncfin (synCcompl (synC1c))) (synCnnc))
        (.classMem (synCcompl (synC1c)) (synCncfin (synCcompl (synC1c)))))
      p0005 p0018
  have p0020 :=
    @gSimprd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCcompl (synC1c))) (synCnnc))
      (.classMem (synCcompl (synC1c)) (synCncfin (synCcompl (synC1c)))) p0019
  have p0021 :=
    @gEleq2 (synC0c) (synCncfin (synCcompl (synC1c))) (synCcompl (synC1c))
  have p0022 :=
    @gSyl5ibrcom (.classMem (synCvv) (synCfin))
      (.classMem (synCcompl (synC1c)) (synC0c))
      (.classEq (synC0c) (synCncfin (synCcompl (synC1c))))
      (.classMem (synCcompl (synC1c)) (synCncfin (synCcompl (synC1c)))) p0020 p0021
  have p0023 := @gEl0c (synCcompl (synC1c))
  have p0024 :=
    @gSyl6ib (.classMem (synCvv) (synCfin))
      (.classEq (synC0c) (synCncfin (synCcompl (synC1c))))
      (.classMem (synCcompl (synC1c)) (synC0c))
      (.classEq (synCcompl (synC1c)) (synC0)) p0022 p0023
  have p0025 :=
    @gMtoi (.classMem (synCvv) (synCfin))
      (.classEq (synC0c) (synCncfin (synCcompl (synC1c))))
      (.classEq (synCcompl (synC1c)) (synC0)) p0017 p0024
  have p0026 := @gAddcid1 (synCncfin (synC1c))
  have p0027 :=
    @gEqeq1i (synCplc (synCncfin (synC1c)) (synC0c)) (synCncfin (synC1c))
      (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))) p0026
  have p0029 := @gNcfinprop (synC1c) (synCvv)
  have p0030 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synC1c) (synCvv))
      (synWa (.classMem (synCncfin (synC1c)) (synCnnc))
        (.classMem (synC1c) (synCncfin (synC1c))))
      p0003 p0029
  have p0031 :=
    @gSimpld (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synC1c)) (synCnnc))
      (.classMem (synC1c) (synCncfin (synC1c))) p0030
  have p0032 := @gPeano1
  have p0033 :=
    @gA1i (.classMem (synC0c) (synCnnc)) (.classMem (synCvv) (synCfin)) p0032
  have p0034 :=
    @gSimpld (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCcompl (synC1c))) (synCnnc))
      (.classMem (synCcompl (synC1c)) (synCncfin (synCcompl (synC1c)))) p0019
  have p0035 :=
    @gA1i (.classEq (synCplc (synCncfin (synC1c)) (synC0c)) (synCncfin (synC1c)))
      (.classMem (synCvv) (synCfin)) p0026
  have p0036 :=
    @gSimprd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synC1c)) (synCnnc))
      (.classMem (synC1c) (synCncfin (synC1c))) p0030
  have p0037 := @gNe0i (synCncfin (synC1c)) (synC1c)
  have p0038 :=
    @gSyl (.classMem (synCvv) (synCfin)) (.classMem (synC1c) (synCncfin (synC1c)))
      (synWne (synCncfin (synC1c)) (synC0)) p0036 p0037
  have p0039 :=
    @gEqnetrd (.classMem (synCvv) (synCfin))
      (synCplc (synCncfin (synC1c)) (synC0c)) (synCncfin (synC1c)) (synC0) p0035
      p0038
  have p0040 :=
    @gPreaddccan2 (synCncfin (synCcompl (synC1c))) (synCncfin (synC1c)) (synC0c)
  have p0041 :=
    @gSyl31anc (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synC1c)) (synCnnc)) (.classMem (synC0c) (synCnnc))
      (.classMem (synCncfin (synCcompl (synC1c))) (synCnnc))
      (synWne (synCplc (synCncfin (synC1c)) (synC0c)) (synC0))
      (synWb (.classEq (synCplc (synCncfin (synC1c)) (synC0c))
          (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
        (.classEq (synC0c) (synCncfin (synCcompl (synC1c)))))
      p0031 p0033 p0034 p0039 p0040
  have p0042 :=
    @gSyl5bbr
      (.classEq (synCncfin (synC1c))
        (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
      (.classEq (synCplc (synCncfin (synC1c)) (synC0c))
        (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
      (.classMem (synCvv) (synCfin))
      (.classEq (synC0c) (synCncfin (synCcompl (synC1c)))) p0027 p0041
  have p0043 :=
    @gMtbird (.classMem (synCvv) (synCfin))
      (.classEq (synCncfin (synC1c))
        (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
      (.classEq (synC0c) (synCncfin (synCcompl (synC1c)))) p0025 p0042
  have p0044 := @gNcfinex (synC1c)
  have p0045 :=
    @gLefinaddc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))) (synCvv)
  have p0046 :=
    @gSylancr (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synC1c)) (synCvv))
      (.classMem (synCncfin (synCcompl (synC1c))) (synCnnc))
      (.classMem (synCopk (synCncfin (synC1c))
          (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))) (synClefin))
      p0044 p0034 p0045
  have p0047 := @gNcfinex (synCcompl (synC1c))
  have p0048 :=
    @gAddcex (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))) p0044 p0047
  have p0049 :=
    @gLefinlteq (synCncfin (synC1c))
      (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))) (synCvv)
      (synCvv)
  have p0050 :=
    @gMp3an12 (.classMem (synCncfin (synC1c)) (synCvv))
      (.classMem (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))
        (synCvv))
      (synWne (synCncfin (synC1c)) (synC0))
      (synWb (.classMem (synCopk (synCncfin (synC1c))
            (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))) (synClefin))
        (synWo (.classMem (synCopk (synCncfin (synC1c))
              (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
            (synCltfin)) (.classEq (synCncfin (synC1c))
            (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))))
      p0044 p0048 p0049
  have p0051 :=
    @gSyl (.classMem (synCvv) (synCfin)) (synWne (synCncfin (synC1c)) (synC0))
      (synWb (.classMem (synCopk (synCncfin (synC1c))
            (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))) (synClefin))
        (synWo (.classMem (synCopk (synCncfin (synC1c))
              (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
            (synCltfin)) (.classEq (synCncfin (synC1c))
            (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))))
      p0038 p0050
  have p0052 :=
    @gMpbid (.classMem (synCvv) (synCfin))
      (.classMem (synCopk (synCncfin (synC1c))
          (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))) (synClefin))
      (synWo (.classMem (synCopk (synCncfin (synC1c))
            (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))) (synCltfin))
        (.classEq (synCncfin (synC1c))
          (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))))
      p0046 p0051
  have p0053 :=
    @gOrcomd (.classMem (synCvv) (synCfin))
      (.classMem (synCopk (synCncfin (synC1c))
          (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))) (synCltfin))
      (.classEq (synCncfin (synC1c))
        (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
      p0052
  have p0054 :=
    @gOrd (.classMem (synCvv) (synCfin))
      (.classEq (synCncfin (synC1c))
        (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
      (.classMem (synCopk (synCncfin (synC1c))
          (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))) (synCltfin))
      p0053
  have p0055 :=
    @gMpd (.classMem (synCvv) (synCfin))
      (.neg (.classEq (synCncfin (synC1c))
          (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))))
      (.classMem (synCopk (synCncfin (synC1c))
          (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c))))) (synCltfin))
      p0043 p0054
  have p0056 :=
    @gEqeltrrd (.classMem (synCvv) (synCfin))
      (synCopk (synCncfin (synC1c))
        (synCplc (synCncfin (synC1c)) (synCncfin (synCcompl (synC1c)))))
      (synCopk (synCncfin (synC1c)) (synCncfin (synCvv))) (synCltfin) p0011 p0055
  exact p0056

/-- Checked nominal proof certificate identified upstream as `g_vfinncvntnn`. -/
@[expose]
noncomputable def gVfinncvntnn (N : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)))
        (synWne (synCtfin N) (synCncfin (synCvv)))) :=
  by
  let proofSupport : Finset Var := N.fv
  let a : Var := freshVar proofSupport 0
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_a_not_N : a ∉ N.fv := by
    intro h
    exact fresh_a (h)
  have dv_cache_0001 : a ∉ (N).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_a_not_N, not_false_eq_true])
  have p0000 := @gVvex
  have p0001 := @gNcfinprop (synCvv) (synCvv)
  have p0002 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCvv) (synCvv))
      (synWa (.classMem (synCncfin (synCvv)) (synCnnc))
        (.classMem (synCvv) (synCncfin (synCvv))))
      p0000 p0001
  have p0003 :=
    @gSimprd (.classMem (synCvv) (synCfin))
      (.classMem (synCncfin (synCvv)) (synCnnc))
      (.classMem (synCvv) (synCncfin (synCvv))) p0002
  have p0004 := @gNe0i (synCncfin (synCvv)) (synCvv)
  have p0005 :=
    @gSyl (.classMem (synCvv) (synCfin)) (.classMem (synCvv) (synCncfin (synCvv)))
      (synWne (synCncfin (synCvv)) (synC0)) p0003 p0004
  have p0006 :=
    @gNecomd (.classMem (synCvv) (synCfin)) (synCncfin (synCvv)) (synC0) p0005
  have p0007 := @gTfineq N (synC0)
  have p0008 := @gTfinnul
  have p0009 :=
    @gSyl6eq (.classEq N (synC0)) (synCtfin N) (synCtfin (synC0)) (synC0) p0007
      p0008
  have p0010 :=
    @gNeeq1d (.classEq N (synC0)) (synCtfin N) (synC0) (synCncfin (synCvv)) p0009
  have p0011 :=
    @gSyl5ibr (.classMem (synCvv) (synCfin))
      (synWne (synCtfin N) (synCncfin (synCvv))) (.classEq N (synC0))
      (synWne (synC0) (synCncfin (synCvv))) p0006 p0010
  have p0012 :=
    @gAdantrd (.classEq N (synC0)) (.classMem (synCvv) (synCfin))
      (synWne (synCtfin N) (synCncfin (synCvv))) (.classMem N (synCnnc)) p0011
  have p0014 :=
    @gSimpld (synWa (.classMem (synCvv) (synCfin)) (.classMem (synCvv) (synCvv)))
      (.classMem (synCncfin (synCvv)) (synCnnc))
      (.classMem (synCvv) (synCncfin (synCvv))) p0001
  have p0015 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synCvv) (synCvv))
      (.classMem (synCncfin (synCvv)) (synCnnc)) p0000 p0014
  have p0016 := @gLtfinirr (synCncfin (synCvv))
  have p0017 :=
    @gSyl (.classMem (synCvv) (synCfin)) (.classMem (synCncfin (synCvv)) (synCnnc))
      (.neg (.classMem (synCopk (synCncfin (synCvv)) (synCncfin (synCvv))) (synCltfin)))
      p0015 p0016
  have p0018 :=
    @gN3ad2ant1 (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (.neg (.classMem (synCopk (synCncfin (synCvv)) (synCncfin (synCvv))) (synCltfin)))
      (synWne N (synC0)) p0017
  have p0019 := @gVfintle N
  have p0020 := @gVfin1cltv
  have p0021 :=
    @gN3ad2ant1 (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (.classMem (synCopk (synCncfin (synC1c)) (synCncfin (synCvv))) (synCltfin))
      (synWne N (synC0)) p0020
  have p0022 := @gTfinprop N a dv_cache_0001
  have p0023 :=
    @gSimpld (synWa (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classMem (synCtfin N) (synCnnc))
      (synWrex a N (.classMem (synCpw1 (.cv a)) (synCtfin N))) p0022
  have p0024 :=
    @gN3adant1 (.classMem N (synCnnc)) (synWne N (synC0))
      (.classMem (synCtfin N) (synCnnc)) (.classMem (synCvv) (synCfin)) p0023
  have p0025 := @gN1cex
  have p0026 := @gNcfinprop (synC1c) (synCvv)
  have p0027 :=
    @gSimpld (synWa (.classMem (synCvv) (synCfin)) (.classMem (synC1c) (synCvv)))
      (.classMem (synCncfin (synC1c)) (synCnnc))
      (.classMem (synC1c) (synCncfin (synC1c))) p0026
  have p0028 :=
    @gMpan2 (.classMem (synCvv) (synCfin)) (.classMem (synC1c) (synCvv))
      (.classMem (synCncfin (synC1c)) (synCnnc)) p0025 p0027
  have p0029 :=
    @gN3ad2ant1 (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (.classMem (synCncfin (synC1c)) (synCnnc)) (synWne N (synC0)) p0028
  have p0030 :=
    @gN3ad2ant1 (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (.classMem (synCncfin (synCvv)) (synCnnc)) (synWne N (synC0)) p0015
  have p0031 := @gLeltfintr (synCtfin N) (synCncfin (synC1c)) (synCncfin (synCvv))
  have p0032 :=
    @gSyl3anc
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classMem (synCtfin N) (synCnnc)) (.classMem (synCncfin (synC1c)) (synCnnc))
      (.classMem (synCncfin (synCvv)) (synCnnc))
      (.imp (synWa (.classMem (synCopk (synCtfin N) (synCncfin (synC1c))) (synClefin))
          (.classMem (synCopk (synCncfin (synC1c)) (synCncfin (synCvv))) (synCltfin)))
        (.classMem (synCopk (synCtfin N) (synCncfin (synCvv))) (synCltfin)))
      p0024 p0029 p0030 p0031
  have p0033 :=
    @gMp2and
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classMem (synCopk (synCtfin N) (synCncfin (synC1c))) (synClefin))
      (.classMem (synCopk (synCncfin (synC1c)) (synCncfin (synCvv))) (synCltfin))
      (.classMem (synCopk (synCtfin N) (synCncfin (synCvv))) (synCltfin)) p0019 p0021
      p0032
  have p0034 := @gOpkeq1 (synCtfin N) (synCncfin (synCvv)) (synCncfin (synCvv))
  have p0035 :=
    @gEleq1d (.classEq (synCtfin N) (synCncfin (synCvv)))
      (synCopk (synCtfin N) (synCncfin (synCvv)))
      (synCopk (synCncfin (synCvv)) (synCncfin (synCvv))) (synCltfin) p0034
  have p0036 :=
    @gSyl5ibcom
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classMem (synCopk (synCtfin N) (synCncfin (synCvv))) (synCltfin))
      (.classEq (synCtfin N) (synCncfin (synCvv)))
      (.classMem (synCopk (synCncfin (synCvv)) (synCncfin (synCvv))) (synCltfin))
      p0033 p0035
  have p0037 :=
    @gMtod
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (.classEq (synCtfin N) (synCncfin (synCvv)))
      (.classMem (synCopk (synCncfin (synCvv)) (synCncfin (synCvv))) (synCltfin))
      p0018 p0036
  have p0038 := (Nominal.biimpRefl (synWne (synCtfin N) (synCncfin (synCvv))))
  have p0039 :=
    @gSylibr
      (synW3a (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)) (synWne N (synC0)))
      (.neg (.classEq (synCtfin N) (synCncfin (synCvv))))
      (synWne (synCtfin N) (synCncfin (synCvv))) p0037 p0038
  have p0040 :=
    @gN3expa (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc))
      (synWne N (synC0)) (synWne (synCtfin N) (synCncfin (synCvv))) p0039
  have p0041 :=
    @gExpcom (synWa (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)))
      (synWne N (synC0)) (synWne (synCtfin N) (synCncfin (synCvv))) p0040
  have p0042 :=
    @gPm261ine
      (.imp (synWa (.classMem (synCvv) (synCfin)) (.classMem N (synCnnc)))
        (synWne (synCtfin N) (synCncfin (synCvv))))
      N (synC0) p0012 p0041
  exact p0042

/-- Checked nominal proof certificate identified upstream as `g_vfinncvntsp`. -/
@[expose]
noncomputable def gVfinncvntsp (x : Var) (a : Var) (dv_a_x : a ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (synCvv) (synCfin)) (.neg (.classMem (synCncfin (synCvv)) (.cab a
              (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x)))))))) :=
  by
  have dv_cache_0001 : x ∉ ((Wff.classMem (synCvv) (synCfin))).fv := by
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
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv a) (synCncfin (synCvv)))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, (Ne.symm dv_a_x), compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0003 : a ∉ ((synCncfin (synCvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0004 :
    a ∉
      ((synWrex x (synCspfin) (.classEq (synCncfin (synCvv)) (synCtfin (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cspfin,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cncfin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ctfin,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, dv_a_x, compact_fv_not_mem_empty, or_false, and_false,
          not_false_eq_true])
  have p0000 := @gVfinspnn
  have p0001 := @gDifss (synCnnc) (synCsn (synC0))
  have p0002 :=
    @gSyl6ss (.classMem (synCvv) (synCfin)) (synCspfin)
      (synCdif (synCnnc) (synCsn (synC0))) (synCnnc) p0000 p0001
  have p0003 :=
    @gSselda (.classMem (synCvv) (synCfin)) (synCspfin) (synCnnc) (.cv x) p0002
  have p0004 := @gVfinncvntnn (.cv x)
  have p0005 :=
    @gSyldan (.classMem (synCvv) (synCfin)) (.classMem (.cv x) (synCspfin))
      (.classMem (.cv x) (synCnnc)) (synWne (synCtfin (.cv x)) (synCncfin (synCvv)))
      p0003 p0004
  have p0006 :=
    @gNecomd (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv x) (synCspfin)))
      (synCtfin (.cv x)) (synCncfin (synCvv)) p0005
  have p0007 := (Nominal.biimpRefl (synWne (synCncfin (synCvv)) (synCtfin (.cv x))))
  have p0008 :=
    @gSylib (synWa (.classMem (synCvv) (synCfin)) (.classMem (.cv x) (synCspfin)))
      (synWne (synCncfin (synCvv)) (synCtfin (.cv x)))
      (.neg (.classEq (synCncfin (synCvv)) (synCtfin (.cv x)))) p0006 p0007
  have p0009 :=
    @gNrexdv (.classMem (synCvv) (synCfin))
      (.classEq (synCncfin (synCvv)) (synCtfin (.cv x))) x (synCspfin) dv_cache_0001
      p0008
  have p0010 := @gNcfinex (synCvv)
  have p0011 := @gEqeq1 (.cv a) (synCncfin (synCvv)) (synCtfin (.cv x))
  have p0012 :=
    @gRexbidv (.classEq (.cv a) (synCncfin (synCvv)))
      (.classEq (.cv a) (synCtfin (.cv x)))
      (.classEq (synCncfin (synCvv)) (synCtfin (.cv x))) x (synCspfin) dv_cache_0002
      p0011
  have p0013 :=
    @gElab (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))
      (synWrex x (synCspfin) (.classEq (synCncfin (synCvv)) (synCtfin (.cv x)))) a
      (synCncfin (synCvv)) dv_cache_0003 dv_cache_0004 p0010 p0012
  have p0014 :=
    @gSylnibr (.classMem (synCvv) (synCfin))
      (synWrex x (synCspfin) (.classEq (synCncfin (synCvv)) (synCtfin (.cv x))))
      (.classMem (synCncfin (synCvv))
        (.cab a (synWrex x (synCspfin) (.classEq (.cv a) (synCtfin (.cv x))))))
      p0009 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay

end
