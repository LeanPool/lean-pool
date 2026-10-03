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

@[expose]
noncomputable def g_spfinex : Nominal.NPrf (.classMem (syn_cspfin) (syn_cvv)) :=
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
      ((syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                          (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
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
  have dv_cache_0005 : t ∉ ((syn_c1c)).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
                (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                        (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
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
  have dv_cache_0009 : t ∉ ((syn_csn (.cv x))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak
              (syn_cdif (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc))
                      (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
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
      ((syn_cdif (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                  (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cins2k (syn_cssetk)))).fv :=
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
  have dv_cache_0012 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
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
  have dv_cache_0013 : t ∉ ((syn_copk (syn_csn (.cv x)) (.cv a))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
            (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cins2k (syn_cssetk))))).fv :=
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
  have dv_cache_0016 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv z))))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
            (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k (syn_csik
                (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                        (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cins2k (syn_cssetk))))).fv :=
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
      ((syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                              (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_c1c)))).fv :=
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
  have dv_cache_0019 : a ∉ ((syn_cncfin (syn_cvv))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_spfin x z a
      dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0001 := @g_vex a
  have p0002 :=
    @g_elimak t
      (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                        (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_c1c) (.cv a) dv_cache_0004 dv_cache_0005 dv_cache_0006 p0001
  have p0003 := @g_el1c x (.cv t) dv_cache_0007
  have p0004 :=
    @g_anbi1i (.classMem (.cv t) (syn_c1c))
      (syn_wex x (.classEq (.cv t) (syn_csn (.cv x))))
      (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0003
  have p0005 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (.cv x)))
      (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      x dv_cache_0008
  have p0006 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (.cv x))))
        (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
                (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                        (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
                  (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                          (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0004 p0005
  have p0007 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
                  (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                          (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      t p0006
  have p0008 :=
    (Nominal.biimpRefl (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  have p0009 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (.cv x))) (.classMem (syn_copk (.cv t) (.cv a))
          (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      x t
  have p0010 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_c1c)) (.classMem (syn_copk (.cv t) (.cv a))
            (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                              (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
                    (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                            (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak
                                  (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk)
            (syn_cimak (syn_cdif (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc))
                      (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
                    (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                            (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak
                                  (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0007 p0008 p0009
  have p0011 := @g_snex (.cv x)
  have p0012 := @g_opkeq1 (.cv t) (syn_csn (.cv x)) (.cv a)
  have p0013 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (.cv x))) (syn_copk (.cv t) (.cv a))
      (syn_copk (syn_csn (.cv x)) (.cv a))
      (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                        (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0012
  have p0014 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      t (syn_csn (.cv x)) dv_cache_0009 dv_cache_0010 p0011 p0013
  have p0015 :=
    @g_elin (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk)
      (syn_cimak (syn_cdif (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc))
                (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
  have p0016 := @g_vex x
  have p0017 := @g_elssetk (.cv x) (.cv a) p0016 p0001
  have p0018 := @g_opkex (syn_csn (.cv x)) (.cv a)
  have p0019 :=
    @g_elimak t
      (syn_cdif (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                            (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (syn_csn (.cv x)) (.cv a)) dv_cache_0011
      dv_cache_0012 dv_cache_0013 p0018
  have p0020 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k
              (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))))
  have p0021 := @g_elpw121c z (.cv t) dv_cache_0014
  have p0022 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k
            (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))
      p0021
  have p0023 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k
            (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))
      z dv_cache_0015
  have p0024 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k
              (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))
      (syn_wa (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k
              (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cins2k (syn_cssetk))))))
      p0022 p0023
  have p0025 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k
              (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cins2k (syn_cssetk))))))
      t p0024
  have p0026 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k
              (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))
      z t
  have p0027 :=
    @g_bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cins2k (syn_cssetk))))))
      (syn_wex t (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
                (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                        (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk)))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
                (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                        (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk)))))))
      p0025 p0026
  have p0028 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                        (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k
              (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))))
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cins2k (syn_cssetk))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
                (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                        (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk)))))))
      p0019 p0020 p0027
  have p0029 := @g_snex (syn_csn (syn_csn (.cv z)))
  have p0030 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv z))))
      (syn_copk (syn_csn (.cv x)) (.cv a))
  have p0031 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
      (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a)))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn (.cv x)) (.cv a)))
      (syn_cdif (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                            (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
      p0030
  have p0032 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k
            (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k (syn_csik
              (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))
      t (syn_csn (syn_csn (syn_csn (.cv z)))) dv_cache_0016 dv_cache_0017 p0029 p0031
  have p0033 :=
    @g_eldif
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv z)))) (syn_copk (syn_csn (.cv x)) (.cv a)))
      (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                          (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cins2k (syn_cssetk))
  have p0034 := @g_snex (.cv z)
  have p0035 :=
    @g_otkelins3k (syn_csn (.cv z)) (syn_csn (.cv x)) (.cv a)
      (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                (syn_cimak (syn_cin (syn_cins3k (syn_csik
                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                            (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0034 p0011 p0001
  have p0036 := @g_vex z
  have p0037 :=
    @g_opksnelsik (.cv z) (.cv x)
      (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak
                (syn_cin (syn_cins3k (syn_csik
                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                          (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
              (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0036 p0016
  have p0038 := @g_srelk (.cv z) (.cv x) p0036 p0016
  have p0039 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cins3k (syn_csik
            (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak
                      (syn_cin (syn_cins3k (syn_csik
                            (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (.cv z)) (syn_csn (.cv x))) (syn_csik
          (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak
                    (syn_cin (syn_cins3k (syn_csik
                          (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (.cv z) (.cv x)) (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
            (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                            (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wsfin (.cv z) (.cv x)) p0035 p0037 p0038
  have p0040 :=
    @g_otkelins2k (syn_csn (.cv z)) (syn_csn (.cv x)) (.cv a) (syn_cssetk) p0034 p0011
      p0001
  have p0041 := @g_elssetk (.cv z) (.cv a) p0036 p0001
  have p0042_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv z)) (.cv a)) (syn_cssetk)) (.objMem z a)) :=
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
      p0041
  have p0042 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv z)) (.cv a)) (syn_cssetk)) (.objMem z a) p0040
      p0042_e01_recanon
  have p0043 :=
    @g_notbii
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cins2k (syn_cssetk)))
      (.objMem z a) p0042
  have p0044 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cins3k (syn_csik
            (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak
                      (syn_cin (syn_cins3k (syn_csik
                            (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wsfin (.cv z) (.cv x))
      (.neg (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
            (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cins2k (syn_cssetk))))
      (.neg (.objMem z a)) p0039 p0043
  have p0045 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cins2k (syn_cssetk))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
          (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif (syn_cins3k (syn_csik
              (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
            (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cins3k (syn_csik
              (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                      (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.neg (.classMem
            (syn_copk (syn_csn (syn_csn (syn_csn (.cv z))))
              (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cins2k (syn_cssetk)))))
      (syn_wa (syn_wsfin (.cv z) (.cv x)) (.neg (.objMem z a))) p0032 p0033 p0044
  have p0046 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cins2k (syn_cssetk))))))
      (syn_wa (syn_wsfin (.cv z) (.cv x)) (.neg (.objMem z a))) z p0045
  have p0047 := @g_exanali (syn_wsfin (.cv z) (.cv x)) (.objMem z a) z
  have p0048 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                        (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv z)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv x)) (.cv a))) (syn_cdif
                (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                        (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk)))))))
      (syn_wex z (syn_wa (syn_wsfin (.cv z) (.cv x)) (.neg (.objMem z a))))
      (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))) p0028 p0046 p0047
  have p0049_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk)) (.objMem x a)) :=
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
      p0017
  have p0049 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk)) (.objMem x a)
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                        (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))) p0049_e00_recanon
      p0048
  have p0050 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
                  (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                          (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
              (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                      (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wa (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk))
        (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cimak (syn_cdif (syn_cins3k
                (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wa (.objMem x a) (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))
      p0014 p0015 p0049
  have p0051 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
          (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
                  (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                          (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wa (.objMem x a) (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))
      x p0050
  have p0052 :=
    @g_n_3bitri
      (.classMem (.cv a) (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k
                  (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                          (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c)))
      (syn_wrex t (syn_c1c) (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk)
            (syn_cimak (syn_cdif (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc))
                      (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (.cv x)))
            (.classMem (syn_copk (.cv t) (.cv a)) (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
                    (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                            (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak
                                  (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wex x (syn_wa (.objMem x a)
          (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))
      p0002 p0010 p0051
  have p0053 :=
    (Nominal.biimpRefl (syn_wrex x (.cv a)
        (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))
  have p0054_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex x (.cv a)
          (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))) (syn_wex x
          (syn_wa (.objMem x a)
            (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_wsfin, syn_w3a, syn_cnnc,
          syn_cint]
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
    @g_bitr4i
      (.classMem (.cv a) (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k
                  (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                          (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c)))
      (syn_wex x (syn_wa (.objMem x a)
          (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))
      (syn_wrex x (.cv a) (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))
      p0052 p0054_e01_recanon
  have p0055 :=
    @g_notbii
      (.classMem (.cv a) (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k
                  (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                          (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c)))
      (syn_wrex x (.cv a) (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))
      p0054
  have p0056 :=
    @g_elcompl (.cv a)
      (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                          (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c))
      p0001
  have p0057 :=
    @g_dfral2 (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))) x (.cv a)
  have p0058 :=
    @g_n_3bitr4i
      (.neg (.classMem (.cv a) (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k
                    (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                            (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c))))
      (.neg (syn_wrex x (.cv a)
          (.neg (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))
      (.classMem (.cv a) (syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif
                  (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                          (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c))))
      (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))) p0055
      p0056 p0057
  have p0059 :=
    @g_eqabi
      (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))) a
      (syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c)))
      dv_cache_0018 p0058
  have p0060 :=
    @g_ineq2i
      (syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c)))
      (.cab a (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))
      (.cab a (.classMem (syn_cncfin (syn_cvv)) (.cv a))) p0059
  have p0061 :=
    @g_inab (.classMem (syn_cncfin (syn_cvv)) (.cv a))
      (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))) a
  have p0062 :=
    @g_eqtri
      (syn_cin (.cab a (.classMem (syn_cncfin (syn_cvv)) (.cv a))) (syn_ccompl (syn_cimak
            (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                              (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c))))
      (syn_cin (.cab a (.classMem (syn_cncfin (syn_cvv)) (.cv a))) (.cab a
          (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))
      (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
          (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))
      p0060 p0061
  have p0063 :=
    @g_inteqi
      (syn_cin (.cab a (.classMem (syn_cncfin (syn_cvv)) (.cv a))) (syn_ccompl (syn_cimak
            (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                              (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c))))
      (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
          (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))
      p0062
  have p0064 :=
    @g_eqtr4i (syn_cspfin)
      (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a)
              (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))))
      (syn_cint (syn_cin (.cab a (.classMem (syn_cncfin (syn_cvv)) (.cv a))) (syn_ccompl
            (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                        (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                              (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak
                                  (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c)))))
      p0000 p0063
  have p0065 := @g_setswithex a (syn_cncfin (syn_cvv)) dv_cache_0019
  have p0066 := @g_ssetkex
  have p0067 := @g_srelkex
  have p0068 :=
    @g_sikex
      (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k (syn_cimak
                (syn_cin (syn_cins3k (syn_csik
                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                          (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
              (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins3k (syn_cssetk))
                            (syn_cins2k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0067
  have p0069 :=
    @g_ins3kex
      (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                (syn_cimak (syn_cin (syn_cins3k (syn_csik
                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                            (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins3k (syn_cssetk))
                              (syn_cins2k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0068
  have p0071 := @g_ins2kex (syn_cssetk) p0066
  have p0072 :=
    @g_difex
      (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                          (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins3k (syn_cssetk))
                                (syn_cins2k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cins2k (syn_cssetk)) p0069 p0071
  have p0073 := @g_n_1cex
  have p0074 := @g_pw1ex (syn_c1c) p0073
  have p0075 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0074
  have p0076 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak
                (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                            (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0072 p0075
  have p0077 :=
    @g_inex (syn_cssetk)
      (syn_cimak (syn_cdif (syn_cins3k (syn_csik (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc))
                (syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                              (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0066 p0076
  have p0079 :=
    @g_imakex
      (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                        (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_c1c) p0077 p0073
  have p0080 :=
    @g_complex
      (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                  (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                          (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                  (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv)) (syn_cimak
                                      (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c))
      p0079
  have p0081 :=
    @g_inex (.cab a (.classMem (syn_cncfin (syn_cvv)) (.cv a)))
      (syn_ccompl (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                    (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                            (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                    (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c)))
      p0065 p0080
  have p0082 :=
    @g_intex
      (syn_cin (.cab a (.classMem (syn_cncfin (syn_cvv)) (.cv a))) (syn_ccompl (syn_cimak
            (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                      (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin (syn_cins3k
                              (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                      (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cins2k (syn_cimak (syn_cin (syn_cins3k (syn_csik (syn_ccompl
                                        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c))))
      p0081
  have p0083 :=
    @g_eqeltri (syn_cspfin)
      (syn_cint (syn_cin (.cab a (.classMem (syn_cncfin (syn_cvv)) (.cv a))) (syn_ccompl
            (syn_cimak (syn_cin (syn_cssetk) (syn_cimak (syn_cdif (syn_cins3k (syn_csik
                        (syn_cin (syn_cxpk (syn_cnnc) (syn_cnnc)) (syn_cimak (syn_cin
                              (syn_cins3k (syn_cimak (syn_cin (syn_cins3k (syn_csik
                                        (syn_cdif (syn_cxpk (syn_cpw (syn_c1c)) (syn_cvv))
        (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins2k (syn_cimak
                                  (syn_cin (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_c1c)))))
      (syn_cvv) p0064 p0082
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

@[expose]
noncomputable def g_ncvspfin :
    Nominal.NPrf (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin)) :=
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
  have dv_cache_0001 : a ∉ ((syn_cncfin (syn_cvv))).fv := by
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
  have p0000 := @g_ncfinex (syn_cvv)
  have p0001 :=
    @g_elintab
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
        (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))
      a (syn_cncfin (syn_cvv)) dv_cache_0001 p0000
  have p0002 :=
    @g_simpl (.classMem (syn_cncfin (syn_cvv)) (.cv a))
      (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))
  have p0003 :=
    @g_mpgbir
      (.classMem (syn_cncfin (syn_cvv)) (syn_cint (.cab a
            (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a)
                (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))))
      (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
          (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))
        (.classMem (syn_cncfin (syn_cvv)) (.cv a)))
      a p0001 p0002
  have p0004 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_spfin x z a
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0005 :=
    @g_eleqtrri (syn_cncfin (syn_cvv))
      (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a)
              (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))))
      (syn_cspfin) p0003 p0004
  exact p0005

@[expose]
noncomputable def g_spfinsfincl (X : Class) (Z : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem X (syn_cspfin)) (syn_wsfin Z X)) (.classMem Z (syn_cspfin))) :=
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
    p ∉ ((Wff.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a)))).fv :=
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
  have dv_cache_0007 : q ∉ ((Wff.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))).fv :=
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
  have dv_cache_0008 : a ∉ ((syn_wsfin (.cv z) (.cv x))).fv :=
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
      ((Wff.imp (syn_wsfin Z X)
          (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin))))).fv :=
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
      ((Wff.imp (syn_wsfin Z (.cv x))
          (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem Z (syn_cspfin))))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin Z X y
      dv_cache_0001 dv_cache_0002
  have p0001 := @g_sfineq1 (.cv z) Z (.cv x)
  have p0002 := @g_eleq1 (.cv z) Z (syn_cspfin)
  have p0003 :=
    @g_imbi2d (.classEq (.cv z) Z) (.classMem (.cv z) (syn_cspfin))
      (.classMem Z (syn_cspfin)) (.classMem (.cv x) (syn_cspfin)) p0002
  have p0004 :=
    @g_imbi12d (.classEq (.cv z) Z) (syn_wsfin (.cv z) (.cv x)) (syn_wsfin Z (.cv x))
      (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv z) (syn_cspfin)))
      (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem Z (syn_cspfin))) p0001 p0003
  have p0005 := @g_sfineq2 (.cv x) X Z
  have p0006 := @g_eleq1 (.cv x) X (syn_cspfin)
  have p0007 :=
    @g_imbi1d (.classEq (.cv x) X) (.classMem (.cv x) (syn_cspfin))
      (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin)) p0006
  have p0008 :=
    @g_imbi12d (.classEq (.cv x) X) (syn_wsfin Z (.cv x)) (syn_wsfin Z X)
      (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem Z (syn_cspfin)))
      (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin))) p0005 p0007
  have p0009 := @g_sfineq2 (.cv p) (.cv x) (.cv q)
  have p0010_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq p x) (syn_wb (syn_wsfin (.cv q) (.cv p)) (syn_wsfin (.cv q) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0009
  have p0010 :=
    @g_imbi1d (.objEq p x) (syn_wsfin (.cv q) (.cv p)) (syn_wsfin (.cv q) (.cv x))
      (.objMem q a) p0010_e00_recanon
  have p0011 :=
    @g_albidv (.objEq p x) (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))
      (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a)) q dv_cache_0003 p0010
  have p0012_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv p) (.cv x))
        (syn_wb (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))
          (.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0011
  have p0012 :=
    @g_rspcv (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))
      (.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a))) p (.cv x) (.cv a)
      dv_cache_0004 dv_cache_0005 dv_cache_0006 p0012_e00_recanon
  have p0013 := @g_sfineq1 (.cv q) (.cv z) (.cv x)
  have p0014 := @g_eleq1 (.cv q) (.cv z) (.cv a)
  have p0015_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq q z) (syn_wb (syn_wsfin (.cv q) (.cv x)) (syn_wsfin (.cv z) (.cv x)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0013
  have p0015_e01_recanon :
    Nominal.NPrf (.imp (.objEq q z) (syn_wb (.objMem q a) (.objMem z a))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb
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
    @g_imbi12d (.objEq q z) (syn_wsfin (.cv q) (.cv x)) (syn_wsfin (.cv z) (.cv x))
      (.objMem q a) (.objMem z a) p0015_e00_recanon p0015_e01_recanon
  have p0016 :=
    @g_spv (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a))
      (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)) q z dv_cache_0007 p0015
  have p0017 :=
    @g_com12 (.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a)))
      (syn_wsfin (.cv z) (.cv x)) (.objMem z a) p0016
  have p0018_e00_recanon :
    Nominal.NPrf
      (.imp (.objMem x a) (.imp
          (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))
          (.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wral syn_wsfin syn_w3a syn_wa syn_cnnc syn_cint syn_wex
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0012
  have p0018 :=
    @g_syl9r (.objMem x a)
      (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))
      (.all q (.imp (syn_wsfin (.cv q) (.cv x)) (.objMem q a)))
      (syn_wsfin (.cv z) (.cv x)) (.objMem z a) p0018_e00_recanon p0017
  have p0019 :=
    @g_com23 (syn_wsfin (.cv z) (.cv x)) (.objMem x a)
      (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))
      (.objMem z a) p0018
  have p0020 :=
    @g_adantld (syn_wsfin (.cv z) (.cv x))
      (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))
      (.imp (.objMem x a) (.objMem z a)) (.classMem (syn_cncfin (syn_cvv)) (.cv a)) p0019
  have p0021 :=
    @g_a2d (syn_wsfin (.cv z) (.cv x))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
        (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))
      (.objMem x a) (.objMem z a) p0020
  have p0022 :=
    @g_alimdv (syn_wsfin (.cv z) (.cv x))
      (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
          (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))
        (.objMem x a))
      (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
          (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))
        (.objMem z a))
      a dv_cache_0008 p0021
  have p0023 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_spfin p q a
      dv_cache_0009 dv_cache_0010 dv_cache_0011
  have p0024 :=
    @g_eleq2i (syn_cspfin)
      (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a)
              (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))))
      (.cv x) p0023
  have p0025 := @g_vex x
  have p0026 :=
    @g_elintab
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
        (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))
      a (.cv x) dv_cache_0012 p0025
  have p0027_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) (syn_cint (.cab a
              (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a)
                  (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))))) (.all a (.imp
            (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a)
                (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wa syn_cncfin syn_cio syn_cuni syn_wex syn_csn syn_cvv
          syn_wral syn_wsfin syn_w3a syn_cnnc
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
    @g_bitri (.classMem (.cv x) (syn_cspfin))
      (.classMem (.cv x) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
              (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))))))
      (.all a (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a)
              (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a)))
      p0024 p0027_e01_recanon
  have p0028 :=
    @g_eleq2i (syn_cspfin)
      (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a)
              (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))))
      (.cv z) p0023
  have p0029 := @g_vex z
  have p0030 :=
    @g_elintab
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
        (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))
      a (.cv z) dv_cache_0013 p0029
  have p0031_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv z) (syn_cint (.cab a
              (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a)
                  (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a)))))))) (.all a (.imp
            (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a)
                (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem z a)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cint syn_wa syn_cncfin syn_cio syn_cuni syn_wex syn_csn syn_cvv
          syn_wral syn_wsfin syn_w3a syn_cnnc
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
    @g_bitri (.classMem (.cv z) (syn_cspfin))
      (.classMem (.cv z) (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
              (syn_wral p (.cv a) (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))))))
      (.all a (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a)
              (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem z a)))
      p0028 p0031_e01_recanon
  have p0032 :=
    @g_n_3imtr4g (syn_wsfin (.cv z) (.cv x))
      (.all a (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a)
              (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem x a)))
      (.all a (.imp (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral p (.cv a)
              (.all q (.imp (syn_wsfin (.cv q) (.cv p)) (.objMem q a))))) (.objMem z a)))
      (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv z) (syn_cspfin)) p0022 p0027 p0031
  have p0033 :=
    @g_vtocl2g
      (.imp (syn_wsfin (.cv z) (.cv x))
        (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv z) (syn_cspfin))))
      (.imp (syn_wsfin Z (.cv x))
        (.imp (.classMem (.cv x) (syn_cspfin)) (.classMem Z (syn_cspfin))))
      (.imp (syn_wsfin Z X) (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin))))
      z x Z X (syn_cnnc) (syn_cnnc) dv_cache_0014 dv_cache_0015 dv_cache_0016
      dv_cache_0017 dv_cache_0018 p0004 p0008 p0032
  have p0034 :=
    @g_n_3adant3 (.classMem Z (syn_cnnc)) (.classMem X (syn_cnnc))
      (.imp (syn_wsfin Z X) (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin))))
      (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) Z) (.classMem (syn_cpw (.cv y)) X)))
      p0033
  have p0035 :=
    @g_sylbi (syn_wsfin Z X)
      (syn_w3a (.classMem Z (syn_cnnc)) (.classMem X (syn_cnnc)) (syn_wex y
          (syn_wa (.classMem (syn_cpw1 (.cv y)) Z) (.classMem (syn_cpw (.cv y)) X))))
      (.imp (syn_wsfin Z X) (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin))))
      p0000 p0034
  have p0036 :=
    @g_pm2_43i (syn_wsfin Z X)
      (.imp (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin))) p0035
  have p0037 :=
    @g_impcom (syn_wsfin Z X) (.classMem X (syn_cspfin)) (.classMem Z (syn_cspfin)) p0036
  exact p0037

@[expose]
noncomputable def g_spfininduct (x : Var) (z : Var) (B : Class) (V : Class)
    (dv_B_x : x ∉ B.fv) (dv_B_z : z ∉ B.fv) (dv_x_z : x ≠ z) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem B V) (.classMem (syn_cncfin (syn_cvv)) B)
          (syn_wral x (syn_cspfin) (.all z
              (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
                (.classMem (.cv z) B))))) (syn_wss (syn_cspfin) B)) :=
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
  have dv_cache_0001 : z ∉ ((Wff.classMem (.cv x) (syn_cspfin))).fv := by
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
  have dv_cache_0002 : z ∉ ((Wff.classMem (.cv x) (syn_cin (syn_cspfin) B))).fv :=
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
  have dv_cache_0006 : z ∉ ((Wff.classEq (.cv a) (syn_cin (syn_cspfin) B))).fv :=
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
  have dv_cache_0008 : x ∉ ((syn_cin (syn_cspfin) B)).fv :=
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
  have dv_cache_0009 : a ∉ ((syn_cin (syn_cspfin) B)).fv :=
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
      ((syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B))
          (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
                (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))).fv :=
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
  have p0000 := @g_spfinex
  have p0001 := @g_inexg (syn_cspfin) B (syn_cvv) V
  have p0002 :=
    @g_mpan (.classMem (syn_cspfin) (syn_cvv)) (.classMem B V)
      (.classMem (syn_cin (syn_cspfin) B) (syn_cvv)) p0000 p0001
  have p0003 := @g_ncvspfin
  have p0004 := @g_elin (syn_cncfin (syn_cvv)) (syn_cspfin) B
  have p0005 :=
    @g_biimpri (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin))
        (.classMem (syn_cncfin (syn_cvv)) B))
      p0004
  have p0006 :=
    @g_mpan (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin))
      (.classMem (syn_cncfin (syn_cvv)) B)
      (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B)) p0003 p0005
  have p0007 := @g_elin (.cv x) (syn_cspfin) B
  have p0008 := @g_spfinsfincl (.cv x) (.cv z)
  have p0009 :=
    @g_adantrl (.classMem (.cv x) (syn_cspfin)) (syn_wsfin (.cv z) (.cv x))
      (.classMem (.cv z) (syn_cspfin)) (.classMem (.cv x) B) p0008
  have p0010 :=
    @g_a1d
      (syn_wa (.classMem (.cv x) (syn_cspfin))
        (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))))
      (.classMem (.cv z) (syn_cspfin)) (.classMem (.cv z) B) p0009
  have p0011 :=
    @g_ancrd
      (syn_wa (.classMem (.cv x) (syn_cspfin))
        (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))))
      (.classMem (.cv z) B) (.classMem (.cv z) (syn_cspfin)) p0010
  have p0012 := @g_elin (.cv z) (syn_cspfin) B
  have p0013 :=
    @g_syl6ibr
      (syn_wa (.classMem (.cv x) (syn_cspfin))
        (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))))
      (.classMem (.cv z) B)
      (syn_wa (.classMem (.cv z) (syn_cspfin)) (.classMem (.cv z) B))
      (.classMem (.cv z) (syn_cin (syn_cspfin) B)) p0011 p0012
  have p0014 :=
    @g_ex (.classMem (.cv x) (syn_cspfin))
      (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
      (.imp (.classMem (.cv z) B) (.classMem (.cv z) (syn_cin (syn_cspfin) B))) p0013
  have p0015 :=
    @g_a2d (.classMem (.cv x) (syn_cspfin))
      (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)
      (.classMem (.cv z) (syn_cin (syn_cspfin) B)) p0014
  have p0016 :=
    @g_exp4a (.classMem (.cv x) (syn_cspfin))
      (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))
      (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))
      (.classMem (.cv z) (syn_cin (syn_cspfin) B)) p0015
  have p0017 :=
    @g_a2i (.classMem (.cv x) (syn_cspfin))
      (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))
      (.imp (.classMem (.cv x) B)
        (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))
      p0016
  have p0018 :=
    @g_imp3a
      (.imp (.classMem (.cv x) (syn_cspfin))
        (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))
      (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv x) B)
      (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))
      p0017
  have p0019 :=
    @g_syl5bi (.classMem (.cv x) (syn_cin (syn_cspfin) B))
      (syn_wa (.classMem (.cv x) (syn_cspfin)) (.classMem (.cv x) B))
      (.imp (.classMem (.cv x) (syn_cspfin))
        (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))
      (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))
      p0007 p0018
  have p0020 :=
    @g_n_2alimi
      (.imp (.classMem (.cv x) (syn_cspfin))
        (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B)))
      (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B))
        (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))
      x z p0019
  have p0021 :=
    (Nominal.biimpRefl (syn_wral x (syn_cspfin) (.all z
          (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B)))))
  have p0022 :=
    @g_n_19_21v (.classMem (.cv x) (syn_cspfin))
      (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x))) (.classMem (.cv z) B))
      z dv_cache_0001
  have p0023 :=
    @g_albii
      (.all z (.imp (.classMem (.cv x) (syn_cspfin))
          (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B))))
      (.imp (.classMem (.cv x) (syn_cspfin)) (.all z
          (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B))))
      x p0022
  have p0024 :=
    @g_bitr4i
      (syn_wral x (syn_cspfin) (.all z
          (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B))))
      (.all x (.imp (.classMem (.cv x) (syn_cspfin)) (.all z
            (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
              (.classMem (.cv z) B)))))
      (.all x (.all z (.imp (.classMem (.cv x) (syn_cspfin))
            (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
              (.classMem (.cv z) B)))))
      p0021 p0023
  have p0025 :=
    (Nominal.biimpRefl (syn_wral x (syn_cin (syn_cspfin) B) (.all z
          (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))
  have p0026 :=
    @g_n_19_21v (.classMem (.cv x) (syn_cin (syn_cspfin) B))
      (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))) z
      dv_cache_0002
  have p0027 :=
    @g_albii
      (.all z (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B))
          (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))
      (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B)) (.all z
          (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))
      x p0026
  have p0028 :=
    @g_bitr4i
      (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
            (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))
      (.all x (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B)) (.all z
            (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))
      (.all x (.all z (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B))
            (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))
      p0025 p0027
  have p0029 :=
    @g_n_3imtr4i
      (.all x (.all z (.imp (.classMem (.cv x) (syn_cspfin))
            (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
              (.classMem (.cv z) B)))))
      (.all x (.all z (.imp (.classMem (.cv x) (syn_cin (syn_cspfin) B))
            (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))
      (syn_wral x (syn_cspfin) (.all z
          (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B))))
      (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
            (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))
      p0020 p0024 p0028
  have p0030 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_spfin x z a
      dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0031 := @g_eleq2 (.cv a) (syn_cin (syn_cspfin) B) (syn_cncfin (syn_cvv))
  have p0032 := @g_eleq2 (.cv a) (syn_cin (syn_cspfin) B) (.cv z)
  have p0033_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv a) (syn_cin (syn_cspfin) B))
        (syn_wb (.objMem z a) (.classMem (.cv z) (syn_cin (syn_cspfin) B)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_cspfin syn_cint syn_wb
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
    @g_imbi2d (.classEq (.cv a) (syn_cin (syn_cspfin) B)) (.objMem z a)
      (.classMem (.cv z) (syn_cin (syn_cspfin) B)) (syn_wsfin (.cv z) (.cv x))
      p0033_e00_recanon
  have p0034 :=
    @g_albidv (.classEq (.cv a) (syn_cin (syn_cspfin) B))
      (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))
      (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))) z
      dv_cache_0006 p0033
  have p0035 :=
    @g_raleqbi1dv (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))
      (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.classMem (.cv z) (syn_cin (syn_cspfin) B))))
      x (.cv a) (syn_cin (syn_cspfin) B) dv_cache_0007 dv_cache_0008 p0034
  have p0036 :=
    @g_anbi12d (.classEq (.cv a) (syn_cin (syn_cspfin) B))
      (.classMem (syn_cncfin (syn_cvv)) (.cv a))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B))
      (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))
      (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
            (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))
      p0031 p0035
  have p0037 :=
    @g_elabg
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
        (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B))
        (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
              (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))
      a (syn_cin (syn_cspfin) B) (syn_cvv) dv_cache_0009 dv_cache_0010 p0036
  have p0038 :=
    @g_biimprd (.classMem (syn_cin (syn_cspfin) B) (syn_cvv))
      (.classMem (syn_cin (syn_cspfin) B) (.cab a
          (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a)
              (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B))
        (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
              (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))
      p0037
  have p0039 :=
    @g_n_3impib (.classMem (syn_cin (syn_cspfin) B) (syn_cvv))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B))
      (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
            (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))
      (.classMem (syn_cin (syn_cspfin) B) (.cab a
          (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a)
              (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))))
      p0038
  have p0040 :=
    @g_intss1 (syn_cin (syn_cspfin) B)
      (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
          (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a))))))
  have p0041 :=
    @g_syl
      (syn_w3a (.classMem (syn_cin (syn_cspfin) B) (syn_cvv))
        (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B))
        (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
              (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))
      (.classMem (syn_cin (syn_cspfin) B) (.cab a
          (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a)
              (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))))
      (syn_wss (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a))
              (syn_wral x (.cv a) (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))))
        (syn_cin (syn_cspfin) B))
      p0039 p0040
  have p0042 :=
    @g_syl5eqss
      (syn_w3a (.classMem (syn_cin (syn_cspfin) B) (syn_cvv))
        (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B))
        (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
              (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))
      (syn_cspfin)
      (syn_cint (.cab a (syn_wa (.classMem (syn_cncfin (syn_cvv)) (.cv a)) (syn_wral x (.cv a)
              (.all z (.imp (syn_wsfin (.cv z) (.cv x)) (.objMem z a)))))))
      (syn_cin (syn_cspfin) B) p0030 p0041
  have p0043 := @g_inss2 (syn_cspfin) B
  have p0044 :=
    @g_syl6ss
      (syn_w3a (.classMem (syn_cin (syn_cspfin) B) (syn_cvv))
        (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B))
        (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
              (.classMem (.cv z) (syn_cin (syn_cspfin) B))))))
      (syn_cspfin) (syn_cin (syn_cspfin) B) B p0042 p0043
  have p0045 :=
    @g_syl3an (.classMem B V) (.classMem (syn_cin (syn_cspfin) B) (syn_cvv))
      (.classMem (syn_cncfin (syn_cvv)) B)
      (.classMem (syn_cncfin (syn_cvv)) (syn_cin (syn_cspfin) B))
      (syn_wral x (syn_cspfin) (.all z
          (.imp (syn_wa (.classMem (.cv x) B) (syn_wsfin (.cv z) (.cv x)))
            (.classMem (.cv z) B))))
      (syn_wral x (syn_cin (syn_cspfin) B) (.all z (.imp (syn_wsfin (.cv z) (.cv x))
            (.classMem (.cv z) (syn_cin (syn_cspfin) B)))))
      (syn_wss (syn_cspfin) B) p0002 p0006 p0029 p0044
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

@[expose]
noncomputable def g_vfinspnn :
    Nominal.NPrf
      (.imp (.classMem (syn_cvv) (syn_cfin))
        (syn_wss (syn_cspfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))) :=
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
  have dv_cache_0003 : y ∉ ((syn_wne (.cv z) (syn_c0))).fv :=
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
  have dv_cache_0004 : x ∉ ((syn_cdif (syn_cnnc) (syn_csn (syn_c0)))).fv :=
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
  have dv_cache_0005 : z ∉ ((syn_cdif (syn_cnnc) (syn_csn (syn_c0)))).fv :=
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
  have p0000 := @g_vvex
  have p0001 := @g_ncfinprop (syn_cvv) (syn_cvv)
  have p0002 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
        (.classMem (syn_cvv) (syn_cncfin (syn_cvv))))
      p0000 p0001
  have p0003 := @g_ne0i (syn_cncfin (syn_cvv)) (syn_cvv)
  have p0004 :=
    @g_anim2i (.classMem (syn_cvv) (syn_cncfin (syn_cvv)))
      (syn_wne (syn_cncfin (syn_cvv)) (syn_c0))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) p0003
  have p0005 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
        (.classMem (syn_cvv) (syn_cncfin (syn_cvv))))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
        (syn_wne (syn_cncfin (syn_cvv)) (syn_c0)))
      p0002 p0004
  have p0006 := @g_eldifsn (syn_cncfin (syn_cvv)) (syn_cnnc) (syn_c0)
  have p0007 :=
    @g_sylibr (.classMem (syn_cvv) (syn_cfin))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
        (syn_wne (syn_cncfin (syn_cvv)) (syn_c0)))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0005
      p0006
  have p0008 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin (.cv z) (.cv x)
      y dv_cache_0001 dv_cache_0002
  have p0009 := @g_ne0i (.cv z) (syn_cpw1 (.cv y))
  have p0010 :=
    @g_adantr (.classMem (syn_cpw1 (.cv y)) (.cv z)) (syn_wne (.cv z) (syn_c0))
      (.classMem (syn_cpw (.cv y)) (.cv x)) p0009
  have p0011 :=
    @g_exlimiv
      (syn_wa (.classMem (syn_cpw1 (.cv y)) (.cv z)) (.classMem (syn_cpw (.cv y)) (.cv x)))
      (syn_wne (.cv z) (syn_c0)) y dv_cache_0003 p0010
  have p0012 := @g_eldifsn (.cv z) (syn_cnnc) (syn_c0)
  have p0013 :=
    @g_biimpri (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
      (syn_wa (.classMem (.cv z) (syn_cnnc)) (syn_wne (.cv z) (syn_c0))) p0012
  have p0014 :=
    @g_sylan2
      (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) (.cv z))
          (.classMem (syn_cpw (.cv y)) (.cv x))))
      (.classMem (.cv z) (syn_cnnc)) (syn_wne (.cv z) (syn_c0))
      (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0011 p0013
  have p0015 :=
    @g_n_3adant2 (.classMem (.cv z) (syn_cnnc))
      (syn_wex y (syn_wa (.classMem (syn_cpw1 (.cv y)) (.cv z))
          (.classMem (syn_cpw (.cv y)) (.cv x))))
      (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
      (.classMem (.cv x) (syn_cnnc)) p0014
  have p0016 :=
    @g_sylbi (syn_wsfin (.cv z) (.cv x))
      (syn_w3a (.classMem (.cv z) (syn_cnnc)) (.classMem (.cv x) (syn_cnnc)) (syn_wex y
          (syn_wa (.classMem (syn_cpw1 (.cv y)) (.cv z))
            (.classMem (syn_cpw (.cv y)) (.cv x)))))
      (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0008 p0015
  have p0017 :=
    @g_adantl (syn_wsfin (.cv z) (.cv x))
      (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
      (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0016
  have p0018 := Nominal.gen p0017 z
  have p0019 :=
    @g_rgenw
      (.all z (.imp (syn_wa (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
            (syn_wsfin (.cv z) (.cv x)))
          (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))))
      x (syn_cspfin) p0018
  have p0020 := @g_nncex
  have p0021 := @g_snex (syn_c0)
  have p0022 := @g_difex (syn_cnnc) (syn_csn (syn_c0)) p0020 p0021
  have p0023 :=
    @g_spfininduct x z (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cvv) dv_cache_0004
      dv_cache_0005 dv_cache_0006
  have p0024 :=
    @g_mp3an1 (.classMem (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cvv))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
      (syn_wral x (syn_cspfin) (.all z (.imp
            (syn_wa (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
              (syn_wsfin (.cv z) (.cv x)))
            (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))))))
      (syn_wss (syn_cspfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0022 p0023
  have p0025 :=
    @g_sylancl (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
      (syn_wral x (syn_cspfin) (.all z (.imp
            (syn_wa (.classMem (.cv x) (syn_cdif (syn_cnnc) (syn_csn (syn_c0))))
              (syn_wsfin (.cv z) (.cv x)))
            (.classMem (.cv z) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))))))
      (syn_wss (syn_cspfin) (syn_cdif (syn_cnnc) (syn_csn (syn_c0)))) p0007 p0019 p0024
  exact p0025

@[expose]
noncomputable def g_n_1cvsfin :
    Nominal.NPrf
      (.imp (.classMem (syn_cvv) (syn_cfin))
        (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv)))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let a : Var := freshVar proofSupport 0
  have dv_cache_0001 : a ∉ ((syn_cvv)).fv := by
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
      ((syn_wa (.classMem (syn_c1c) (syn_cncfin (syn_c1c)))
          (.classMem (syn_cvv) (syn_cncfin (syn_cvv))))).fv :=
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
  have dv_cache_0003 : a ∉ ((syn_cncfin (syn_c1c))).fv :=
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
  have dv_cache_0004 : a ∉ ((syn_cncfin (syn_cvv))).fv :=
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
  have p0000 := @g_n_1cex
  have p0001 := @g_ncfinprop (syn_c1c) (syn_cvv)
  have p0002 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv)))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
      (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0001
  have p0003 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) p0000 p0002
  have p0004 := @g_vvex
  have p0005 := @g_ncfinprop (syn_cvv) (syn_cvv)
  have p0006 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv)))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
      (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0005
  have p0007 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) p0004 p0006
  have p0009 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
        (.classMem (syn_c1c) (syn_cncfin (syn_c1c))))
      p0000 p0001
  have p0010 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
      (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0009
  have p0012 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
        (.classMem (syn_cvv) (syn_cncfin (syn_cvv))))
      p0004 p0005
  have p0013 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
      (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0012
  have p0015 := @g_pw1eq (.cv a) (syn_cvv)
  have p0016 := @g_df1c2
  have p0017 :=
    @g_syl6eqr (.classEq (.cv a) (syn_cvv)) (syn_cpw1 (.cv a)) (syn_cpw1 (syn_cvv))
      (syn_c1c) p0015 p0016
  have p0018 :=
    @g_eleq1d (.classEq (.cv a) (syn_cvv)) (syn_cpw1 (.cv a)) (syn_c1c)
      (syn_cncfin (syn_c1c)) p0017
  have p0019 := @g_pweq (.cv a) (syn_cvv)
  have p0020 := @g_pwv
  have p0021 :=
    @g_syl6eq (.classEq (.cv a) (syn_cvv)) (syn_cpw (.cv a)) (syn_cpw (syn_cvv)) (syn_cvv)
      p0019 p0020
  have p0022 :=
    @g_eleq1d (.classEq (.cv a) (syn_cvv)) (syn_cpw (.cv a)) (syn_cvv)
      (syn_cncfin (syn_cvv)) p0021
  have p0023 :=
    @g_anbi12d (.classEq (.cv a) (syn_cvv))
      (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_c1c)))
      (.classMem (syn_c1c) (syn_cncfin (syn_c1c)))
      (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cvv)))
      (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0018 p0022
  have p0024 :=
    @g_spcev
      (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_c1c)))
        (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cvv))))
      (syn_wa (.classMem (syn_c1c) (syn_cncfin (syn_c1c)))
        (.classMem (syn_cvv) (syn_cncfin (syn_cvv))))
      a (syn_cvv) dv_cache_0001 dv_cache_0002 p0004 p0023
  have p0025 :=
    @g_syl2anc (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_c1c) (syn_cncfin (syn_c1c)))
      (.classMem (syn_cvv) (syn_cncfin (syn_cvv)))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cvv)))))
      p0010 p0013 p0024
  have p0026 :=
    @g_n_3jca (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
      (syn_wex a (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_c1c)))
          (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cvv)))))
      p0003 p0007 p0025
  have p0027 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_sfin
      (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv)) a dv_cache_0003 dv_cache_0004
  have p0028 :=
    @g_sylibr (.classMem (syn_cvv) (syn_cfin))
      (syn_w3a (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
        (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (syn_wex a
          (syn_wa (.classMem (syn_cpw1 (.cv a)) (syn_cncfin (syn_c1c)))
            (.classMem (syn_cpw (.cv a)) (syn_cncfin (syn_cvv))))))
      (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) p0026 p0027
  exact p0028

@[expose]
noncomputable def g_n_1cspfin :
    Nominal.NPrf
      (.imp (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_c1c)) (syn_cspfin))) :=
  by
  have p0000 := @g_ncvspfin
  have p0001 := @g_n_1cvsfin
  have p0002 := @g_spfinsfincl (syn_cncfin (syn_cvv)) (syn_cncfin (syn_c1c))
  have p0003 :=
    @g_sylancr (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cspfin))
      (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv)))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cspfin)) p0000 p0001 p0002
  exact p0003

@[expose]
noncomputable def g_tncveqnc1fin :
    Nominal.NPrf
      (.imp (.classMem (syn_cvv) (syn_cfin))
        (.classEq (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)))) :=
  by
  have p0000 := @g_vvex
  have p0001 := @g_ncfintfin (syn_cvv) (syn_cvv)
  have p0002 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv))
      (.classEq (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_cpw1 (syn_cvv))))
      p0000 p0001
  have p0003 := @g_df1c2
  have p0004 := @g_ncfineq (syn_c1c) (syn_cpw1 (syn_cvv))
  have p0005 := Nominal.mp p0003 p0004
  have p0006 :=
    @g_syl6eqr (.classMem (syn_cvv) (syn_cfin)) (syn_ctfin (syn_cncfin (syn_cvv)))
      (syn_cncfin (syn_cpw1 (syn_cvv))) (syn_cncfin (syn_c1c)) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_t1csfin1c :
    Nominal.NPrf
      (.imp (.classMem (syn_cvv) (syn_cfin))
        (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cncfin (syn_c1c)))) :=
  by
  have p0000 := @g_n_1cvsfin
  have p0001 := @g_sfintfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))
  have p0002 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin))
      (syn_wsfin (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv)))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_ctfin (syn_cncfin (syn_cvv))))
      p0000 p0001
  have p0003 := @g_tncveqnc1fin
  have p0004 :=
    @g_sfineq2 (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c))
      (syn_ctfin (syn_cncfin (syn_c1c)))
  have p0005 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)))
      (syn_wb (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_ctfin (syn_cncfin (syn_cvv))))
        (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cncfin (syn_c1c))))
      p0003 p0004
  have p0006 :=
    @g_mpbid (.classMem (syn_cvv) (syn_cfin))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_ctfin (syn_cncfin (syn_cvv))))
      (syn_wsfin (syn_ctfin (syn_cncfin (syn_c1c))) (syn_cncfin (syn_c1c))) p0002 p0005
  exact p0006

@[expose]
noncomputable def g_vfintle (N : Class) :
    Nominal.NPrf
      (.imp (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
          (syn_wne N (syn_c0)))
        (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin))) :=
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
    a ∉ ((Wff.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin))).fv :=
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
    a ∉ ((syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)))).fv :=
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
  have p0000 := @g_n0 a N dv_cache_0001
  have p0001 :=
    @g_simp2 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (.classMem (.cv a) N)
  have p0002 := @g_ncfinprop (.cv a) N
  have p0003 :=
    @g_n_3adant2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv a) N)
      (syn_wa (.classMem (syn_cncfin (.cv a)) (syn_cnnc))
        (.classMem (.cv a) (syn_cncfin (.cv a))))
      (.classMem N (syn_cnnc)) p0002
  have p0004 :=
    @g_simpld
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
      (.classMem (syn_cncfin (.cv a)) (syn_cnnc)) (.classMem (.cv a) (syn_cncfin (.cv a)))
      p0003
  have p0005 :=
    @g_simp3 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (.classMem (.cv a) N)
  have p0006 :=
    @g_simprd
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
      (.classMem (syn_cncfin (.cv a)) (syn_cnnc)) (.classMem (.cv a) (syn_cncfin (.cv a)))
      p0003
  have p0007 := @g_nnceleq (.cv a) N (syn_cncfin (.cv a))
  have p0008 :=
    @g_syl22anc
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (.classMem (.cv a) N))
      (.classMem N (syn_cnnc)) (.classMem (syn_cncfin (.cv a)) (syn_cnnc))
      (.classMem (.cv a) N) (.classMem (.cv a) (syn_cncfin (.cv a)))
      (.classEq N (syn_cncfin (.cv a))) p0001 p0004 p0005 p0006 p0007
  have p0009 :=
    @g_n_3expia (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (.classMem (.cv a) N) (.classEq N (syn_cncfin (.cv a))) p0008
  have p0010 :=
    @g_simpr (.classMem (syn_cvv) (syn_cfin)) (.classEq N (syn_cncfin (.cv a)))
  have p0011 := @g_uncompl (.cv a)
  have p0012 := @g_ncfineq (syn_cun (.cv a) (syn_ccompl (.cv a))) (syn_cvv)
  have p0013 := Nominal.mp p0011 p0012
  have p0014 := @g_vex a
  have p0015 := @g_complex (.cv a) p0014
  have p0016 := @g_incompl (.cv a)
  have p0017 := @g_ncfindi (.cv a) (syn_ccompl (.cv a)) (syn_cvv) (syn_cvv)
  have p0018 :=
    @g_mp3an23 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv a) (syn_cvv)))
      (.classMem (syn_ccompl (.cv a)) (syn_cvv))
      (.classEq (syn_cin (.cv a) (syn_ccompl (.cv a))) (syn_c0))
      (.classEq (syn_cncfin (syn_cun (.cv a) (syn_ccompl (.cv a))))
        (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))))
      p0015 p0016 p0017
  have p0019 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv a) (syn_cvv))
      (.classEq (syn_cncfin (syn_cun (.cv a) (syn_ccompl (.cv a))))
        (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))))
      p0014 p0018
  have p0020 :=
    @g_syl5eqr (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cvv))
      (syn_cncfin (syn_cun (.cv a) (syn_ccompl (.cv a))))
      (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))) p0013 p0019
  have p0021 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_cncfin (syn_cvv))
        (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))))
      (.classEq N (syn_cncfin (.cv a))) p0020
  have p0022 :=
    @g_opkeq12d
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classEq N (syn_cncfin (.cv a)))) N
      (syn_cncfin (.cv a)) (syn_cncfin (syn_cvv))
      (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))) p0010 p0021
  have p0023 := @g_ncfinex (.cv a)
  have p0024 := @g_ncfinprop (syn_ccompl (.cv a)) (syn_cvv)
  have p0025 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ccompl (.cv a)) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_ccompl (.cv a))) (syn_cnnc))
        (.classMem (syn_ccompl (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))))
      p0015 p0024
  have p0026 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_ccompl (.cv a))) (syn_cnnc))
      (.classMem (syn_ccompl (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))) p0025
  have p0027 :=
    @g_lefinaddc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a))) (syn_cvv)
  have p0028 :=
    @g_sylancr (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (.cv a)) (syn_cvv))
      (.classMem (syn_cncfin (syn_ccompl (.cv a))) (syn_cnnc))
      (.classMem (syn_copk (syn_cncfin (.cv a))
          (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a))))) (syn_clefin))
      p0023 p0026 p0027
  have p0029 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_copk (syn_cncfin (.cv a))
          (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a))))) (syn_clefin))
      (.classEq N (syn_cncfin (.cv a))) p0028
  have p0030 :=
    @g_eqeltrd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classEq N (syn_cncfin (.cv a))))
      (syn_copk N (syn_cncfin (syn_cvv)))
      (syn_copk (syn_cncfin (.cv a))
        (syn_cplc (syn_cncfin (.cv a)) (syn_cncfin (syn_ccompl (.cv a)))))
      (syn_clefin) p0022 p0029
  have p0031 :=
    @g_ex (.classMem (syn_cvv) (syn_cfin)) (.classEq N (syn_cncfin (.cv a)))
      (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) p0030
  have p0032 :=
    @g_adantr (.classMem (syn_cvv) (syn_cfin))
      (.imp (.classEq N (syn_cncfin (.cv a)))
        (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)))
      (.classMem N (syn_cnnc)) p0031
  have p0033 :=
    @g_syld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)))
      (.classMem (.cv a) N) (.classEq N (syn_cncfin (.cv a)))
      (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) p0009 p0032
  have p0034 :=
    @g_exlimdv (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)))
      (.classMem (.cv a) N) (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) a
      dv_cache_0002 dv_cache_0003 p0033
  have p0035 :=
    @g_syl5bi (syn_wne N (syn_c0)) (syn_wex a (.classMem (.cv a) N))
      (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)))
      (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin)) p0000 p0034
  have p0036 :=
    @g_n_3impia (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (syn_wne N (syn_c0)) (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin))
      p0035
  have p0037 :=
    @g_simp2 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (syn_wne N (syn_c0))
  have p0038 := @g_vvex
  have p0039 := @g_ncfinprop (syn_cvv) (syn_cvv)
  have p0040 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
        (.classMem (syn_cvv) (syn_cncfin (syn_cvv))))
      p0038 p0039
  have p0041 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
        (.classMem (syn_cvv) (syn_cncfin (syn_cvv))))
      (syn_wne N (syn_c0)) p0040
  have p0042 :=
    @g_simpld
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
      (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0041
  have p0043 := @g_tfinlefin N (syn_cncfin (syn_cvv))
  have p0044 :=
    @g_syl2anc
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classMem N (syn_cnnc)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
      (syn_wb (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin))
        (.classMem (syn_copk (syn_ctfin N) (syn_ctfin (syn_cncfin (syn_cvv)))) (syn_clefin)))
      p0037 p0042 p0043
  have p0045 := @g_tncveqnc1fin
  have p0046 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (.classEq (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)))
      (syn_wne N (syn_c0)) p0045
  have p0047 :=
    @g_opkeq2d
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (syn_ctfin (syn_cncfin (syn_cvv))) (syn_cncfin (syn_c1c)) (syn_ctfin N) p0046
  have p0048 :=
    @g_eleq1d
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (syn_copk (syn_ctfin N) (syn_ctfin (syn_cncfin (syn_cvv))))
      (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin) p0047
  have p0049 :=
    @g_bitrd
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin))
      (.classMem (syn_copk (syn_ctfin N) (syn_ctfin (syn_cncfin (syn_cvv)))) (syn_clefin))
      (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin)) p0044 p0048
  have p0050 :=
    @g_mpbid
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classMem (syn_copk N (syn_cncfin (syn_cvv))) (syn_clefin))
      (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin)) p0036 p0049
  exact p0050

@[expose]
noncomputable def g_vfin1cltv :
    Nominal.NPrf
      (.imp (.classMem (syn_cvv) (syn_cfin))
        (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_cltfin))) :=
  by
  have p0000 := @g_uncompl (syn_c1c)
  have p0001 := @g_ncfineq (syn_cun (syn_c1c) (syn_ccompl (syn_c1c))) (syn_cvv)
  have p0002 := Nominal.mp p0000 p0001
  have p0003 := @g_n_1cex
  have p0005 := @g_complex (syn_c1c) p0003
  have p0006 := @g_incompl (syn_c1c)
  have p0007 := @g_ncfindi (syn_c1c) (syn_ccompl (syn_c1c)) (syn_cvv) (syn_cvv)
  have p0008 :=
    @g_mp3an23 (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv)))
      (.classMem (syn_ccompl (syn_c1c)) (syn_cvv))
      (.classEq (syn_cin (syn_c1c) (syn_ccompl (syn_c1c))) (syn_c0))
      (.classEq (syn_cncfin (syn_cun (syn_c1c) (syn_ccompl (syn_c1c))))
        (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
      p0005 p0006 p0007
  have p0009 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv))
      (.classEq (syn_cncfin (syn_cun (syn_c1c) (syn_ccompl (syn_c1c))))
        (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
      p0003 p0008
  have p0010 :=
    @g_syl5reqr (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cvv))
      (syn_cncfin (syn_cun (syn_c1c) (syn_ccompl (syn_c1c))))
      (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) p0002 p0009
  have p0011 :=
    @g_opkeq2d (.classMem (syn_cvv) (syn_cfin))
      (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))
      (syn_cncfin (syn_cvv)) (syn_cncfin (syn_c1c)) p0010
  have p0012 := @g_n_0nel1c
  have p0013 := @g_n_0ex
  have p0014 := @g_elcompl (syn_c0) (syn_c1c) p0013
  have p0015 :=
    @g_mpbir (.classMem (syn_c0) (syn_ccompl (syn_c1c)))
      (.neg (.classMem (syn_c0) (syn_c1c))) p0012 p0014
  have p0016 := @g_n0i (syn_ccompl (syn_c1c)) (syn_c0)
  have p0017 := Nominal.mp p0015 p0016
  have p0018 := @g_ncfinprop (syn_ccompl (syn_c1c)) (syn_cvv)
  have p0019 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_ccompl (syn_c1c)) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cnnc))
        (.classMem (syn_ccompl (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
      p0005 p0018
  have p0020 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cnnc))
      (.classMem (syn_ccompl (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) p0019
  have p0021 :=
    @g_eleq2 (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c))) (syn_ccompl (syn_c1c))
  have p0022 :=
    @g_syl5ibrcom (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_ccompl (syn_c1c)) (syn_c0c))
      (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c))))
      (.classMem (syn_ccompl (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) p0020 p0021
  have p0023 := @g_el0c (syn_ccompl (syn_c1c))
  have p0024 :=
    @g_syl6ib (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c))))
      (.classMem (syn_ccompl (syn_c1c)) (syn_c0c))
      (.classEq (syn_ccompl (syn_c1c)) (syn_c0)) p0022 p0023
  have p0025 :=
    @g_mtoi (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c))))
      (.classEq (syn_ccompl (syn_c1c)) (syn_c0)) p0017 p0024
  have p0026 := @g_addcid1 (syn_cncfin (syn_c1c))
  have p0027 :=
    @g_eqeq1i (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c)) (syn_cncfin (syn_c1c))
      (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) p0026
  have p0029 := @g_ncfinprop (syn_c1c) (syn_cvv)
  have p0030 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
        (.classMem (syn_c1c) (syn_cncfin (syn_c1c))))
      p0003 p0029
  have p0031 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
      (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0030
  have p0032 := @g_peano1
  have p0033 :=
    @g_a1i (.classMem (syn_c0c) (syn_cnnc)) (.classMem (syn_cvv) (syn_cfin)) p0032
  have p0034 :=
    @g_simpld (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cnnc))
      (.classMem (syn_ccompl (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) p0019
  have p0035 :=
    @g_a1i (.classEq (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c)) (syn_cncfin (syn_c1c)))
      (.classMem (syn_cvv) (syn_cfin)) p0026
  have p0036 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
      (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0030
  have p0037 := @g_ne0i (syn_cncfin (syn_c1c)) (syn_c1c)
  have p0038 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cncfin (syn_c1c)))
      (syn_wne (syn_cncfin (syn_c1c)) (syn_c0)) p0036 p0037
  have p0039 :=
    @g_eqnetrd (.classMem (syn_cvv) (syn_cfin))
      (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c)) (syn_cncfin (syn_c1c)) (syn_c0) p0035
      p0038
  have p0040 :=
    @g_preaddccan2 (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cncfin (syn_c1c)) (syn_c0c)
  have p0041 :=
    @g_syl31anc (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (.classMem (syn_c0c) (syn_cnnc))
      (.classMem (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cnnc))
      (syn_wne (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c)) (syn_c0))
      (syn_wb (.classEq (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c))
          (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
        (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c)))))
      p0031 p0033 p0034 p0039 p0040
  have p0042 :=
    @g_syl5bbr
      (.classEq (syn_cncfin (syn_c1c))
        (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
      (.classEq (syn_cplc (syn_cncfin (syn_c1c)) (syn_c0c))
        (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
      (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c)))) p0027 p0041
  have p0043 :=
    @g_mtbird (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_cncfin (syn_c1c))
        (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
      (.classEq (syn_c0c) (syn_cncfin (syn_ccompl (syn_c1c)))) p0025 p0042
  have p0044 := @g_ncfinex (syn_c1c)
  have p0045 :=
    @g_lefinaddc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cvv)
  have p0046 :=
    @g_sylancr (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cvv))
      (.classMem (syn_cncfin (syn_ccompl (syn_c1c))) (syn_cnnc))
      (.classMem (syn_copk (syn_cncfin (syn_c1c))
          (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_clefin))
      p0044 p0034 p0045
  have p0047 := @g_ncfinex (syn_ccompl (syn_c1c))
  have p0048 :=
    @g_addcex (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))) p0044 p0047
  have p0049 :=
    @g_lefinlteq (syn_cncfin (syn_c1c))
      (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))) (syn_cvv)
      (syn_cvv)
  have p0050 :=
    @g_mp3an12 (.classMem (syn_cncfin (syn_c1c)) (syn_cvv))
      (.classMem (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))
        (syn_cvv))
      (syn_wne (syn_cncfin (syn_c1c)) (syn_c0))
      (syn_wb (.classMem (syn_copk (syn_cncfin (syn_c1c))
            (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_clefin))
        (syn_wo (.classMem (syn_copk (syn_cncfin (syn_c1c))
              (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
            (syn_cltfin)) (.classEq (syn_cncfin (syn_c1c))
            (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))))
      p0044 p0048 p0049
  have p0051 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (syn_wne (syn_cncfin (syn_c1c)) (syn_c0))
      (syn_wb (.classMem (syn_copk (syn_cncfin (syn_c1c))
            (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_clefin))
        (syn_wo (.classMem (syn_copk (syn_cncfin (syn_c1c))
              (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
            (syn_cltfin)) (.classEq (syn_cncfin (syn_c1c))
            (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))))
      p0038 p0050
  have p0052 :=
    @g_mpbid (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_copk (syn_cncfin (syn_c1c))
          (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_clefin))
      (syn_wo (.classMem (syn_copk (syn_cncfin (syn_c1c))
            (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_cltfin))
        (.classEq (syn_cncfin (syn_c1c))
          (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))))
      p0046 p0051
  have p0053 :=
    @g_orcomd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_copk (syn_cncfin (syn_c1c))
          (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_cltfin))
      (.classEq (syn_cncfin (syn_c1c))
        (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
      p0052
  have p0054 :=
    @g_ord (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_cncfin (syn_c1c))
        (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
      (.classMem (syn_copk (syn_cncfin (syn_c1c))
          (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_cltfin))
      p0053
  have p0055 :=
    @g_mpd (.classMem (syn_cvv) (syn_cfin))
      (.neg (.classEq (syn_cncfin (syn_c1c))
          (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))))
      (.classMem (syn_copk (syn_cncfin (syn_c1c))
          (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c))))) (syn_cltfin))
      p0043 p0054
  have p0056 :=
    @g_eqeltrrd (.classMem (syn_cvv) (syn_cfin))
      (syn_copk (syn_cncfin (syn_c1c))
        (syn_cplc (syn_cncfin (syn_c1c)) (syn_cncfin (syn_ccompl (syn_c1c)))))
      (syn_copk (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_cltfin) p0011 p0055
  exact p0056

@[expose]
noncomputable def g_vfinncvntnn (N : Class) :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)))
        (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv)))) :=
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
  have p0000 := @g_vvex
  have p0001 := @g_ncfinprop (syn_cvv) (syn_cvv)
  have p0002 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv))
      (syn_wa (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
        (.classMem (syn_cvv) (syn_cncfin (syn_cvv))))
      p0000 p0001
  have p0003 :=
    @g_simprd (.classMem (syn_cvv) (syn_cfin))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
      (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0002
  have p0004 := @g_ne0i (syn_cncfin (syn_cvv)) (syn_cvv)
  have p0005 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cncfin (syn_cvv)))
      (syn_wne (syn_cncfin (syn_cvv)) (syn_c0)) p0003 p0004
  have p0006 :=
    @g_necomd (.classMem (syn_cvv) (syn_cfin)) (syn_cncfin (syn_cvv)) (syn_c0) p0005
  have p0007 := @g_tfineq N (syn_c0)
  have p0008 := @g_tfinnul
  have p0009 :=
    @g_syl6eq (.classEq N (syn_c0)) (syn_ctfin N) (syn_ctfin (syn_c0)) (syn_c0) p0007
      p0008
  have p0010 :=
    @g_neeq1d (.classEq N (syn_c0)) (syn_ctfin N) (syn_c0) (syn_cncfin (syn_cvv)) p0009
  have p0011 :=
    @g_syl5ibr (.classMem (syn_cvv) (syn_cfin))
      (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))) (.classEq N (syn_c0))
      (syn_wne (syn_c0) (syn_cncfin (syn_cvv))) p0006 p0010
  have p0012 :=
    @g_adantrd (.classEq N (syn_c0)) (.classMem (syn_cvv) (syn_cfin))
      (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))) (.classMem N (syn_cnnc)) p0011
  have p0014 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv)))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
      (.classMem (syn_cvv) (syn_cncfin (syn_cvv))) p0001
  have p0015 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cvv) (syn_cvv))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) p0000 p0014
  have p0016 := @g_ltfinirr (syn_cncfin (syn_cvv))
  have p0017 :=
    @g_syl (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
      (.neg (.classMem (syn_copk (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))) (syn_cltfin)))
      p0015 p0016
  have p0018 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (.neg (.classMem (syn_copk (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))) (syn_cltfin)))
      (syn_wne N (syn_c0)) p0017
  have p0019 := @g_vfintle N
  have p0020 := @g_vfin1cltv
  have p0021 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_cltfin))
      (syn_wne N (syn_c0)) p0020
  have p0022 := @g_tfinprop N a dv_cache_0001
  have p0023 :=
    @g_simpld (syn_wa (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classMem (syn_ctfin N) (syn_cnnc))
      (syn_wrex a N (.classMem (syn_cpw1 (.cv a)) (syn_ctfin N))) p0022
  have p0024 :=
    @g_n_3adant1 (.classMem N (syn_cnnc)) (syn_wne N (syn_c0))
      (.classMem (syn_ctfin N) (syn_cnnc)) (.classMem (syn_cvv) (syn_cfin)) p0023
  have p0025 := @g_n_1cex
  have p0026 := @g_ncfinprop (syn_c1c) (syn_cvv)
  have p0027 :=
    @g_simpld (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv)))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
      (.classMem (syn_c1c) (syn_cncfin (syn_c1c))) p0026
  have p0028 :=
    @g_mpan2 (.classMem (syn_cvv) (syn_cfin)) (.classMem (syn_c1c) (syn_cvv))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) p0025 p0027
  have p0029 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc)) (syn_wne N (syn_c0)) p0028
  have p0030 :=
    @g_n_3ad2ant1 (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc)) (syn_wne N (syn_c0)) p0015
  have p0031 := @g_leltfintr (syn_ctfin N) (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))
  have p0032 :=
    @g_syl3anc
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classMem (syn_ctfin N) (syn_cnnc)) (.classMem (syn_cncfin (syn_c1c)) (syn_cnnc))
      (.classMem (syn_cncfin (syn_cvv)) (syn_cnnc))
      (.imp (syn_wa (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin))
          (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_cltfin)))
        (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_cvv))) (syn_cltfin)))
      p0024 p0029 p0030 p0031
  have p0033 :=
    @g_mp2and
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_c1c))) (syn_clefin))
      (.classMem (syn_copk (syn_cncfin (syn_c1c)) (syn_cncfin (syn_cvv))) (syn_cltfin))
      (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_cvv))) (syn_cltfin)) p0019 p0021
      p0032
  have p0034 := @g_opkeq1 (syn_ctfin N) (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))
  have p0035 :=
    @g_eleq1d (.classEq (syn_ctfin N) (syn_cncfin (syn_cvv)))
      (syn_copk (syn_ctfin N) (syn_cncfin (syn_cvv)))
      (syn_copk (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))) (syn_cltfin) p0034
  have p0036 :=
    @g_syl5ibcom
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classMem (syn_copk (syn_ctfin N) (syn_cncfin (syn_cvv))) (syn_cltfin))
      (.classEq (syn_ctfin N) (syn_cncfin (syn_cvv)))
      (.classMem (syn_copk (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))) (syn_cltfin))
      p0033 p0035
  have p0037 :=
    @g_mtod
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.classEq (syn_ctfin N) (syn_cncfin (syn_cvv)))
      (.classMem (syn_copk (syn_cncfin (syn_cvv)) (syn_cncfin (syn_cvv))) (syn_cltfin))
      p0018 p0036
  have p0038 := (Nominal.biimpRefl (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))))
  have p0039 :=
    @g_sylibr
      (syn_w3a (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)) (syn_wne N (syn_c0)))
      (.neg (.classEq (syn_ctfin N) (syn_cncfin (syn_cvv))))
      (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))) p0037 p0038
  have p0040 :=
    @g_n_3expa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc))
      (syn_wne N (syn_c0)) (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))) p0039
  have p0041 :=
    @g_expcom (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)))
      (syn_wne N (syn_c0)) (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))) p0040
  have p0042 :=
    @g_pm2_61ine
      (.imp (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem N (syn_cnnc)))
        (syn_wne (syn_ctfin N) (syn_cncfin (syn_cvv))))
      N (syn_c0) p0012 p0041
  exact p0042

@[expose]
noncomputable def g_vfinncvntsp (x : Var) (a : Var) (dv_a_x : a ≠ x) :
    Nominal.NPrf
      (.imp (.classMem (syn_cvv) (syn_cfin)) (.neg (.classMem (syn_cncfin (syn_cvv)) (.cab a
              (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x)))))))) :=
  by
  have dv_cache_0001 : x ∉ ((Wff.classMem (syn_cvv) (syn_cfin))).fv := by
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
  have dv_cache_0002 : x ∉ ((Wff.classEq (.cv a) (syn_cncfin (syn_cvv)))).fv :=
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
  have dv_cache_0003 : a ∉ ((syn_cncfin (syn_cvv))).fv :=
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
      ((syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))))).fv :=
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
  have p0000 := @g_vfinspnn
  have p0001 := @g_difss (syn_cnnc) (syn_csn (syn_c0))
  have p0002 :=
    @g_syl6ss (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin)
      (syn_cdif (syn_cnnc) (syn_csn (syn_c0))) (syn_cnnc) p0000 p0001
  have p0003 :=
    @g_sselda (.classMem (syn_cvv) (syn_cfin)) (syn_cspfin) (syn_cnnc) (.cv x) p0002
  have p0004 := @g_vfinncvntnn (.cv x)
  have p0005 :=
    @g_syldan (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv x) (syn_cspfin))
      (.classMem (.cv x) (syn_cnnc)) (syn_wne (syn_ctfin (.cv x)) (syn_cncfin (syn_cvv)))
      p0003 p0004
  have p0006 :=
    @g_necomd (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv x) (syn_cspfin)))
      (syn_ctfin (.cv x)) (syn_cncfin (syn_cvv)) p0005
  have p0007 := (Nominal.biimpRefl (syn_wne (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))))
  have p0008 :=
    @g_sylib (syn_wa (.classMem (syn_cvv) (syn_cfin)) (.classMem (.cv x) (syn_cspfin)))
      (syn_wne (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x)))
      (.neg (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x)))) p0006 p0007
  have p0009 :=
    @g_nrexdv (.classMem (syn_cvv) (syn_cfin))
      (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))) x (syn_cspfin) dv_cache_0001
      p0008
  have p0010 := @g_ncfinex (syn_cvv)
  have p0011 := @g_eqeq1 (.cv a) (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))
  have p0012 :=
    @g_rexbidv (.classEq (.cv a) (syn_cncfin (syn_cvv)))
      (.classEq (.cv a) (syn_ctfin (.cv x)))
      (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))) x (syn_cspfin) dv_cache_0002
      p0011
  have p0013 :=
    @g_elab (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))
      (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x)))) a
      (syn_cncfin (syn_cvv)) dv_cache_0003 dv_cache_0004 p0010 p0012
  have p0014 :=
    @g_sylnibr (.classMem (syn_cvv) (syn_cfin))
      (syn_wrex x (syn_cspfin) (.classEq (syn_cncfin (syn_cvv)) (syn_ctfin (.cv x))))
      (.classMem (syn_cncfin (syn_cvv))
        (.cab a (syn_wrex x (syn_cspfin) (.classEq (.cv a) (syn_ctfin (.cv x))))))
      p0009 p0013
  exact p0014


end NFChoice.DirectNominalPrf.WPPReplay

end
