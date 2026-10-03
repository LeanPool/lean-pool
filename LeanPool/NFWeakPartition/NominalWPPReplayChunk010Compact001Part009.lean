/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block003

/-! NF weak partition development: NominalWPPReplayChunk010Compact001Part009. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_nnpweqlem1 (m : Var) (n : Var) (a : Var) (b : Var) (dv_a_b : a ≠ b)
    (dv_a_m : a ≠ m) (dv_a_n : a ≠ n) (dv_b_m : b ≠ m) (dv_b_n : b ≠ n)
    (_dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.classMem (.cab m (syn_wral a (.cv m) (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
                (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                  (.classMem (syn_cpw (.cv b)) (.cv n))))))) (syn_cvv)) :=
  by
  let proofSupport : Finset Var :=
    ({ m } : Finset Var) ∪ ({ n } : Finset Var) ∪ ({ a } : Finset Var) ∪
      ({ b } : Finset Var)
  let t : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_m : t ≠ m := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))))
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_n_ne_t : n ≠ t := Ne.symm fresh_t_ne_n
  have fresh_t_ne_a : t ≠ a := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_a_ne_t : a ≠ t := Ne.symm fresh_t_ne_a
  have fresh_t_ne_b : t ≠ b := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_t : b ≠ t := Ne.symm fresh_t_ne_b
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_ne_n : x ≠ n := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))))
  have fresh_x_ne_a : x ≠ a := by
    intro h
    exact
      fresh_x
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_b : x ≠ b := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_t_ne_x : t ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have dv_cache_0001 : t ∉ ((syn_csn (syn_csn (.cv a)))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_a,
          not_false_eq_true])
  have dv_cache_0002 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))
          (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_m, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0003 :
    t ∉
      ((syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))
              (syn_cpw1 (syn_cpw1 (syn_cnnc))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0005 :
    t ∉ ((syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_m, or_false, not_false_eq_true])
  have dv_cache_0006 : b ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_t, not_false_eq_true])
  have dv_cache_0007 :
    b ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_t, (Ne.symm dv_a_b), dv_b_m,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_b,
          not_false_eq_true])
  have dv_cache_0009 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
            (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_b, fresh_t_ne_a, fresh_t_ne_m,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    t ∉
      ((syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                  (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cnnc)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0012 :
    t ∉ ((syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_b, fresh_t_ne_a, or_false, not_false_eq_true])
  have dv_cache_0013 : n ∉ ((Class.cv t)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_t, not_false_eq_true])
  have dv_cache_0014 : n ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0015 :
    n ∉
      ((Wff.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_t, (Ne.symm dv_b_n), (Ne.symm dv_a_n),
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : t ∉ ((syn_cnnc)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0017 : n ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact (show n ≠ t from (by exact fresh_n_ne_t))
  have dv_cache_0018 : t ∉ ((syn_csn (syn_csn (.cv n)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_n,
          not_false_eq_true])
  have dv_cache_0019 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv n)))
            (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_n, fresh_t_ne_b, fresh_t_ne_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 :
    t ∉
      ((syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0022 : t ∉ ((syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_n, fresh_t_ne_a, or_false, not_false_eq_true])
  have dv_cache_0023 : x ∉ ((Class.cv t)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0024 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_n, fresh_x_ne_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0025 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0026 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
            (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin (syn_cins2k (syn_csik
                (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_n, fresh_t_ne_a,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0027 : x ∉ ((syn_cpw (.cv a))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_a,
          not_false_eq_true])
  have dv_cache_0028 : x ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_n, not_false_eq_true])
  have dv_cache_0029 :
    t ∉
      ((syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0030 : t ∉ ((syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_n, fresh_t_ne_b, or_false, not_false_eq_true])
  have dv_cache_0031 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
            (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_n, fresh_x_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0032 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
            (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin (syn_cins2k (syn_ccnvk
                (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_n, fresh_t_ne_b,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0033 : x ∉ ((syn_cpw (.cv b))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_x_ne_b,
          not_false_eq_true])
  have dv_cache_0034 :
    t ∉
      ((syn_cin (syn_csik (syn_cssetk)) (syn_cimak
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0035 : t ∉ ((syn_cpw1 (syn_c1c))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0036 : t ∉ ((syn_csn (.cv m))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_m,
          not_false_eq_true])
  have dv_cache_0037 : a ∉ ((Class.cv t)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_t, not_false_eq_true])
  have dv_cache_0038 :
    a ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
            (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                    (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_t, dv_a_m, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0039 :
    m ∉
      ((syn_cuni1 (syn_ccompl (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
                  (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                      (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                                (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c)))))).fv :=
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
        have compact_fv_not_mem_empty : m ∉ (∅ : Finset Var) :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @g_vex m
  have p0001 :=
    @g_eluni1 (.cv m)
      (syn_ccompl (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c))))
      p0000
  have p0002 := @g_snex (syn_csn (.cv a))
  have p0003 := @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))
  have p0004 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
      (syn_copk (.cv t) (syn_csn (.cv m)))
      (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))
      (syn_cin (syn_csik (syn_cssetk)) (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk)))
            (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k
                          (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0003
  have p0005 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
          (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))
        (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      t (syn_csn (syn_csn (.cv a))) dv_cache_0001 dv_cache_0002 p0002 p0004
  have p0006 :=
    @g_elin (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))
      (syn_csik (syn_cssetk))
      (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0007 := @g_snex (.cv a)
  have p0008 := @g_opksnelsik (syn_csn (.cv a)) (.cv m) (syn_cssetk) p0007 p0000
  have p0009 := @g_vex a
  have p0010 := @g_elssetk (.cv a) (.cv m) p0009 p0000
  have p0011_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv a)) (.cv m)) (syn_cssetk)) (.objMem a m)) :=
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
      p0010
  have p0011 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv a)) (.cv m)) (syn_cssetk)) (.objMem a m) p0008
      p0011_e01_recanon
  have p0012 := @g_opkex (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))
  have p0013 :=
    @g_elimak t
      (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))) dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0012
  have p0014 := @g_elpw131c b (.cv t) dv_cache_0006
  have p0015 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex b (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
        (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))
      p0014
  have p0016 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
        (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))
      b dv_cache_0007
  have p0017 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classMem
          (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc))))))))
      (syn_wa (syn_wex b (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc))))))))
      (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))))
      p0015 p0016
  have p0018 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) (.classMem
          (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc))))))))
      (syn_wex b (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))))
      t p0017
  have p0019 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem
          (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))))
  have p0020 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) (.classMem
          (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc))))))))
      b t
  have p0021 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))))
      (syn_wex t (syn_wex b
          (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) (.classMem
              (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem
          (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc))))))))
      (syn_wex b (syn_wex t
          (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) (.classMem
              (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))))))
      p0018 p0019 p0020
  have p0022 := @g_snex (syn_csn (syn_csn (syn_csn (.cv b))))
  have p0023 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
      (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))
  have p0024 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
      (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
      (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
        (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
      (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
      p0023
  have p0025 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
        (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
          (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
        (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))
      t (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))) dv_cache_0008 dv_cache_0009 p0022
      p0024
  have p0026 :=
    @g_eldif
      (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
        (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
      (syn_cins2k (syn_csik (syn_cssetk)))
      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik
                      (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc)))))
  have p0027 := @g_snex (syn_csn (.cv b))
  have p0028 := @g_snex (.cv m)
  have p0029 :=
    @g_otkelins2k (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))
      (syn_csn (.cv m)) (syn_csik (syn_cssetk)) p0027 p0002 p0028
  have p0030 := @g_snex (.cv b)
  have p0031 := @g_opksnelsik (syn_csn (.cv b)) (.cv m) (syn_cssetk) p0030 p0000
  have p0032 := @g_vex b
  have p0033 := @g_elssetk (.cv b) (.cv m) p0032 p0000
  have p0034_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cssetk)) (.objMem b m)) :=
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
      p0033
  have p0034 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
          (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
        (syn_cins2k (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (.cv m)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv m)) (syn_cssetk)) (.objMem b m) p0029
      p0031 p0034_e02_recanon
  have p0035 :=
    @g_otkelins3k (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))
      (syn_csn (.cv m))
      (syn_cimak (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                  (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc))))
      p0027 p0002 p0028
  have p0036 := @g_opkex (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))
  have p0037 :=
    @g_elimak t
      (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cpw1 (syn_cpw1 (syn_cnnc)))
      (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))) dv_cache_0010
      dv_cache_0011 dv_cache_0012 p0036
  have p0038 := @g_elpw12 n (.cv t) (syn_cnnc) dv_cache_0013 dv_cache_0014
  have p0039 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cnnc))))
      (syn_wrex n (syn_cnnc) (.classEq (.cv t) (syn_csn (syn_csn (.cv n)))))
      (.classMem (syn_copk (.cv t)
          (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                  (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0038
  have p0040 :=
    @g_r19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv n))))
      (.classMem (syn_copk (.cv t)
          (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                  (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      n (syn_cnnc) dv_cache_0015
  have p0041 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wa (syn_wrex n (syn_cnnc) (.classEq (.cv t) (syn_csn (syn_csn (.cv n))))) (.classMem
          (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))))
          (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv n)))) (.classMem
            (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0039 p0040
  have p0042 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv n)))) (.classMem
            (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      t p0041
  have p0043 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cnnc))) (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
  have p0044 :=
    @g_rexcom4
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv n)))) (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      n t (syn_cnnc) dv_cache_0016 dv_cache_0017
  have p0045 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cnnc)))) (.classMem
            (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wex t (syn_wrex n (syn_cnnc) (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv n))))
            (.classMem (syn_copk (.cv t)
                (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cnnc))) (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wrex n (syn_cnnc) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv n))))
            (.classMem (syn_copk (.cv t)
                (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0042 p0043 p0044
  have p0046 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))) (syn_cimak
          (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cnnc))) (.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wrex n (syn_cnnc) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv n))))
            (.classMem (syn_copk (.cv t)
                (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0037 p0045
  have p0047 := @g_snex (syn_csn (.cv n))
  have p0048 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv n)))
      (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))
  have p0049 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv n))))
      (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))))
      (syn_copk (syn_csn (syn_csn (.cv n)))
        (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))))
      (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0048
  have p0050 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t)
          (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                  (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv n)))
          (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                  (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      t (syn_csn (syn_csn (.cv n))) dv_cache_0018 dv_cache_0019 p0047 p0049
  have p0051 :=
    @g_elin
      (syn_copk (syn_csn (syn_csn (.cv n)))
        (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))))
      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0052 := @g_opkex (.cv n) (syn_csn (syn_csn (.cv a)))
  have p0053 :=
    @g_elimak t
      (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))
      dv_cache_0020 dv_cache_0021 dv_cache_0022 p0052
  have p0054 := @g_elpw121c x (.cv t) dv_cache_0023
  have p0055 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
          (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))
      p0054
  have p0056 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
          (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))
      x dv_cache_0024
  have p0057 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
              (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
      p0055 p0056
  have p0058 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
              (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
      t p0057
  have p0059 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
  have p0060 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      x t
  have p0061 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
              (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a)))))
              (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a)))))
              (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))))
      p0058 p0059 p0060
  have p0062 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0063 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))
      (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))
  have p0064 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a)))))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
        (syn_copk (.cv n) (syn_csn (syn_csn (.cv a)))))
      (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
      p0063
  have p0065 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
          (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin (syn_cins2k (syn_csik
              (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                      (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cins3k (syn_cssetk))))
      t (syn_csn (syn_csn (syn_csn (.cv x)))) dv_cache_0025 dv_cache_0026 p0062 p0064
  have p0066 :=
    @g_elin
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
        (syn_copk (.cv n) (syn_csn (syn_csn (.cv a)))))
      (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cins3k (syn_cssetk))
  have p0067 := @g_snex (.cv x)
  have p0068 := @g_vex n
  have p0069 :=
    @g_otkelins2k (syn_csn (.cv x)) (.cv n) (syn_csn (syn_csn (.cv a)))
      (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0067 p0068 p0002
  have p0070 := @g_vex x
  have p0071 :=
    @g_opksnelsik (.cv x) (syn_csn (.cv a))
      (syn_ccnvk (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0070 p0007
  have p0072 :=
    @g_opkelcnvk (.cv x) (syn_csn (.cv a))
      (syn_ccompl (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0070 p0007
  have p0073 := @g_eqpwrelk (.cv a) (.cv x) p0009 p0070
  have p0074 :=
    @g_bitri
      (.classMem (syn_copk (.cv x) (syn_csn (.cv a))) (syn_ccnvk (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (syn_csn (.cv a)) (.cv x)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv x) (syn_cpw (.cv a))) p0072 p0073
  have p0075 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cins2k (syn_csik (syn_ccnvk
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                    (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (syn_csn (.cv a)))) (syn_csik (syn_ccnvk
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                  (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (.cv x) (syn_csn (.cv a))) (syn_ccnvk (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classEq (.cv x) (syn_cpw (.cv a))) p0069 p0071 p0074
  have p0076 :=
    @g_otkelins3k (syn_csn (.cv x)) (.cv n) (syn_csn (syn_csn (.cv a))) (syn_cssetk) p0067
      p0068 p0002
  have p0077 := @g_elssetk (.cv x) (.cv n) p0070 p0068
  have p0078_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv n)) (syn_cssetk)) (.objMem x n)) :=
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
      p0077
  have p0078 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cins3k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv n)) (syn_cssetk)) (.objMem x n) p0076
      p0078_e01_recanon
  have p0079 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cins2k (syn_csik (syn_ccnvk
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                    (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classEq (.cv x) (syn_cpw (.cv a)))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cins3k (syn_cssetk)))
      (.objMem x n) p0075 p0078
  have p0080 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
              (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin (syn_cins2k (syn_csik
              (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                      (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cins3k (syn_cssetk))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
            (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cins2k (syn_csik (syn_ccnvk
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                      (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
            (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cins3k (syn_cssetk))))
      (syn_wa (.classEq (.cv x) (syn_cpw (.cv a))) (.objMem x n)) p0065 p0066 p0079
  have p0081 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
              (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
      (syn_wa (.classEq (.cv x) (syn_cpw (.cv a))) (.objMem x n)) x p0080
  have p0082 :=
    @g_n_3bitri
      (.classMem (syn_copk (.cv n) (syn_csn (syn_csn (.cv a)))) (syn_cimak (syn_cin (syn_cins2k
              (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a))))) (syn_cin
            (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv a)))))
              (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cpw (.cv a))) (.objMem x n))) p0053 p0061
      p0081
  have p0083 :=
    @g_otkelins2k (.cv n) (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))
      (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0068 p0027 p0002
  have p0084 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x
      (syn_cpw (.cv a)) (.cv n) dv_cache_0027 dv_cache_0028)
  have p0085_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cpw (.cv a)) (.cv n))
        (syn_wex x (syn_wa (.classEq (.cv x) (syn_cpw (.cv a))) (.objMem x n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_wex
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
      p0084
  have p0085 :=
    @g_n_3bitr4i
      (.classMem (syn_copk (.cv n) (syn_csn (syn_csn (.cv a)))) (syn_cimak (syn_cin (syn_cins2k
              (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cpw (.cv a))) (.objMem x n)))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv n)))
          (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cins2k
          (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classMem (syn_cpw (.cv a)) (.cv n)) p0082 p0083 p0085_e02_recanon
  have p0086 := @g_opkex (.cv n) (syn_csn (syn_csn (.cv b)))
  have p0087 :=
    @g_elimak t
      (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))
      dv_cache_0029 dv_cache_0021 dv_cache_0030 p0086
  have p0088 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
          (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))
      p0054
  have p0089 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
          (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))
      x dv_cache_0031
  have p0090 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
            (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
            (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
              (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
      p0088 p0089
  have p0091 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
            (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
              (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
      t p0090
  have p0092 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
            (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
  have p0093 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
            (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      x t
  have p0094 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
              (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b)))))
              (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
            (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b)))))
              (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))))
      p0091 p0092 p0093
  have p0095 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))
      (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))
  have p0096 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b)))))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
        (syn_copk (.cv n) (syn_csn (syn_csn (.cv b)))))
      (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
      p0095
  have p0097 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
          (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin (syn_cins2k (syn_ccnvk
              (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                      (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cins3k (syn_cssetk))))
      t (syn_csn (syn_csn (syn_csn (.cv x)))) dv_cache_0025 dv_cache_0032 p0062 p0096
  have p0098 :=
    @g_elin
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
        (syn_copk (.cv n) (syn_csn (syn_csn (.cv b)))))
      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cins3k (syn_cssetk))
  have p0099 :=
    @g_otkelins2k (syn_csn (.cv x)) (.cv n) (syn_csn (syn_csn (.cv b)))
      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0067 p0068 p0027
  have p0100 :=
    @g_opkelcnvk (syn_csn (.cv x)) (syn_csn (syn_csn (.cv b)))
      (syn_csik (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0067 p0027
  have p0101 :=
    @g_opksnelsik (syn_csn (.cv b)) (.cv x)
      (syn_ccompl (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0030 p0070
  have p0102 := @g_eqpwrelk (.cv b) (.cv x) p0032 p0070
  have p0103 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (.cv x))) (syn_csik (syn_ccompl
            (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv x)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classEq (.cv x) (syn_cpw (.cv b))) p0101 p0102
  have p0104 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cins2k (syn_ccnvk (syn_csik
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                    (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn (syn_csn (.cv b)))) (syn_ccnvk (syn_csik
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                  (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (.cv x))) (syn_csik (syn_ccompl
            (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classEq (.cv x) (syn_cpw (.cv b))) p0099 p0100 p0103
  have p0105 :=
    @g_otkelins3k (syn_csn (.cv x)) (.cv n) (syn_csn (syn_csn (.cv b))) (syn_cssetk) p0067
      p0068 p0027
  have p0106_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv n)) (syn_cssetk)) (.objMem x n)) :=
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
      p0077
  have p0106 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cins3k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv n)) (syn_cssetk)) (.objMem x n) p0105
      p0106_e01_recanon
  have p0107 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cins2k (syn_ccnvk (syn_csik
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                    (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classEq (.cv x) (syn_cpw (.cv b)))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cins3k (syn_cssetk)))
      (.objMem x n) p0104 p0106
  have p0108 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
              (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
          (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin (syn_cins2k (syn_ccnvk
              (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                      (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cins3k (syn_cssetk))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
            (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cins2k (syn_ccnvk (syn_csik
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                      (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv x))))
            (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cins3k (syn_cssetk))))
      (syn_wa (.classEq (.cv x) (syn_cpw (.cv b))) (.objMem x n)) p0097 p0098 p0107
  have p0109 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
              (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk))))))
      (syn_wa (.classEq (.cv x) (syn_cpw (.cv b))) (.objMem x n)) x p0108
  have p0110 :=
    @g_n_3bitri
      (.classMem (syn_copk (.cv n) (syn_csn (syn_csn (.cv b)))) (syn_cimak (syn_cin (syn_cins2k
              (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b))))) (syn_cin
            (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (syn_csn (syn_csn (.cv b)))))
              (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cpw (.cv b))) (.objMem x n))) p0087 p0094
      p0109
  have p0111 :=
    @g_otkelins3k (.cv n) (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))
      (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0068 p0027 p0002
  have p0112 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x
      (syn_cpw (.cv b)) (.cv n) dv_cache_0033 dv_cache_0028)
  have p0113_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_cpw (.cv b)) (.cv n))
        (syn_wex x (syn_wa (.classEq (.cv x) (syn_cpw (.cv b))) (.objMem x n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold syn_wb syn_cpw syn_wss syn_cin syn_ccompl syn_cnin syn_wnan syn_wa syn_wex
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
      p0112
  have p0113 :=
    @g_n_3bitr4i
      (.classMem (syn_copk (.cv n) (syn_csn (syn_csn (.cv b)))) (syn_cimak (syn_cin (syn_cins2k
              (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wex x (syn_wa (.classEq (.cv x) (syn_cpw (.cv b))) (.objMem x n)))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv n)))
          (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cins3k
          (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classMem (syn_cpw (.cv b)) (.cv n)) p0110 p0111 p0113_e02_recanon
  have p0114 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (.cv n)))
          (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cins2k
          (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classMem (syn_cpw (.cv a)) (.cv n))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv n)))
          (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cins3k
          (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classMem (syn_cpw (.cv b)) (.cv n)) p0085 p0113
  have p0115 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv n)))) (.classMem
            (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv n)))
          (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                        (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                  (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (.cv n)))
            (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cins2k
            (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (.classMem
          (syn_copk (syn_csn (syn_csn (.cv n)))
            (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cins3k
            (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))
      p0050 p0051 p0114
  have p0116 :=
    @g_rexbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv n)))) (.classMem
            (syn_copk (.cv t)
              (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
              (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                            (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n)) (.classMem (syn_cpw (.cv b)) (.cv n)))
      n (syn_cnnc) p0115
  have p0117 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
          (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))) (syn_cins3k (syn_cimak
            (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a)))) (syn_cimak
          (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc)))))
      (syn_wrex n (syn_cnnc) (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv n))))
            (.classMem (syn_copk (.cv t)
                (syn_copk (syn_csn (syn_csn (.cv b))) (syn_csn (syn_csn (.cv a))))) (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
          (.classMem (syn_cpw (.cv b)) (.cv n))))
      p0035 p0046 p0116
  have p0118 :=
    @g_notbii
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
          (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))) (syn_cins3k (syn_cimak
            (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
      (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
          (.classMem (syn_cpw (.cv b)) (.cv n))))
      p0117
  have p0119 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
          (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
        (syn_cins2k (syn_csik (syn_cssetk))))
      (.objMem b m)
      (.neg (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
            (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))) (syn_cins3k (syn_cimak
              (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))
      (.neg (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
            (.classMem (syn_cpw (.cv b)) (.cv n)))))
      p0034 p0118
  have p0120 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
          (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
        (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
            (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
          (syn_cins2k (syn_csik (syn_cssetk)))) (.neg (.classMem
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
              (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))) (syn_cins3k (syn_cimak
                (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc))))))))
      (syn_wa (.objMem b m) (.neg (syn_wrex n (syn_cnnc)
            (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
              (.classMem (syn_cpw (.cv b)) (.cv n))))))
      p0025 p0026 p0119
  have p0121 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc)))))))))
      (syn_wa (.objMem b m) (.neg (syn_wrex n (syn_cnnc)
            (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
              (.classMem (syn_cpw (.cv b)) (.cv n))))))
      b p0120
  have p0122 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))) (syn_cimak
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) (.classMem
          (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc))))))))
      (syn_wex b (syn_wex t
          (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) (.classMem
              (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))))
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))))))
      (syn_wex b (syn_wa (.objMem b m) (.neg (syn_wrex n (syn_cnnc)
              (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                (.classMem (syn_cpw (.cv b)) (.cv n)))))))
      p0013 p0021 p0121
  have p0123 :=
    (Nominal.biimpRefl (syn_wrex b (.cv m) (.neg (syn_wrex n (syn_cnnc)
            (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
              (.classMem (syn_cpw (.cv b)) (.cv n)))))))
  have p0124 :=
    @g_rexnal
      (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
          (.classMem (syn_cpw (.cv b)) (.cv n))))
      b (.cv m)
  have p0125_e01_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex b (.cv m) (.neg (syn_wrex n (syn_cnnc)
              (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                (.classMem (syn_cpw (.cv b)) (.cv n)))))) (syn_wex b (syn_wa (.objMem b m) (.neg
              (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                  (.classMem (syn_cpw (.cv b)) (.cv n)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa]
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
      p0123
  have p0125 :=
    @g_n_3bitr2i
      (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))) (syn_cimak
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wex b (syn_wa (.objMem b m) (.neg (syn_wrex n (syn_cnnc)
              (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                (.classMem (syn_cpw (.cv b)) (.cv n)))))))
      (syn_wrex b (.cv m) (.neg (syn_wrex n (syn_cnnc)
            (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
              (.classMem (syn_cpw (.cv b)) (.cv n))))))
      (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
            (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
              (.classMem (syn_cpw (.cv b)) (.cv n))))))
      p0122 p0125_e01_recanon p0124
  have p0126 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))
        (syn_csik (syn_cssetk)))
      (.objMem a m)
      (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))) (syn_cimak
          (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
            (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
              (.classMem (syn_cpw (.cv b)) (.cv n))))))
      p0011 p0125
  have p0127 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
          (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
              (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))
        (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wa (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m)))
          (syn_csik (syn_cssetk)))
        (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (.cv m))) (syn_cimak
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wa (.objMem a m) (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
              (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                (.classMem (syn_cpw (.cv b)) (.cv n)))))))
      p0005 p0006 p0126
  have p0128 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
          (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
              (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.objMem a m) (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
              (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                (.classMem (syn_cpw (.cv b)) (.cv n)))))))
      a p0127
  have p0129 :=
    @g_elimak t
      (syn_cin (syn_csik (syn_cssetk)) (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk)))
            (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k
                          (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cpw1 (syn_c1c)) (syn_csn (.cv m)) dv_cache_0034 dv_cache_0035 dv_cache_0036
      p0028
  have p0130 := @g_elpw11c a (.cv t) dv_cache_0037
  have p0131 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (.cv a)))))
      (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
          (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0130
  have p0132 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
      (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
          (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                  (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      a dv_cache_0038
  have p0133 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
            (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                    (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wa (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (.cv a)))))
        (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
            (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                    (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex a (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
          (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
              (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0131 p0132
  have p0134 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
            (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                    (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex a (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
          (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
              (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      t p0133
  have p0135 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_c1c))
        (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
            (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                    (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
  have p0136 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
        (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
            (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                    (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      a t
  have p0137 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
          (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
              (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wex t (syn_wex a (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
            (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
                (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik
                                    (syn_ccnvk (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                                (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wrex t (syn_cpw1 (syn_c1c)) (.classMem (syn_copk (.cv t) (syn_csn (.cv m)))
          (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex a (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
            (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
                (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik
                                    (syn_ccnvk (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                                (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0134 p0135 p0136
  have p0138 :=
    @g_bitri
      (.classMem (syn_csn (.cv m)) (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c))))
      (syn_wrex t (syn_cpw1 (syn_c1c)) (.classMem (syn_copk (.cv t) (syn_csn (.cv m)))
          (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wex a (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
            (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
                (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik
                                    (syn_ccnvk (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                                (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0129 p0137
  have p0139 :=
    (Nominal.biimpRefl (syn_wrex a (.cv m) (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
              (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                (.classMem (syn_cpw (.cv b)) (.cv n))))))))
  have p0140_e02_recanon :
    Nominal.NPrf
      (syn_wb (syn_wrex a (.cv m) (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
                (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                  (.classMem (syn_cpw (.cv b)) (.cv n))))))) (syn_wex a (syn_wa (.objMem a m)
            (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
                  (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                    (.classMem (syn_cpw (.cv b)) (.cv n))))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_wrex, syn_wex, syn_wa, syn_wral]
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
      p0139
  have p0140 :=
    @g_n_3bitr4i
      (syn_wex a (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv a))))
            (.classMem (syn_copk (.cv t) (syn_csn (.cv m))) (syn_cin (syn_csik (syn_cssetk))
                (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik
                                    (syn_ccnvk (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                                (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex a (syn_wa (.objMem a m) (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
                (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                  (.classMem (syn_cpw (.cv b)) (.cv n))))))))
      (.classMem (syn_csn (.cv m)) (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c))))
      (syn_wrex a (.cv m) (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
              (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                (.classMem (syn_cpw (.cv b)) (.cv n)))))))
      p0128 p0138 p0140_e02_recanon
  have p0141 :=
    @g_notbii
      (.classMem (syn_csn (.cv m)) (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c))))
      (syn_wrex a (.cv m) (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
              (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                (.classMem (syn_cpw (.cv b)) (.cv n)))))))
      p0140
  have p0142 :=
    @g_elcompl (syn_csn (.cv m))
      (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c)))
      p0028
  have p0143 :=
    @g_dfral2
      (syn_wral b (.cv m) (syn_wrex n (syn_cnnc) (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
            (.classMem (syn_cpw (.cv b)) (.cv n)))))
      a (.cv m)
  have p0144 :=
    @g_n_3bitr4i
      (.neg (.classMem (syn_csn (.cv m)) (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
                (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c)))))
      (.neg (syn_wrex a (.cv m) (.neg (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
                (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                  (.classMem (syn_cpw (.cv b)) (.cv n))))))))
      (.classMem (syn_csn (.cv m)) (syn_ccompl (syn_cimak (syn_cin (syn_csik (syn_cssetk))
              (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c)))))
      (syn_wral a (.cv m) (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
            (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
              (.classMem (syn_cpw (.cv b)) (.cv n))))))
      p0141 p0142 p0143
  have p0145 :=
    @g_bitri
      (.classMem (.cv m) (syn_cuni1 (syn_ccompl (syn_cimak (syn_cin (syn_csik (syn_cssetk))
                (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                        (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik
                                    (syn_ccnvk (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                                (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c))))))
      (.classMem (syn_csn (.cv m)) (syn_ccompl (syn_cimak (syn_cin (syn_csik (syn_cssetk))
              (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak
                      (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c)))))
      (syn_wral a (.cv m) (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
            (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
              (.classMem (syn_cpw (.cv b)) (.cv n))))))
      p0001 p0144
  have p0146 :=
    @g_eqabi
      (syn_wral a (.cv m) (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
            (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
              (.classMem (syn_cpw (.cv b)) (.cv n))))))
      m
      (syn_cuni1 (syn_ccompl (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
                (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c)))))
      dv_cache_0039 p0145
  have p0147 := @g_ssetkex
  have p0148 := @g_sikex (syn_cssetk) p0147
  have p0149 := @g_ins2kex (syn_csik (syn_cssetk)) p0148
  have p0151 := @g_ins2kex (syn_cssetk) p0147
  have p0152 := @g_ins3kex (syn_csik (syn_cssetk)) p0148
  have p0153 :=
    @g_symdifex (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))) p0151 p0152
  have p0154 := @g_n_1cex
  have p0155 := @g_pw1ex (syn_c1c) p0154
  have p0156 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0155
  have p0157 :=
    @g_imakex (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0153 p0156
  have p0158 :=
    @g_complex
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0157
  have p0159 :=
    @g_cnvkex
      (syn_ccompl (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0158
  have p0160 :=
    @g_sikex
      (syn_ccnvk (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0159
  have p0161 :=
    @g_ins2kex
      (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0160
  have p0163 := @g_ins3kex (syn_cssetk) p0147
  have p0164 :=
    @g_inex
      (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cins3k (syn_cssetk)) p0161 p0163
  have p0165 :=
    @g_imakex
      (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0164 p0156
  have p0166 :=
    @g_ins2kex
      (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0165
  have p0167 :=
    @g_sikex
      (syn_ccompl (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0158
  have p0168 :=
    @g_cnvkex
      (syn_csik (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0167
  have p0169 :=
    @g_ins2kex
      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0168
  have p0170 :=
    @g_inex
      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cins3k (syn_cssetk)) p0169 p0163
  have p0171 :=
    @g_imakex
      (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0170 p0156
  have p0172 :=
    @g_ins3kex
      (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_cssetk))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0171
  have p0173 :=
    @g_inex
      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_cssetk))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0166 p0172
  have p0174 := @g_nncex
  have p0175 := @g_pw1ex (syn_cnnc) p0174
  have p0176 := @g_pw1ex (syn_cpw1 (syn_cnnc)) p0175
  have p0177 :=
    @g_imakex
      (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_csik (syn_cssetk))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cpw1 (syn_cpw1 (syn_cnnc))) p0173 p0176
  have p0178 :=
    @g_ins3kex
      (syn_cimak (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                  (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_cssetk))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc))))
      p0177
  have p0179 :=
    @g_difex (syn_cins2k (syn_csik (syn_cssetk)))
      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik
                      (syn_ccnvk (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                    (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_cssetk))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc)))))
      p0149 p0178
  have p0180 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0156
  have p0181 :=
    @g_imakex
      (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin (syn_cins2k
                      (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_csik (syn_cssetk))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0179 p0180
  have p0182 :=
    @g_inex (syn_csik (syn_cssetk))
      (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                              (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_csik (syn_cssetk))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0148 p0181
  have p0183 :=
    @g_imakex
      (syn_cin (syn_csik (syn_cssetk)) (syn_cimak (syn_cdif (syn_cins2k (syn_csik (syn_cssetk)))
            (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cimak (syn_cin (syn_cins2k
                          (syn_csik (syn_ccnvk (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cins3k
                    (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk))
                                    (syn_cins3k (syn_csik (syn_cssetk))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                (syn_cpw1 (syn_cpw1 (syn_cnnc)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_cpw1 (syn_c1c)) p0182 p0155
  have p0184 :=
    @g_complex
      (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
            (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                    (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik (syn_ccompl
                                  (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                      (syn_cins3k (syn_csik (syn_cssetk))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                  (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c)))
      p0183
  have p0185 :=
    @g_uni1ex
      (syn_ccompl (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
              (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_csik (syn_cssetk))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                    (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c))))
      p0184
  have p0186 :=
    @g_eqeltrri
      (syn_cuni1 (syn_ccompl (syn_cimak (syn_cin (syn_csik (syn_cssetk)) (syn_cimak
                (syn_cdif (syn_cins2k (syn_csik (syn_cssetk))) (syn_cins3k (syn_cimak (syn_cin
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_csik (syn_ccnvk
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccnvk (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_csik (syn_cssetk)))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cins3k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_cnnc))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_c1c)))))
      (.cab m (syn_wral a (.cv m) (syn_wral b (.cv m) (syn_wrex n (syn_cnnc)
              (syn_wa (.classMem (syn_cpw (.cv a)) (.cv n))
                (.classMem (syn_cpw (.cv b)) (.cv n)))))))
      (syn_cvv) p0146 p0185
  exact p0186


end NFChoice.DirectNominalPrf.WPPReplay
