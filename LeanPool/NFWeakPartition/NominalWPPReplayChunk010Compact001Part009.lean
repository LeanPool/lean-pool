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

/-- Checked nominal proof certificate identified upstream as `g_nnpweqlem1`. -/
@[expose]
noncomputable def gNnpweqlem1 (m : Var) (n : Var) (a : Var) (b : Var) (dv_a_b : a ≠ b)
    (dv_a_m : a ≠ m) (dv_a_n : a ≠ n) (dv_b_m : b ≠ m) (dv_b_n : b ≠ n)
    (_dv_m_n : m ≠ n) :
    Nominal.NPrf
      (.classMem (.cab m (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
                (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n))))))) (synCvv)) :=
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
  have dv_cache_0001 : t ∉ ((synCsn (synCsn (.cv a)))).fv := by
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
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
          (synCin (synCsik (synCssetk)) (synCimak
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
      ((synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))
              (synCpw1 (synCpw1 (synCnnc))))))).fv :=
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
  have dv_cache_0004 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synC1c))))).fv :=
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
    t ∉ ((synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc)))))))).fv :=
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
  have dv_cache_0008 : t ∉ ((synCsn (synCsn (synCsn (synCsn (.cv b)))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
            (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc)))))))).fv :=
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
      ((synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                        (synCimak (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                  (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))))).fv :=
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
  have dv_cache_0011 : t ∉ ((synCpw1 (synCpw1 (synCnnc)))).fv :=
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
    t ∉ ((synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))).fv :=
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
  have dv_cache_0014 : n ∉ ((synCnnc)).fv :=
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
      ((Wff.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have dv_cache_0016 : t ∉ ((synCnnc)).fv :=
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
  have dv_cache_0018 : t ∉ ((synCsn (synCsn (.cv n)))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv n)))
            (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
      ((synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))).fv :=
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
  have dv_cache_0021 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
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
  have dv_cache_0022 : t ∉ ((synCopk (.cv n) (synCsn (synCsn (.cv a))))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))).fv :=
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
  have dv_cache_0025 : t ∉ ((synCsn (synCsn (synCsn (.cv x))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
            (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin (synCins2k (synCsik
                (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))).fv :=
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
  have dv_cache_0027 : x ∉ ((synCpw (.cv a))).fv :=
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
      ((synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))).fv :=
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
  have dv_cache_0030 : t ∉ ((synCopk (.cv n) (synCsn (synCsn (.cv b))))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
            (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
            (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin (synCins2k (synCcnvk
                (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))).fv :=
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
  have dv_cache_0033 : x ∉ ((synCpw (.cv b))).fv :=
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
      ((synCin (synCsik (synCssetk)) (synCimak
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c))))))).fv :=
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
  have dv_cache_0035 : t ∉ ((synCpw1 (synC1c))).fv :=
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
  have dv_cache_0036 : t ∉ ((synCsn (.cv m))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
            (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                    (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
      ((synCuni1 (synCcompl (synCimak (synCin (synCsik (synCssetk)) (synCimak
                  (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                          (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                      (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                                (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCnnc))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c)))))).fv :=
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
  have p0000 := @gVex m
  have p0001 :=
    @gEluni1 (.cv m)
      (synCcompl (synCimak (synCin (synCsik (synCssetk)) (synCimak
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c))))
      p0000
  have p0002 := @gSnex (synCsn (.cv a))
  have p0003 := @gOpkeq1 (.cv t) (synCsn (synCsn (.cv a))) (synCsn (.cv m))
  have p0004 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv a))))
      (synCopk (.cv t) (synCsn (.cv m)))
      (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
      (synCin (synCsik (synCssetk)) (synCimak (synCdif (synCins2k (synCsik (synCssetk)))
            (synCins3k (synCimak (synCin (synCins2k (synCimak (synCin (synCins2k
                          (synCsik (synCcnvk (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0003
  have p0005 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
          (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                  (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
        (synCin (synCsik (synCssetk)) (synCimak
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      t (synCsn (synCsn (.cv a))) dv_cache_0001 dv_cache_0002 p0002 p0004
  have p0006 :=
    @gElin (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
      (synCsik (synCssetk))
      (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
  have p0007 := @gSnex (.cv a)
  have p0008 := @gOpksnelsik (synCsn (.cv a)) (.cv m) (synCssetk) p0007 p0000
  have p0009 := @gVex a
  have p0010 := @gElssetk (.cv a) (.cv m) p0009 p0000
  have p0011_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv a)) (.cv m)) (synCssetk)) (.objMem a m)) :=
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
      p0010
  have p0011 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv a)) (.cv m)) (synCssetk)) (.objMem a m) p0008
      p0011_e01_recanon
  have p0012 := @gOpkex (synCsn (synCsn (.cv a))) (synCsn (.cv m))
  have p0013 :=
    @gElimak t
      (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins2k
                (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                      (synCcnvk (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc))))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c))))
      (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))) dv_cache_0003 dv_cache_0004
      dv_cache_0005 p0012
  have p0014 := @gElpw131c b (.cv t) dv_cache_0006
  have p0015 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
        (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc)))))))
      p0014
  have p0016 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
        (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc)))))))
      b dv_cache_0007
  have p0017 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c))))) (.classMem
          (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc))))))))
      (synWa (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc))))))))
      (synWex b (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc)))))))))
      p0015 p0016
  have p0018 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c))))) (.classMem
          (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc))))))))
      (synWex b (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc)))))))))
      t p0017
  have p0019 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c)))) (.classMem
          (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc)))))))))
  have p0020 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))) (.classMem
          (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc))))))))
      b t
  have p0021 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc)))))))))
      (synWex t (synWex b
          (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))) (.classMem
              (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))))))
      (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c)))) (.classMem
          (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc))))))))
      (synWex b (synWex t
          (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))) (.classMem
              (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))))))
      p0018 p0019 p0020
  have p0022 := @gSnex (synCsn (synCsn (synCsn (.cv b))))
  have p0023 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))
      (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
  have p0024 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
      (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
        (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
      (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins2k
                (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                      (synCcnvk (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc))))))
      p0023
  have p0025 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
        (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc)))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
          (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
        (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc)))))))
      t (synCsn (synCsn (synCsn (synCsn (.cv b))))) dv_cache_0008 dv_cache_0009 p0022
      p0024
  have p0026 :=
    @gEldif
      (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
        (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
      (synCins2k (synCsik (synCssetk)))
      (synCins3k (synCimak (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik
                      (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc)))))
  have p0027 := @gSnex (synCsn (.cv b))
  have p0028 := @gSnex (.cv m)
  have p0029 :=
    @gOtkelins2k (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))
      (synCsn (.cv m)) (synCsik (synCssetk)) p0027 p0002 p0028
  have p0030 := @gSnex (.cv b)
  have p0031 := @gOpksnelsik (synCsn (.cv b)) (.cv m) (synCssetk) p0030 p0000
  have p0032 := @gVex b
  have p0033 := @gElssetk (.cv b) (.cv m) p0032 p0000
  have p0034_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv b)) (.cv m)) (synCssetk)) (.objMem b m)) :=
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
      p0033
  have p0034 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
          (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
        (synCins2k (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv b))) (synCsn (.cv m)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv b)) (.cv m)) (synCssetk)) (.objMem b m) p0029
      p0031 p0034_e02_recanon
  have p0035 :=
    @gOtkelins3k (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))
      (synCsn (.cv m))
      (synCimak (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                  (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc))))
      p0027 p0002 p0028
  have p0036 := @gOpkex (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))
  have p0037 :=
    @gElimak t
      (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                      (synCimak (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                (synCcnvk (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synCpw1 (synCnnc)))
      (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))) dv_cache_0010
      dv_cache_0011 dv_cache_0012 p0036
  have p0038 := @gElpw12 n (.cv t) (synCnnc) dv_cache_0013 dv_cache_0014
  have p0039 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCnnc))))
      (synWrex n (synCnnc) (.classEq (.cv t) (synCsn (synCsn (.cv n)))))
      (.classMem (synCopk (.cv t)
          (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
          (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                        (synCimak (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                  (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      p0038
  have p0040 :=
    @gR1941v (.classEq (.cv t) (synCsn (synCsn (.cv n))))
      (.classMem (synCopk (.cv t)
          (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
          (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                        (synCimak (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                  (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      n (synCnnc) dv_cache_0015
  have p0041 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCnnc)))) (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWa (synWrex n (synCnnc) (.classEq (.cv t) (synCsn (synCsn (.cv n))))) (.classMem
          (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))))
          (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWrex n (synCnnc) (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n)))) (.classMem
            (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
              (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                            (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                      (synCcnvk (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      p0039 p0040
  have p0042 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCnnc)))) (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWrex n (synCnnc) (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n)))) (.classMem
            (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
              (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                            (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                      (synCcnvk (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      t p0041
  have p0043 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synCnnc))) (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))))))
  have p0044 :=
    @gRexcom4
      (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n)))) (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      n t (synCnnc) dv_cache_0016 dv_cache_0017
  have p0045 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCnnc)))) (.classMem
            (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
              (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                            (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                      (synCcnvk (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex t (synWrex n (synCnnc) (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n))))
            (.classMem (synCopk (.cv t)
                (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWrex t (synCpw1 (synCpw1 (synCnnc))) (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWrex n (synCnnc) (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n))))
            (.classMem (synCopk (.cv t)
                (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      p0042 p0043 p0044
  have p0046 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))) (synCimak
          (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc)))))
      (synWrex t (synCpw1 (synCpw1 (synCnnc))) (.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWrex n (synCnnc) (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n))))
            (.classMem (synCopk (.cv t)
                (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      p0037 p0045
  have p0047 := @gSnex (synCsn (.cv n))
  have p0048 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (.cv n)))
      (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))
  have p0049 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv n))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))))
      (synCopk (synCsn (synCsn (.cv n)))
        (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))))
      (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                      (synCimak (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                (synCcnvk (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      p0048
  have p0050 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t)
          (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
          (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                        (synCimak (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                  (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (synCsn (synCsn (.cv n)))
          (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
          (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                        (synCimak (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                  (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      t (synCsn (synCsn (.cv n))) dv_cache_0018 dv_cache_0019 p0047 p0049
  have p0051 :=
    @gElin
      (synCopk (synCsn (synCsn (.cv n)))
        (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))))
      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
  have p0052 := @gOpkex (.cv n) (synCsn (synCsn (.cv a)))
  have p0053 :=
    @gElimak t
      (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (.cv n) (synCsn (synCsn (.cv a))))
      dv_cache_0020 dv_cache_0021 dv_cache_0022 p0052
  have p0054 := @gElpw121c x (.cv t) dv_cache_0023
  have p0055 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
          (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))
      p0054
  have p0056 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
          (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))
      x dv_cache_0024
  have p0057 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
              (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
      p0055 p0056
  have p0058 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
              (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
      t p0057
  have p0059 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
  have p0060 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      x t
  have p0061 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
              (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a)))))
              (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a)))))
              (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))))
      p0058 p0059 p0060
  have p0062 := @gSnex (synCsn (synCsn (.cv x)))
  have p0063 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (.cv n) (synCsn (synCsn (.cv a))))
  have p0064 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a)))))
      (synCopk (synCsn (synCsn (synCsn (.cv x))))
        (synCopk (.cv n) (synCsn (synCsn (.cv a)))))
      (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
      p0063
  have p0065 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
          (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin (synCins2k (synCsik
              (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                      (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
          (synCins3k (synCssetk))))
      t (synCsn (synCsn (synCsn (.cv x)))) dv_cache_0025 dv_cache_0026 p0062 p0064
  have p0066 :=
    @gElin
      (synCopk (synCsn (synCsn (synCsn (.cv x))))
        (synCopk (.cv n) (synCsn (synCsn (.cv a)))))
      (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synCins3k (synCssetk))
  have p0067 := @gSnex (.cv x)
  have p0068 := @gVex n
  have p0069 :=
    @gOtkelins2k (synCsn (.cv x)) (.cv n) (synCsn (synCsn (.cv a)))
      (synCsik (synCcnvk (synCcompl (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      p0067 p0068 p0002
  have p0070 := @gVex x
  have p0071 :=
    @gOpksnelsik (.cv x) (synCsn (.cv a))
      (synCcnvk (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0070 p0007
  have p0072 :=
    @gOpkelcnvk (.cv x) (synCsn (.cv a))
      (synCcompl (synCimak
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0070 p0007
  have p0073 := @gEqpwrelk (.cv a) (.cv x) p0009 p0070
  have p0074 :=
    @gBitri
      (.classMem (synCopk (.cv x) (synCsn (.cv a))) (synCcnvk (synCcompl (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (synCsn (.cv a)) (.cv x)) (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv x) (synCpw (.cv a))) p0072 p0073
  have p0075 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCins2k (synCsik (synCcnvk
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                    (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (.cv x)) (synCsn (synCsn (.cv a)))) (synCsik (synCcnvk
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                  (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (.cv x) (synCsn (.cv a))) (synCcnvk (synCcompl (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classEq (.cv x) (synCpw (.cv a))) p0069 p0071 p0074
  have p0076 :=
    @gOtkelins3k (synCsn (.cv x)) (.cv n) (synCsn (synCsn (.cv a))) (synCssetk) p0067
      p0068 p0002
  have p0077 := @gElssetk (.cv x) (.cv n) p0070 p0068
  have p0078_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv n)) (synCssetk)) (.objMem x n)) :=
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
      p0077
  have p0078 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCins3k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv n)) (synCssetk)) (.objMem x n) p0076
      p0078_e01_recanon
  have p0079 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCins2k (synCsik (synCcnvk
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                    (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))))
      (.classEq (.cv x) (synCpw (.cv a)))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCins3k (synCssetk)))
      (.objMem x n) p0075 p0078
  have p0080 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
              (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin (synCins2k (synCsik
              (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                      (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
          (synCins3k (synCssetk))))
      (synWa (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
            (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCins2k (synCsik (synCcnvk
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                      (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c))))))))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv x))))
            (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCins3k (synCssetk))))
      (synWa (.classEq (.cv x) (synCpw (.cv a))) (.objMem x n)) p0065 p0066 p0079
  have p0081 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
              (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
      (synWa (.classEq (.cv x) (synCpw (.cv a))) (.objMem x n)) x p0080
  have p0082 :=
    @gN3bitri
      (.classMem (synCopk (.cv n) (synCsn (synCsn (.cv a)))) (synCimak (synCin (synCins2k
              (synCsik (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a))))) (synCin
            (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv a)))))
              (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))))
      (synWex x (synWa (.classEq (.cv x) (synCpw (.cv a))) (.objMem x n))) p0053 p0061
      p0081
  have p0083 :=
    @gOtkelins2k (.cv n) (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))
      (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0068 p0027 p0002
  have p0084 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x
      (synCpw (.cv a)) (.cv n) dv_cache_0027 dv_cache_0028)
  have p0085_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCpw (.cv a)) (.cv n))
        (synWex x (synWa (.classEq (.cv x) (synCpw (.cv a))) (.objMem x n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCpw synWss synCin synCcompl synCnin synWnan synWa synWex
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
    @gN3bitr4i
      (.classMem (synCopk (.cv n) (synCsn (synCsn (.cv a)))) (synCimak (synCin (synCins2k
              (synCsik (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWex x (synWa (.classEq (.cv x) (synCpw (.cv a))) (.objMem x n)))
      (.classMem (synCopk (synCsn (synCsn (.cv n)))
          (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCins2k
          (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCpw (.cv a)) (.cv n)) p0082 p0083 p0085_e02_recanon
  have p0086 := @gOpkex (.cv n) (synCsn (synCsn (.cv b)))
  have p0087 :=
    @gElimak t
      (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) (synCopk (.cv n) (synCsn (synCsn (.cv b))))
      dv_cache_0029 dv_cache_0021 dv_cache_0030 p0086
  have p0088 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
      (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
          (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))
      p0054
  have p0089 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
          (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))
      x dv_cache_0031
  have p0090 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
            (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x))))))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
            (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
              (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
      p0088 p0089
  have p0091 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
            (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
              (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
      t p0090
  have p0092 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
            (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
  have p0093 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
            (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      x t
  have p0094 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
          (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
              (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
      (synWex t (synWex x (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b)))))
              (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
            (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b)))))
              (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))))
      p0091 p0092 p0093
  have p0095 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv x))))
      (synCopk (.cv n) (synCsn (synCsn (.cv b))))
  have p0096 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
      (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b)))))
      (synCopk (synCsn (synCsn (synCsn (.cv x))))
        (synCopk (.cv n) (synCsn (synCsn (.cv b)))))
      (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
      p0095
  have p0097 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
          (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin (synCins2k (synCcnvk
              (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                      (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
          (synCins3k (synCssetk))))
      t (synCsn (synCsn (synCsn (.cv x)))) dv_cache_0025 dv_cache_0032 p0062 p0096
  have p0098 :=
    @gElin
      (synCopk (synCsn (synCsn (synCsn (.cv x))))
        (synCopk (.cv n) (synCsn (synCsn (.cv b)))))
      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synCins3k (synCssetk))
  have p0099 :=
    @gOtkelins2k (synCsn (.cv x)) (.cv n) (synCsn (synCsn (.cv b)))
      (synCcnvk (synCsik (synCcompl (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      p0067 p0068 p0027
  have p0100 :=
    @gOpkelcnvk (synCsn (.cv x)) (synCsn (synCsn (.cv b)))
      (synCsik (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0067 p0027
  have p0101 :=
    @gOpksnelsik (synCsn (.cv b)) (.cv x)
      (synCcompl (synCimak
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0030 p0070
  have p0102 := @gEqpwrelk (.cv b) (.cv x) p0032 p0070
  have p0103 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv b))) (synCsn (.cv x))) (synCsik (synCcompl
            (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (synCsn (.cv b)) (.cv x)) (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classEq (.cv x) (synCpw (.cv b))) p0101 p0102
  have p0104 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCins2k (synCcnvk (synCsik
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                    (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (.cv x)) (synCsn (synCsn (.cv b)))) (synCcnvk (synCsik
            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                  (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (synCsn (synCsn (.cv b))) (synCsn (.cv x))) (synCsik (synCcompl
            (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classEq (.cv x) (synCpw (.cv b))) p0099 p0100 p0103
  have p0105 :=
    @gOtkelins3k (synCsn (.cv x)) (.cv n) (synCsn (synCsn (.cv b))) (synCssetk) p0067
      p0068 p0027
  have p0106_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv n)) (synCssetk)) (.objMem x n)) :=
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
      p0077
  have p0106 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCins3k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv n)) (synCssetk)) (.objMem x n) p0105
      p0106_e01_recanon
  have p0107 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCins2k (synCcnvk (synCsik
              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                    (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c)))))))))
      (.classEq (.cv x) (synCpw (.cv b)))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCins3k (synCssetk)))
      (.objMem x n) p0104 p0106
  have p0108 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
              (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
          (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin (synCins2k (synCcnvk
              (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                      (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
          (synCins3k (synCssetk))))
      (synWa (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x))))
            (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCins2k (synCcnvk (synCsik
                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                      (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c))))))))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (.cv x))))
            (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCins3k (synCssetk))))
      (synWa (.classEq (.cv x) (synCpw (.cv b))) (.objMem x n)) p0097 p0098 p0107
  have p0109 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
          (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
              (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk))))))
      (synWa (.classEq (.cv x) (synCpw (.cv b))) (.objMem x n)) x p0108
  have p0110 :=
    @gN3bitri
      (.classMem (synCopk (.cv n) (synCsn (synCsn (.cv b)))) (synCimak (synCin (synCins2k
              (synCcnvk (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWrex t (synCpw1 (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b))))) (synCin
            (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))
      (synWex x (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv x)))))
            (.classMem (synCopk (.cv t) (synCopk (.cv n) (synCsn (synCsn (.cv b)))))
              (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))))))
      (synWex x (synWa (.classEq (.cv x) (synCpw (.cv b))) (.objMem x n))) p0087 p0094
      p0109
  have p0111 :=
    @gOtkelins3k (.cv n) (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))
      (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0068 p0027 p0002
  have p0112 :=
    (NFChoice.DirectNominalPrf.Nominal.DefinitionLeafHandlersCanonical001.dfClelOfDV x
      (synCpw (.cv b)) (.cv n) dv_cache_0033 dv_cache_0028)
  have p0113_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCpw (.cv b)) (.cv n))
        (synWex x (synWa (.classEq (.cv x) (synCpw (.cv b))) (.objMem x n)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCpw synWss synCin synCcompl synCnin synWnan synWa synWex
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
    @gN3bitr4i
      (.classMem (synCopk (.cv n) (synCsn (synCsn (.cv b)))) (synCimak (synCin (synCins2k
              (synCcnvk (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synWex x (synWa (.classEq (.cv x) (synCpw (.cv b))) (.objMem x n)))
      (.classMem (synCopk (synCsn (synCsn (.cv n)))
          (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCins3k
          (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCpw (.cv b)) (.cv n)) p0110 p0111 p0113_e02_recanon
  have p0114 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (.cv n)))
          (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCins2k
          (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCpw (.cv a)) (.cv n))
      (.classMem (synCopk (synCsn (synCsn (.cv n)))
          (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCins3k
          (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCpw (.cv b)) (.cv n)) p0085 p0113
  have p0115 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n)))) (.classMem
            (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
              (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                            (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                      (synCcnvk (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (synCsn (.cv n)))
          (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
          (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                        (synCimak (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                  (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (.classMem (synCopk (synCsn (synCsn (.cv n)))
            (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCins2k
            (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (.classMem
          (synCopk (synCsn (synCsn (.cv n)))
            (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCins3k
            (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (.classMem (synCpw (.cv a)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      p0050 p0051 p0114
  have p0116 :=
    @gRexbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n)))) (.classMem
            (synCopk (.cv t)
              (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
              (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                            (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                      (synCcnvk (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.classMem (synCpw (.cv a)) (.cv n)) (.classMem (synCpw (.cv b)) (.cv n)))
      n (synCnnc) p0115
  have p0117 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
          (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))) (synCins3k (synCimak
            (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                      (synCcnvk (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc))))))
      (.classMem (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a)))) (synCimak
          (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc)))))
      (synWrex n (synCnnc) (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv n))))
            (.classMem (synCopk (.cv t)
                (synCopk (synCsn (synCsn (.cv b))) (synCsn (synCsn (.cv a))))) (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      p0035 p0046 p0116
  have p0118 :=
    @gNotbii
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
          (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))) (synCins3k (synCimak
            (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                      (synCcnvk (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc))))))
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      p0117
  have p0119 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
          (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
        (synCins2k (synCsik (synCssetk))))
      (.objMem b m)
      (.neg (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
            (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))) (synCins3k (synCimak
              (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc)))))))
      (.neg (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      p0034 p0118
  have p0120 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc)))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
          (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
        (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc)))))))
      (synWa (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
            (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          (synCins2k (synCsik (synCssetk)))) (.neg (.classMem
            (synCopk (synCsn (synCsn (synCsn (synCsn (.cv b)))))
              (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))) (synCins3k (synCimak
                (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                              (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc))))))))
      (synWa (.objMem b m) (.neg (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      p0025 p0026 p0119
  have p0121 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b))))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc)))))))))
      (synWa (.objMem b m) (.neg (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      b p0120
  have p0122 :=
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))) (synCimak
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWrex t (synCpw1 (synCpw1 (synCpw1 (synC1c)))) (.classMem
          (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc))))))))
      (synWex b (synWex t
          (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (.cv b)))))) (.classMem
              (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))))
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))))))
      (synWex b (synWa (.objMem b m) (.neg (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      p0013 p0021 p0121
  have p0123 :=
    (Nominal.biimpRefl (synWrex b (.cv m) (.neg (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n)))))))
  have p0124 :=
    @gRexnal
      (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
          (.classMem (synCpw (.cv b)) (.cv n))))
      b (.cv m)
  have p0125_e01_recanon :
    Nominal.NPrf
      (synWb (synWrex b (.cv m) (.neg (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))) (synWex b (synWa (.objMem b m) (.neg
              (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n)))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa]
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
    @gN3bitr2i
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))) (synCimak
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex b (synWa (.objMem b m) (.neg (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      (synWrex b (.cv m) (.neg (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      (.neg (synWral b (.cv m) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      p0122 p0125_e01_recanon p0124
  have p0126 :=
    @gAnbi12i
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
        (synCsik (synCssetk)))
      (.objMem a m)
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))) (synCimak
          (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                  (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                (synCimak (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (.neg (synWral b (.cv m) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      p0011 p0125
  have p0127 :=
    @gN3bitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a))))
          (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
              (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                      (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCnnc))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
        (synCin (synCsik (synCssetk)) (synCimak
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m)))
          (synCsik (synCssetk)))
        (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (.cv m))) (synCimak
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWa (.objMem a m) (.neg (synWral b (.cv m) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      p0005 p0006 p0126
  have p0128 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a))))
          (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
              (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                      (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCnnc))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (.objMem a m) (.neg (synWral b (.cv m) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      a p0127
  have p0129 :=
    @gElimak t
      (synCin (synCsik (synCssetk)) (synCimak (synCdif (synCins2k (synCsik (synCssetk)))
            (synCins3k (synCimak (synCin (synCins2k (synCimak (synCin (synCins2k
                          (synCsik (synCcnvk (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synC1c)) (synCsn (.cv m)) dv_cache_0034 dv_cache_0035 dv_cache_0036
      p0028
  have p0130 := @gElpw11c a (.cv t) dv_cache_0037
  have p0131 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex a (.classEq (.cv t) (synCsn (synCsn (.cv a)))))
      (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
          (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                  (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0130
  have p0132 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv a))))
      (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
          (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                  (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      a dv_cache_0038
  have p0133 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
            (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                    (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synWa (synWex a (.classEq (.cv t) (synCsn (synCsn (.cv a)))))
        (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
            (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                    (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synWex a (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a))))
          (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
              (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                      (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCnnc))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0131 p0132
  have p0134 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
            (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                    (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synWex a (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a))))
          (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
              (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                      (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCnnc))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      t p0133
  have p0135 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synC1c))
        (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
            (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                    (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
  have p0136 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a))))
        (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
            (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                    (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      a t
  have p0137 :=
    @gN3bitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
          (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
              (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                      (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCnnc))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex t (synWex a (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a))))
            (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
                (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                        (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik
                                    (synCcnvk (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                                (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCnnc))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synWrex t (synCpw1 (synC1c)) (.classMem (synCopk (.cv t) (synCsn (.cv m)))
          (synCin (synCsik (synCssetk)) (synCimak
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synWex a (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a))))
            (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
                (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                        (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik
                                    (synCcnvk (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                                (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCnnc))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      p0134 p0135 p0136
  have p0138 :=
    @gBitri
      (.classMem (synCsn (.cv m)) (synCimak (synCin (synCsik (synCssetk)) (synCimak
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c))))
      (synWrex t (synCpw1 (synC1c)) (.classMem (synCopk (.cv t) (synCsn (.cv m)))
          (synCin (synCsik (synCssetk)) (synCimak
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synWex a (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a))))
            (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
                (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                        (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik
                                    (synCcnvk (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                                (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCnnc))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      p0129 p0137
  have p0139 :=
    (Nominal.biimpRefl (synWrex a (.cv m) (.neg (synWral b (.cv m) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n))))))))
  have p0140_e02_recanon :
    Nominal.NPrf
      (synWb (synWrex a (.cv m) (.neg (synWral b (.cv m) (synWrex n (synCnnc)
                (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n))))))) (synWex a (synWa (.objMem a m)
            (.neg (synWral b (.cv m) (synWrex n (synCnnc)
                  (synWa (.classMem (synCpw (.cv a)) (.cv n))
                    (.classMem (synCpw (.cv b)) (.cv n))))))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWrex, synWex, synWa, synWral]
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
    @gN3bitr4i
      (synWex a (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv a))))
            (.classMem (synCopk (.cv t) (synCsn (.cv m))) (synCin (synCsik (synCssetk))
                (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                        (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik
                                    (synCcnvk (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                                (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCnnc))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex a (synWa (.objMem a m) (.neg (synWral b (.cv m) (synWrex n (synCnnc)
                (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n))))))))
      (.classMem (synCsn (.cv m)) (synCimak (synCin (synCsik (synCssetk)) (synCimak
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c))))
      (synWrex a (.cv m) (.neg (synWral b (.cv m) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      p0128 p0138 p0140_e02_recanon
  have p0141 :=
    @gNotbii
      (.classMem (synCsn (.cv m)) (synCimak (synCin (synCsik (synCssetk)) (synCimak
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c))))
      (synWrex a (.cv m) (.neg (synWral b (.cv m) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      p0140
  have p0142 :=
    @gElcompl (synCsn (.cv m))
      (synCimak (synCin (synCsik (synCssetk)) (synCimak
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c)))
      p0028
  have p0143 :=
    @gDfral2
      (synWral b (.cv m) (synWrex n (synCnnc) (synWa (.classMem (synCpw (.cv a)) (.cv n))
            (.classMem (synCpw (.cv b)) (.cv n)))))
      a (.cv m)
  have p0144 :=
    @gN3bitr4i
      (.neg (.classMem (synCsn (.cv m)) (synCimak (synCin (synCsik (synCssetk)) (synCimak
                (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                        (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCnnc))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c)))))
      (.neg (synWrex a (.cv m) (.neg (synWral b (.cv m) (synWrex n (synCnnc)
                (synWa (.classMem (synCpw (.cv a)) (.cv n))
                  (.classMem (synCpw (.cv b)) (.cv n))))))))
      (.classMem (synCsn (.cv m)) (synCcompl (synCimak (synCin (synCsik (synCssetk))
              (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                      (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCnnc))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c)))))
      (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      p0141 p0142 p0143
  have p0145 :=
    @gBitri
      (.classMem (.cv m) (synCuni1 (synCcompl (synCimak (synCin (synCsik (synCssetk))
                (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                        (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik
                                    (synCcnvk (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                                (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synCnnc))))))
                  (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c))))))
      (.classMem (synCsn (.cv m)) (synCcompl (synCimak (synCin (synCsik (synCssetk))
              (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak
                      (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCnnc))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c)))))
      (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      p0001 p0144
  have p0146 :=
    @gEqabi
      (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
            (synWa (.classMem (synCpw (.cv a)) (.cv n))
              (.classMem (synCpw (.cv b)) (.cv n))))))
      m
      (synCuni1 (synCcompl (synCimak (synCin (synCsik (synCssetk)) (synCimak
                (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                        (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCnnc))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c)))))
      dv_cache_0039 p0145
  have p0147 := @gSsetkex
  have p0148 := @gSikex (synCssetk) p0147
  have p0149 := @gIns2kex (synCsik (synCssetk)) p0148
  have p0151 := @gIns2kex (synCssetk) p0147
  have p0152 := @gIns3kex (synCsik (synCssetk)) p0148
  have p0153 :=
    @gSymdifex (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))) p0151 p0152
  have p0154 := @gN1cex
  have p0155 := @gPw1ex (synC1c) p0154
  have p0156 := @gPw1ex (synCpw1 (synC1c)) p0155
  have p0157 :=
    @gImakex (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
      (synCpw1 (synCpw1 (synC1c))) p0153 p0156
  have p0158 :=
    @gComplex
      (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
        (synCpw1 (synCpw1 (synC1c))))
      p0157
  have p0159 :=
    @gCnvkex
      (synCcompl (synCimak
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0158
  have p0160 :=
    @gSikex
      (synCcnvk (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0159
  have p0161 :=
    @gIns2kex
      (synCsik (synCcnvk (synCcompl (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      p0160
  have p0163 := @gIns3kex (synCssetk) p0147
  have p0164 :=
    @gInex
      (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synCins3k (synCssetk)) p0161 p0163
  have p0165 :=
    @gImakex
      (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0164 p0156
  have p0166 :=
    @gIns2kex
      (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0165
  have p0167 :=
    @gSikex
      (synCcompl (synCimak
          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
          (synCpw1 (synCpw1 (synC1c)))))
      p0158
  have p0168 :=
    @gCnvkex
      (synCsik (synCcompl (synCimak
            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
            (synCpw1 (synCpw1 (synC1c))))))
      p0167
  have p0169 :=
    @gIns2kex
      (synCcnvk (synCsik (synCcompl (synCimak
              (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
              (synCpw1 (synCpw1 (synC1c)))))))
      p0168
  have p0170 :=
    @gInex
      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synCins3k (synCssetk)) p0169 p0163
  have p0171 :=
    @gImakex
      (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0170 p0156
  have p0172 :=
    @gIns3kex
      (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCsik (synCssetk))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))
      p0171
  have p0173 :=
    @gInex
      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCssetk))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
          (synCpw1 (synCpw1 (synC1c)))))
      p0166 p0172
  have p0174 := @gNncex
  have p0175 := @gPw1ex (synCnnc) p0174
  have p0176 := @gPw1ex (synCpw1 (synCnnc)) p0175
  have p0177 :=
    @gImakex
      (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                      (synCimak (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                (synCcnvk (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCsik (synCssetk))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
            (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synCpw1 (synCnnc))) p0173 p0176
  have p0178 :=
    @gIns3kex
      (synCimak (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                  (synCcnvk (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCssetk))))
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc))))
      p0177
  have p0179 :=
    @gDifex (synCins2k (synCsik (synCssetk)))
      (synCins3k (synCimak (synCin (synCins2k (synCimak (synCin (synCins2k (synCsik
                      (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                    (synCcnvk (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCssetk))))
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc)))))
      p0149 p0178
  have p0180 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0156
  have p0181 :=
    @gImakex
      (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin (synCins2k
                (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin (synCins2k
                      (synCcnvk (synCsik (synCcompl (synCimak
                              (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCsik (synCssetk))))
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc))))))
      (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0179 p0180
  have p0182 :=
    @gInex (synCsik (synCssetk))
      (synCimak (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                              (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c))))) (synCins3k (synCimak (synCin
                      (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCsik (synCssetk))))
                                (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synCnnc))))))
        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      p0148 p0181
  have p0183 :=
    @gImakex
      (synCin (synCsik (synCssetk)) (synCimak (synCdif (synCins2k (synCsik (synCssetk)))
            (synCins3k (synCimak (synCin (synCins2k (synCimak (synCin (synCins2k
                          (synCsik (synCcnvk (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))) (synCins3k
                    (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk))
                                    (synCins3k (synCsik (synCssetk))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                (synCpw1 (synCpw1 (synCnnc)))))) (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synCpw1 (synC1c)) p0182 p0155
  have p0184 :=
    @gComplex
      (synCimak (synCin (synCsik (synCssetk)) (synCimak
            (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                    (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                    (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik (synCcompl
                                  (synCimak (synCsymdif (synCins2k (synCssetk))
                                      (synCins3k (synCsik (synCssetk))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                  (synCpw1 (synCpw1 (synCnnc))))))
            (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c)))
      p0183
  have p0185 :=
    @gUni1ex
      (synCcompl (synCimak (synCin (synCsik (synCssetk)) (synCimak
              (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                      (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                      (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCsik (synCssetk))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                    (synCpw1 (synCpw1 (synCnnc))))))
              (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c))))
      p0184
  have p0186 :=
    @gEqeltrri
      (synCuni1 (synCcompl (synCimak (synCin (synCsik (synCssetk)) (synCimak
                (synCdif (synCins2k (synCsik (synCssetk))) (synCins3k (synCimak (synCin
                        (synCins2k (synCimak (synCin (synCins2k (synCsik (synCcnvk
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))
                        (synCins3k (synCimak (synCin (synCins2k (synCcnvk (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCsik (synCssetk)))) (synCpw1 (synCpw1 (synC1c))))))))
                              (synCins3k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synCnnc))))))
                (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synC1c)))))
      (.cab m (synWral a (.cv m) (synWral b (.cv m) (synWrex n (synCnnc)
              (synWa (.classMem (synCpw (.cv a)) (.cv n))
                (.classMem (synCpw (.cv b)) (.cv n)))))))
      (synCvv) p0146 p0185
  exact p0186


end NFChoice.DirectNominalPrf.WPPReplay
