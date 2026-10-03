/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block001

/-! NF weak partition development: NominalWPPReplayChunk010Compact001Part003. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_evenodddisjlem1 (j : Var) (n : Var) (dv_j_n : j ≠ n) :
    Nominal.NPrf
      (.classMem (.cab j (.imp (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0))
            (syn_wral n (syn_cnnc)
              (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))
                (syn_wne (syn_cplc (.cv j) (.cv j))
                  (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))))) (syn_cvv)) :=
  by
  let proofSupport : Finset Var := ({ j } : Finset Var) ∪ ({ n } : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let a : Var := freshVar proofSupport 2
  let b : Var := freshVar proofSupport 3
  let t : Var := freshVar proofSupport 4
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_ne_j : x ≠ j := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_n : x ≠ n := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_n_ne_x : n ≠ x := Ne.symm fresh_x_ne_n
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_j : y ≠ j := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_y_ne_n : y ≠ n := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_a : a ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_a_ne_j : a ≠ j := by
    intro h
    exact fresh_a (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_a_ne_n : a ≠ n := by
    intro h
    exact fresh_a (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_b : b ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_b_ne_j : b ≠ j := by
    intro h
    exact fresh_b (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_b_ne_n : b ≠ n := by
    intro h
    exact fresh_b (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_t_ne_j : t ≠ j := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_singleton.mpr h))
  have fresh_t_ne_n : t ≠ n := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (Finset.mem_singleton.mpr h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_a : x ≠ a :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_b : x ≠ b :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_a : y ≠ a :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_a_ne_y : a ≠ y := Ne.symm fresh_y_ne_a
  have fresh_y_ne_b : y ≠ b :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_b_ne_y : b ≠ y := Ne.symm fresh_y_ne_b
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_a_ne_b : a ≠ b :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_b_ne_a : b ≠ a := Ne.symm fresh_a_ne_b
  have fresh_a_ne_t : a ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_t_ne_a : t ≠ a := Ne.symm fresh_a_ne_t
  have fresh_b_ne_t : b ≠ t :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_t_ne_b : t ≠ b := Ne.symm fresh_b_ne_t
  have dv_cache_0001 :
    x ∉
      ((syn_cin (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                        (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k
                              (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                        (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k
                                    (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
                                    (syn_cins3k (syn_csik (syn_csik
        (syn_csik (syn_csik (syn_csik (syn_cssetk))))))) (syn_cins2k (syn_cins3k
                                        (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
          (syn_cxpk (syn_cun (syn_csn (syn_c0)) (syn_ccompl (syn_cimak (syn_cimak (syn_cin
                      (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                                        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak (syn_cin
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl (syn_cins3k (syn_ccnvk
        (syn_csik (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
        (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k
        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cins3k (syn_cimagek
                                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c))))
                      (syn_cins2k
                        (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))))
                    (syn_cpw1 (syn_c1c))) (syn_cnnc)))) (syn_cvv)))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : x ∉ ((Class.cv j)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_j, not_false_eq_true])
  have dv_cache_0003 :
    t ∉
      ((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                  (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k (syn_csik
                          (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak
                          (syn_csymdif
                            (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                            (syn_cun (syn_cins3k (syn_csik (syn_csik
                                    (syn_csik (syn_csik (syn_csik (syn_cssetk))))))) (syn_cins2k
                                (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0004 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
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
  have dv_cache_0005 : t ∉ ((syn_copk (.cv x) (.cv j))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_j, or_false, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0007 :
    y ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv j)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                    (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k
                          (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                    (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k
                                (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
                                (syn_cins3k (syn_csik (syn_csik
                                      (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
                                (syn_cins2k (syn_cins3k
                                    (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))) (syn_cpw1
                              (syn_cpw1 (syn_cpw1 (syn_cpw1
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_x, fresh_y_ne_j,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv y))))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
          not_false_eq_true])
  have dv_cache_0009 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv j)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                    (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k
                          (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                    (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k
                                (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
                                (syn_cins3k (syn_csik (syn_csik
                                      (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
                                (syn_cins2k (syn_cins3k
                                    (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))) (syn_cpw1
                              (syn_cpw1 (syn_cpw1 (syn_cpw1
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, fresh_t_ne_j,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 :
    t ∉
      ((syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
            (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k (syn_csik
                    (syn_csik (syn_csik (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                      (syn_cun (syn_cins3k (syn_csik
                            (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
                        (syn_cins2k
                          (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0011 : t ∉ ((syn_copk (syn_csn (.cv y)) (.cv j))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_j, or_false, not_false_eq_true])
  have dv_cache_0012 : b ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_t, not_false_eq_true])
  have dv_cache_0013 :
    b ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv y)) (.cv j)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
              (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k (syn_csik
                      (syn_csik (syn_csik (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak
                      (syn_csymdif
                        (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
                          (syn_cins3k (syn_csik
                              (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
                          (syn_cins2k
                            (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_t, fresh_b_ne_y, fresh_b_ne_j,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0014 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv b))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_b,
          not_false_eq_true])
  have dv_cache_0015 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
            (syn_copk (syn_csn (.cv y)) (.cv j))) (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
              (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k (syn_csik
                      (syn_csik (syn_csik (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak
                      (syn_csymdif
                        (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
                          (syn_cins3k (syn_csik
                              (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
                          (syn_cins2k
                            (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_b, fresh_t_ne_y, fresh_t_ne_j,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    t ∉
      ((syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k (syn_csik (syn_csik
                  (syn_csik (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                  (syn_cun (syn_cins3k
                      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
                    (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0017 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0018 :
    t ∉
      ((syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_copk (syn_csn (.cv y)) (.cv j)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_b, fresh_t_ne_y, fresh_t_ne_j, or_false,
          not_false_eq_true])
  have dv_cache_0019 : a ∉ ((Class.cv t)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_t, not_false_eq_true])
  have dv_cache_0020 :
    a ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
              (syn_copk (syn_csn (.cv y)) (.cv j))))
          (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k (syn_csik
                  (syn_csik (syn_csik (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                    (syn_cun (syn_cins3k (syn_csik
                          (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))) (syn_cins2k
                        (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))) (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_t, fresh_a_ne_b, fresh_a_ne_y, fresh_a_ne_j,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_a,
          not_false_eq_true])
  have dv_cache_0022 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
            (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
              (syn_copk (syn_csn (.cv y)) (.cv j))))
          (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k (syn_csik
                  (syn_csik (syn_csik (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                    (syn_cun (syn_cins3k (syn_csik
                          (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))) (syn_cins2k
                        (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))) (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_b, fresh_t_ne_y, fresh_t_ne_j,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0023 :
    t ∉
      ((syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
            (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
            (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0024 :
    t ∉
      ((syn_cpw1 (syn_cpw1
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0025 :
    t ∉
      ((syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
            (syn_copk (syn_csn (.cv y)) (.cv j))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_b, fresh_t_ne_y, fresh_t_ne_j,
          or_false, not_false_eq_true])
  have dv_cache_0026 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0027 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
              (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
                (syn_copk (syn_csn (.cv y)) (.cv j)))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
              (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
              (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_a, fresh_x_ne_b, fresh_x_ne_y,
          fresh_x_ne_j, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0028 :
    t ∉
      ((syn_csn (syn_csn
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0029 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
              (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
                (syn_copk (syn_csn (.cv y)) (.cv j)))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
              (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
              (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_a, fresh_t_ne_b, fresh_t_ne_y,
          fresh_t_ne_j, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0030 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
  have dv_cache_0031 : x ∉ ((syn_cun (.cv a) (.cv b))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_a, fresh_x_ne_b, or_false, not_false_eq_true])
  have dv_cache_0032 : a ∉ ((Class.cv j)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_j, not_false_eq_true])
  have dv_cache_0033 : b ∉ ((Class.cv j)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_j, not_false_eq_true])
  have dv_cache_0034 : b ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact (show b ≠ a from (by exact fresh_b_ne_a))
  have dv_cache_0035 : y ∉ ((Class.cv j)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_j, not_false_eq_true])
  have dv_cache_0036 : y ≠ a :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show y ≠ a from (by exact fresh_y_ne_a))
  have dv_cache_0037 : y ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036
    exact (show y ≠ b from (by exact fresh_y_ne_b))
  have dv_cache_0038 : a ≠ b :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037
    exact (show a ≠ b from (by exact fresh_a_ne_b))
  have dv_cache_0039 : y ∉ ((Class.cv x)).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0040 :
    n ∉
      ((syn_cimak (syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                                  (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin
                                      (syn_ccompl (syn_cins3k (syn_ccnvk (syn_csik (syn_csik
        (syn_csik (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun (syn_cins2k (syn_cins3k
        (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k (syn_csik (syn_csik
        (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cins3k (syn_cimagek (syn_cimak
                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c))))
            (syn_cins2k (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))))
          (syn_cpw1 (syn_c1c)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0041 : n ∉ ((syn_cnnc)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0042 : n ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_n_ne_x, not_false_eq_true])
  have dv_cache_0043 :
    t ∉
      ((syn_cin (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                                (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin
                                    (syn_ccompl (syn_cins3k (syn_ccnvk (syn_csik (syn_csik
        (syn_csik (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun (syn_cins2k (syn_cins3k
        (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k (syn_csik (syn_csik
        (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cins3k (syn_cimagek (syn_cimak
                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c)))) (syn_cins2k
            (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0044 : t ∉ ((syn_cpw1 (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0045 : t ∉ ((syn_copk (.cv n) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_n, fresh_t_ne_x, or_false, not_false_eq_true])
  have dv_cache_0046 :
    y ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv n) (.cv x))) (syn_cin (syn_cins3k
              (syn_cimak (syn_cin (syn_cins2k (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                                  (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin
                                      (syn_ccompl (syn_cins3k (syn_ccnvk (syn_csik (syn_csik
        (syn_csik (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun (syn_cins2k (syn_cins3k
        (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k (syn_csik (syn_csik
        (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cins3k (syn_cimagek (syn_cimak
                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c)))) (syn_cins2k
              (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_n, fresh_y_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0047 : t ∉ ((syn_csn (syn_csn (.cv y)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
          not_false_eq_true])
  have dv_cache_0048 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (.cv x))) (syn_cin
            (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                                  (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin
                                      (syn_ccompl (syn_cins3k (syn_ccnvk (syn_csik (syn_csik
        (syn_csik (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun (syn_cins2k (syn_cins3k
        (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k (syn_csik (syn_csik
        (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cins3k (syn_cimagek (syn_cimak
                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c)))) (syn_cins2k
              (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_n, fresh_t_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0049 :
    t ∉
      ((syn_cin (syn_cins2k (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                          (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl
                                (syn_cins3k (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                                    (syn_cun (syn_cins2k (syn_cins3k
        (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k (syn_csik (syn_csik
        (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
                                        (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
          (syn_cins3k (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0050 : t ∉ ((syn_copk (.cv y) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_n, or_false, not_false_eq_true])
  have dv_cache_0051 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv n))) (syn_cin (syn_cins2k
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                      (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                            (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl
                                  (syn_cins3k (syn_ccnvk (syn_csik (syn_csik (syn_csik
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k
                                        (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_csik
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k (syn_csik (syn_csik (syn_csik
        (syn_csik (syn_csik (syn_cssetk))))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
            (syn_cins3k (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_y, fresh_x_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0052 : t ∉ ((syn_csn (syn_csn (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0053 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv n))) (syn_cin
            (syn_cins2k (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                            (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl
                                  (syn_cins3k (syn_ccnvk (syn_csik (syn_csik (syn_csik
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k
                                        (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_csik
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k (syn_csik (syn_csik (syn_csik
        (syn_csik (syn_csik (syn_cssetk))))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
            (syn_cins3k (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0054 :
    t ∉
      ((syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                  (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl
                        (syn_cins3k (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak
                                    (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl
                        (syn_cimak (syn_csymdif
                            (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                            (syn_cun (syn_cins2k (syn_cins3k
                                  (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k
                                (syn_csik (syn_csik
                                    (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))) (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0055 : t ∉ ((syn_copk (.cv x) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_n, or_false, not_false_eq_true])
  have dv_cache_0056 :
    y ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv n)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                    (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl
                          (syn_cins3k (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak
                                      (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k
                                (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
                                (syn_cins2k (syn_cins3k
                                    (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k
                                  (syn_csik (syn_csik
                                      (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_x, fresh_y_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0057 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv n)))
          (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cimak
                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                    (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl
                          (syn_cins3k (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak
                                      (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k
                                (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
                                (syn_cins2k (syn_cins3k
                                    (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k
                                  (syn_csik (syn_csik
                                      (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, fresh_t_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0058 :
    t ∉
      ((syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
            (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl (syn_cins3k
                    (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                      (syn_cun (syn_cins2k
                          (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cins3k (syn_csik
                            (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0059 : t ∉ ((syn_copk (syn_csn (.cv y)) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058
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
  have dv_cache_0060 :
    a ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv y)) (.cv n)))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
              (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl (syn_cins3k
                      (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak
                      (syn_csymdif
                        (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
                          (syn_cins2k
                            (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cins3k (syn_csik
                              (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_a_ne_t, fresh_a_ne_y, fresh_a_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0061 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv a))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_a,
          not_false_eq_true])
  have dv_cache_0062 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
            (syn_copk (syn_csn (.cv y)) (.cv n))) (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
              (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl (syn_cins3k
                      (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak
                      (syn_csymdif
                        (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
                          (syn_cins2k
                            (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cins3k (syn_csik
                              (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_y, fresh_t_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0063 :
    t ∉
      ((syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl (syn_cins3k
                (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                  (syn_cun (syn_cins2k
                      (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k
                      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0064 :
    t ∉
      ((syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
          (syn_copk (syn_csn (.cv y)) (.cv n)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_a, fresh_t_ne_y, fresh_t_ne_n, or_false,
          not_false_eq_true])
  have dv_cache_0065 :
    b ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
              (syn_copk (syn_csn (.cv y)) (.cv n))))
          (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl (syn_cins3k
                  (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                    (syn_cun (syn_cins2k
                        (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k
                        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_b_ne_t, fresh_b_ne_a, fresh_b_ne_y, fresh_b_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0066 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_b,
          not_false_eq_true])
  have dv_cache_0067 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
            (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
              (syn_copk (syn_csn (.cv y)) (.cv n))))
          (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl (syn_cins3k
                  (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                    (syn_cun (syn_cins2k
                        (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k
                        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_b, fresh_t_ne_a, fresh_t_ne_y, fresh_t_ne_n,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0068 :
    t ∉
      ((syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
          (syn_cun (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cins3k (syn_csik
                (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0069 :
    t ∉
      ((syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
            (syn_copk (syn_csn (.cv y)) (.cv n))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_b, fresh_t_ne_a, fresh_t_ne_y, fresh_t_ne_n,
          or_false, not_false_eq_true])
  have dv_cache_0070 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
              (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
                (syn_copk (syn_csn (.cv y)) (.cv n)))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
              (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cins3k (syn_csik
                  (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_ne_b, fresh_x_ne_a, fresh_x_ne_y,
          fresh_x_ne_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0071 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn
                (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
              (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
                (syn_copk (syn_csn (.cv y)) (.cv n)))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
              (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cins3k (syn_csik
                  (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_b, fresh_t_ne_a, fresh_t_ne_y,
          fresh_t_ne_n, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0072 : y ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_n, not_false_eq_true])
  have dv_cache_0073 : a ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072
    exact
      (by
        have compact_fv_not_mem_empty : a ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_a_ne_n, not_false_eq_true])
  have dv_cache_0074 : b ∉ ((Class.cv n)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073
    exact
      (by
        have compact_fv_not_mem_empty : b ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_b_ne_n, not_false_eq_true])
  have dv_cache_0075 : x ∉ ((syn_cplc (.cv n) (.cv n))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_n, or_false, not_false_eq_true])
  have dv_cache_0076 :
    x ∉ ((Wff.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_y, fresh_x_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0077 : y ∉ ((syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_n, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0078 :
    y ∉
      ((syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) (.neg
            (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wa,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_n, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0079 : n ∉ ((Wff.classEq (.cv x) (syn_cplc (.cv j) (.cv j)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078
    exact
      (by
        have compact_fv_not_mem_empty : n ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc, Finset.mem_union,
          Finset.mem_singleton, fresh_n_ne_x, (Ne.symm dv_j_n), or_false,
          not_false_eq_true])
  have dv_cache_0080 : x ∉ ((syn_cplc (.cv j) (.cv j))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_j, or_false, not_false_eq_true])
  have dv_cache_0081 :
    x ∉
      ((syn_wo (.classEq (syn_cplc (.cv j) (.cv j)) (syn_c0)) (syn_wral n (syn_cnnc)
            (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))
              (syn_wne (syn_cplc (.cv j) (.cv j))
                (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wo,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wral,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CoreFVSimp.fv_wff_imp,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wne,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_ne_j, fresh_x_ne_n,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0082 :
    j ∉
      ((syn_cimak (syn_cin (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_cssetk))
                  (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
                          (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_cins3k
                                (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k
                                      (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
                                    (syn_cun (syn_cins3k (syn_csik (syn_csik (syn_csik
        (syn_csik (syn_csik (syn_cssetk))))))) (syn_cins2k (syn_cins3k (syn_csik
        (syn_csik (syn_csik (syn_cssetk)))))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
            (syn_cxpk (syn_cun (syn_csn (syn_c0)) (syn_ccompl (syn_cimak (syn_cimak (syn_cin
                        (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins3k (syn_cssetk)) (syn_cins2k
                                        (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cimak
        (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cin (syn_ccompl (syn_cins3k
        (syn_ccnvk (syn_csik (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))) (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) (syn_cun
        (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) (syn_cins3k
        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cins3k
                                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_c1c)))) (syn_cins2k
                          (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))))
                      (syn_cpw1 (syn_c1c))) (syn_cnnc)))) (syn_cvv))) (syn_cvv))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040 dv_cache_0041
      dv_cache_0042 dv_cache_0043 dv_cache_0044 dv_cache_0045 dv_cache_0046 dv_cache_0047
      dv_cache_0048 dv_cache_0049 dv_cache_0050 dv_cache_0051 dv_cache_0052 dv_cache_0053
      dv_cache_0054 dv_cache_0055 dv_cache_0056 dv_cache_0057 dv_cache_0058 dv_cache_0059
      dv_cache_0060 dv_cache_0061 dv_cache_0062 dv_cache_0063 dv_cache_0064 dv_cache_0065
      dv_cache_0066 dv_cache_0067 dv_cache_0068 dv_cache_0069 dv_cache_0070 dv_cache_0071
      dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0075 dv_cache_0076 dv_cache_0077
      dv_cache_0078 dv_cache_0079 dv_cache_0080 dv_cache_0081
    exact
      (by
        have compact_fv_not_mem_empty : j ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  let syntaxFormula0000 : Wff :=
    (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
  let syntaxFormula0001 : Wff :=
    (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) syntaxFormula0000)
  let syntaxFormula0002 : Wff := (syn_wral n (syn_cnnc) syntaxFormula0001)
  let syntaxFormula0003 : Wff :=
    (syn_wo (.classEq (syn_cplc (.cv j) (.cv j)) (syn_c0)) syntaxFormula0002)
  let syntaxClass0004 : Class :=
    (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0005 : Class := (syn_ccompl syntaxClass0004)
  let syntaxClass0006 : Class := (syn_csik syntaxClass0005)
  let syntaxClass0007 : Class := (syn_csik syntaxClass0006)
  let syntaxClass0008 : Class := (syn_csik syntaxClass0007)
  let syntaxClass0009 : Class := (syn_cins3k syntaxClass0008)
  let syntaxClass0010 : Class :=
    (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxClass0011 : Class :=
    (syn_cun syntaxClass0010
      (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxClass0012 : Class :=
    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) syntaxClass0011)
  let syntaxClass0013 : Class :=
    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  let syntaxClass0014 : Class := (syn_cimak syntaxClass0012 syntaxClass0013)
  let syntaxClass0015 : Class := (syn_ccompl syntaxClass0014)
  let syntaxClass0016 : Class := (syn_cin syntaxClass0009 syntaxClass0015)
  let syntaxClass0017 : Class :=
    (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0016)
  let syntaxClass0018 : Class :=
    (syn_cimak syntaxClass0017 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  let syntaxClass0019 : Class := (syn_cin (syn_cins2k (syn_cssetk)) syntaxClass0018)
  let syntaxClass0020 : Class :=
    (syn_cimak syntaxClass0019 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0021 : Class := (syn_cins2k syntaxClass0020)
  let syntaxClass0022 : Class := (syn_csymdif (syn_cins3k (syn_cssetk)) syntaxClass0021)
  let syntaxClass0023 : Class :=
    (syn_cimak syntaxClass0022 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0024 : Class := (syn_ccompl syntaxClass0023)
  let syntaxClass0025 : Class := (syn_csik syntaxClass0004)
  let syntaxClass0026 : Class := (syn_csik syntaxClass0025)
  let syntaxClass0027 : Class := (syn_csik syntaxClass0026)
  let syntaxClass0028 : Class := (syn_ccnvk syntaxClass0027)
  let syntaxClass0029 : Class := (syn_cins3k syntaxClass0028)
  let syntaxClass0030 : Class := (syn_ccompl syntaxClass0029)
  let syntaxClass0031 : Class :=
    (syn_cun (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      syntaxClass0010)
  let syntaxClass0032 : Class :=
    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) syntaxClass0031)
  let syntaxClass0033 : Class := (syn_cimak syntaxClass0032 syntaxClass0013)
  let syntaxClass0034 : Class := (syn_ccompl syntaxClass0033)
  let syntaxClass0035 : Class := (syn_cin syntaxClass0030 syntaxClass0034)
  let syntaxClass0036 : Class :=
    (syn_cin (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0035)
  let syntaxClass0037 : Class :=
    (syn_cimak syntaxClass0036 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  let syntaxClass0038 : Class := (syn_cin (syn_cins2k (syn_cssetk)) syntaxClass0037)
  let syntaxClass0039 : Class :=
    (syn_cimak syntaxClass0038 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0040 : Class := (syn_cins2k syntaxClass0039)
  let syntaxClass0041 : Class := (syn_csymdif (syn_cins3k (syn_cssetk)) syntaxClass0040)
  let syntaxClass0042 : Class :=
    (syn_cimak syntaxClass0041 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0043 : Class := (syn_ccompl syntaxClass0042)
  let syntaxClass0044 : Class := (syn_cins2k syntaxClass0043)
  let syntaxClass0045 : Class := (syn_cins3k syntaxClass0005)
  let syntaxClass0046 : Class :=
    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
      (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
  let syntaxClass0047 : Class :=
    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0046)
  let syntaxClass0048 : Class :=
    (syn_cimak syntaxClass0047 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  let syntaxClass0049 : Class := (syn_cdif syntaxClass0045 syntaxClass0048)
  let syntaxClass0050 : Class :=
    (syn_cimak syntaxClass0049 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0051 : Class := (syn_cimagek syntaxClass0050)
  let syntaxClass0052 : Class := (syn_cins3k syntaxClass0051)
  let syntaxClass0053 : Class := (syn_cin syntaxClass0044 syntaxClass0052)
  let syntaxClass0054 : Class := (syn_cimak syntaxClass0053 (syn_cpw1 (syn_c1c)))
  let syntaxClass0055 : Class := (syn_cins3k syntaxClass0054)
  let syntaxClass0056 : Class :=
    (syn_cin syntaxClass0055
      (syn_cins2k (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))))
  let syntaxClass0057 : Class := (syn_cimak syntaxClass0056 (syn_cpw1 (syn_c1c)))
  let syntaxClass0058 : Class := (syn_cimak syntaxClass0057 (syn_cnnc))
  let syntaxClass0059 : Class := (syn_ccompl syntaxClass0058)
  let syntaxClass0060 : Class := (syn_cun (syn_csn (syn_c0)) syntaxClass0059)
  let syntaxClass0061 : Class := (syn_cxpk syntaxClass0060 (syn_cvv))
  let syntaxClass0062 : Class := (syn_cin syntaxClass0024 syntaxClass0061)
  let syntaxFormula0063 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv j))) syntaxClass0022)
  let syntaxFormula0064 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0063)
  let syntaxFormula0065 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) syntaxFormula0063)
  let syntaxFormula0066 : Wff := (syn_wex y syntaxFormula0065)
  let syntaxFormula0067 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0063)
  let syntaxFormula0068 : Wff := (syn_wex t syntaxFormula0065)
  let syntaxFormula0069 : Wff := (syn_wex y syntaxFormula0068)
  let syntaxFormula0070 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv j)))
      syntaxClass0022)
  let syntaxFormula0071 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv j)))
      (syn_cins3k (syn_cssetk)))
  let syntaxFormula0072 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv y)) (.cv j))) syntaxClass0019)
  let syntaxFormula0073 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0072)
  let syntaxFormula0074 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b))))) syntaxFormula0072)
  let syntaxFormula0075 : Wff := (syn_wex b syntaxFormula0074)
  let syntaxFormula0076 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0072)
  let syntaxFormula0077 : Wff := (syn_wex t syntaxFormula0074)
  let syntaxFormula0078 : Wff := (syn_wex b syntaxFormula0077)
  let syntaxClass0079 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_copk (syn_csn (.cv y)) (.cv j)))
  let syntaxFormula0080 : Wff := (.classMem syntaxClass0079 syntaxClass0019)
  let syntaxFormula0081 : Wff := (.classMem syntaxClass0079 (syn_cins2k (syn_cssetk)))
  let syntaxClass0082 : Class := (syn_copk (.cv t) syntaxClass0079)
  let syntaxFormula0083 : Wff := (.classMem syntaxClass0082 syntaxClass0017)
  let syntaxFormula0084 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      syntaxFormula0083)
  let syntaxFormula0085 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
      syntaxFormula0083)
  let syntaxFormula0086 : Wff := (syn_wex a syntaxFormula0085)
  let syntaxFormula0087 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) syntaxFormula0083)
  let syntaxFormula0088 : Wff := (syn_wex t syntaxFormula0085)
  let syntaxFormula0089 : Wff := (syn_wex a syntaxFormula0088)
  let syntaxClass0090 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))) syntaxClass0079)
  let syntaxFormula0091 : Wff := (.classMem syntaxClass0090 syntaxClass0017)
  let syntaxFormula0092 : Wff :=
    (.classMem syntaxClass0090 (syn_cins2k (syn_cins2k (syn_cssetk))))
  let syntaxFormula0093 : Wff := (.classMem (syn_copk (.cv a) (.cv b)) syntaxClass0004)
  let syntaxFormula0094 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (syn_csn (.cv b))))
      syntaxClass0007)
  let syntaxFormula0095 : Wff := (.classMem syntaxClass0090 syntaxClass0009)
  let syntaxFormula0096 : Wff := (.classMem (.cv t) syntaxClass0013)
  let syntaxClass0097 : Class :=
    (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))))
  let syntaxFormula0098 : Wff := (.classEq (.cv t) syntaxClass0097)
  let syntaxFormula0099 : Wff := (syn_wex x syntaxFormula0098)
  let syntaxClass0100 : Class := (syn_copk (.cv t) syntaxClass0090)
  let syntaxFormula0101 : Wff := (.classMem syntaxClass0100 syntaxClass0012)
  let syntaxFormula0102 : Wff := (syn_wa syntaxFormula0096 syntaxFormula0101)
  let syntaxFormula0103 : Wff := (syn_wa syntaxFormula0098 syntaxFormula0101)
  let syntaxFormula0104 : Wff := (syn_wex x syntaxFormula0103)
  let syntaxFormula0105 : Wff := (syn_wrex t syntaxClass0013 syntaxFormula0101)
  let syntaxFormula0106 : Wff := (syn_wex t syntaxFormula0103)
  let syntaxFormula0107 : Wff := (syn_wex x syntaxFormula0106)
  let syntaxClass0108 : Class := (syn_copk syntaxClass0097 syntaxClass0090)
  let syntaxFormula0109 : Wff := (.classMem syntaxClass0108 syntaxClass0012)
  let syntaxFormula0110 : Wff :=
    (.classMem syntaxClass0108 (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))))
  let syntaxFormula0111 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn (.cv a))))
      (syn_csik (syn_csik (syn_cssetk))))
  let syntaxFormula0112 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
        (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
  let syntaxClass0113 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv a)))))
  let syntaxFormula0114 : Wff :=
    (.classMem syntaxClass0113 (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
  let syntaxFormula0115 : Wff := (.classMem syntaxClass0108 syntaxClass0010)
  let syntaxClass0116 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv b)))))
  let syntaxFormula0117 : Wff :=
    (.classMem syntaxClass0116 (syn_csik (syn_csik (syn_csik (syn_cssetk)))))
  let syntaxFormula0118 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn (.cv b))))
      (syn_csik (syn_csik (syn_cssetk))))
  let syntaxFormula0119 : Wff :=
    (.classMem syntaxClass0108
      (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxFormula0120 : Wff := (.classMem syntaxClass0108 syntaxClass0011)
  let syntaxFormula0121 : Wff := (syn_wb syntaxFormula0110 syntaxFormula0120)
  let syntaxFormula0122 : Wff := (.classMem syntaxClass0090 syntaxClass0014)
  let syntaxFormula0123 : Wff := (.classMem syntaxClass0090 syntaxClass0015)
  let syntaxFormula0124 : Wff := (.classMem syntaxClass0090 syntaxClass0016)
  let syntaxFormula0125 : Wff :=
    (syn_wa (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      (.classEq (.cv y) (syn_cun (.cv a) (.cv b))))
  let syntaxFormula0126 : Wff := (.classMem syntaxClass0079 syntaxClass0018)
  let syntaxFormula0127 : Wff := (syn_wrex a (.cv j) syntaxFormula0125)
  let syntaxFormula0128 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv y)) (.cv j)) syntaxClass0020)
  let syntaxFormula0129 : Wff := (syn_wrex b (.cv j) syntaxFormula0127)
  let syntaxFormula0130 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv j)))
      syntaxClass0021)
  let syntaxFormula0131 : Wff := (syn_wrex b (.cv j) syntaxFormula0125)
  let syntaxFormula0132 : Wff := (syn_wrex a (.cv j) syntaxFormula0131)
  let syntaxFormula0133 : Wff := (syn_wb syntaxFormula0071 syntaxFormula0130)
  let syntaxFormula0134 : Wff := (.classMem (syn_copk (.cv x) (.cv j)) syntaxClass0023)
  let syntaxFormula0135 : Wff := (.classMem (syn_copk (.cv x) (.cv j)) syntaxClass0024)
  let syntaxClass0136 : Class := (.cab y syntaxFormula0132)
  let syntaxFormula0137 : Wff := (.classEq (.cv x) syntaxClass0136)
  let syntaxFormula0138 : Wff := (.classMem (syn_copk (.cv x) (.cv j)) syntaxClass0061)
  let syntaxFormula0139 : Wff := (.classMem (.cv x) syntaxClass0060)
  let syntaxFormula0140 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv n) (.cv x))) syntaxClass0056)
  let syntaxFormula0141 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) syntaxFormula0140)
  let syntaxFormula0142 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv y)))) syntaxFormula0140)
  let syntaxFormula0143 : Wff := (syn_wex y syntaxFormula0142)
  let syntaxFormula0144 : Wff := (syn_wrex t (syn_cpw1 (syn_c1c)) syntaxFormula0140)
  let syntaxFormula0145 : Wff := (syn_wex t syntaxFormula0142)
  let syntaxFormula0146 : Wff := (syn_wex y syntaxFormula0145)
  let syntaxFormula0147 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (.cv x)))
      syntaxClass0056)
  let syntaxFormula0148 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv n))) syntaxClass0053)
  let syntaxFormula0149 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) syntaxFormula0148)
  let syntaxFormula0150 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) syntaxFormula0148)
  let syntaxFormula0151 : Wff := (syn_wex x syntaxFormula0150)
  let syntaxFormula0152 : Wff := (syn_wrex t (syn_cpw1 (syn_c1c)) syntaxFormula0148)
  let syntaxFormula0153 : Wff := (syn_wex t syntaxFormula0150)
  let syntaxFormula0154 : Wff := (syn_wex x syntaxFormula0153)
  let syntaxFormula0155 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv n)))
      syntaxClass0053)
  let syntaxFormula0156 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv n))) syntaxClass0041)
  let syntaxFormula0157 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0156)
  let syntaxFormula0158 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) syntaxFormula0156)
  let syntaxFormula0159 : Wff := (syn_wex y syntaxFormula0158)
  let syntaxFormula0160 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0156)
  let syntaxFormula0161 : Wff := (syn_wex t syntaxFormula0158)
  let syntaxFormula0162 : Wff := (syn_wex y syntaxFormula0161)
  let syntaxFormula0163 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv n)))
      syntaxClass0041)
  let syntaxFormula0164 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv n)))
      (syn_cins3k (syn_cssetk)))
  let syntaxFormula0165 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (.cv y)) (.cv n))) syntaxClass0038)
  let syntaxFormula0166 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c)))) syntaxFormula0165)
  let syntaxFormula0167 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))) syntaxFormula0165)
  let syntaxFormula0168 : Wff := (syn_wex a syntaxFormula0167)
  let syntaxFormula0169 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c))) syntaxFormula0165)
  let syntaxFormula0170 : Wff := (syn_wex t syntaxFormula0167)
  let syntaxFormula0171 : Wff := (syn_wex a syntaxFormula0170)
  let syntaxClass0172 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (syn_csn (.cv y)) (.cv n)))
  let syntaxFormula0173 : Wff := (.classMem syntaxClass0172 syntaxClass0038)
  let syntaxFormula0174 : Wff := (.classMem syntaxClass0172 (syn_cins2k (syn_cssetk)))
  let syntaxClass0175 : Class := (syn_copk (.cv t) syntaxClass0172)
  let syntaxFormula0176 : Wff := (.classMem syntaxClass0175 syntaxClass0036)
  let syntaxFormula0177 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      syntaxFormula0176)
  let syntaxFormula0178 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
      syntaxFormula0176)
  let syntaxFormula0179 : Wff := (syn_wex b syntaxFormula0178)
  let syntaxFormula0180 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) syntaxFormula0176)
  let syntaxFormula0181 : Wff := (syn_wex t syntaxFormula0178)
  let syntaxFormula0182 : Wff := (syn_wex b syntaxFormula0181)
  let syntaxClass0183 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0172)
  let syntaxFormula0184 : Wff := (.classMem syntaxClass0183 syntaxClass0036)
  let syntaxFormula0185 : Wff :=
    (.classMem syntaxClass0183 (syn_cins2k (syn_cins2k (syn_cssetk))))
  let syntaxFormula0186 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv a)) (syn_csn (.cv b))) syntaxClass0025)
  let syntaxFormula0187 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
        (syn_csn (syn_csn (syn_csn (.cv b))))) syntaxClass0027)
  let syntaxFormula0188 : Wff := (.classMem syntaxClass0183 syntaxClass0029)
  let syntaxFormula0189 : Wff := (.classMem syntaxClass0183 syntaxClass0030)
  let syntaxClass0190 : Class := (syn_copk (.cv t) syntaxClass0183)
  let syntaxFormula0191 : Wff := (.classMem syntaxClass0190 syntaxClass0032)
  let syntaxFormula0192 : Wff := (syn_wa syntaxFormula0096 syntaxFormula0191)
  let syntaxFormula0193 : Wff := (syn_wa syntaxFormula0098 syntaxFormula0191)
  let syntaxFormula0194 : Wff := (syn_wex x syntaxFormula0193)
  let syntaxFormula0195 : Wff := (syn_wrex t syntaxClass0013 syntaxFormula0191)
  let syntaxFormula0196 : Wff := (syn_wex t syntaxFormula0193)
  let syntaxFormula0197 : Wff := (syn_wex x syntaxFormula0196)
  let syntaxClass0198 : Class := (syn_copk syntaxClass0097 syntaxClass0183)
  let syntaxFormula0199 : Wff := (.classMem syntaxClass0198 syntaxClass0032)
  let syntaxFormula0200 : Wff :=
    (.classMem syntaxClass0198 (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))))
  let syntaxFormula0201 : Wff :=
    (.classMem syntaxClass0198
      (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
  let syntaxFormula0202 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
        (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
  let syntaxFormula0203 : Wff := (.classMem syntaxClass0198 syntaxClass0010)
  let syntaxFormula0204 : Wff := (.classMem syntaxClass0198 syntaxClass0031)
  let syntaxFormula0205 : Wff := (syn_wb syntaxFormula0200 syntaxFormula0204)
  let syntaxFormula0206 : Wff := (.classMem syntaxClass0183 syntaxClass0033)
  let syntaxFormula0207 : Wff := (.classMem syntaxClass0183 syntaxClass0034)
  let syntaxFormula0208 : Wff := (.classMem syntaxClass0183 syntaxClass0035)
  let syntaxFormula0209 : Wff := (.classMem syntaxClass0172 syntaxClass0037)
  let syntaxFormula0210 : Wff := (syn_wrex b (.cv n) syntaxFormula0125)
  let syntaxFormula0211 : Wff :=
    (.classMem (syn_copk (syn_csn (.cv y)) (.cv n)) syntaxClass0039)
  let syntaxFormula0212 : Wff := (syn_wrex a (.cv n) syntaxFormula0210)
  let syntaxFormula0213 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv n)))
      syntaxClass0040)
  let syntaxFormula0214 : Wff := (syn_wb syntaxFormula0164 syntaxFormula0213)
  let syntaxFormula0215 : Wff := (.classMem (syn_copk (.cv x) (.cv n)) syntaxClass0042)
  let syntaxFormula0216 : Wff := (.classMem (syn_copk (.cv x) (.cv n)) syntaxClass0043)
  let syntaxClass0217 : Class := (.cab y syntaxFormula0212)
  let syntaxFormula0218 : Wff := (.classEq (.cv x) syntaxClass0217)
  let syntaxFormula0219 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv n)))
      syntaxClass0044)
  let syntaxClass0220 : Class := (syn_cimak syntaxClass0050 (.cv x))
  let syntaxFormula0221 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv n)))
      syntaxClass0052)
  let syntaxFormula0222 : Wff :=
    (syn_wa (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))
      (.classEq (.cv y) (syn_cplc (.cv x) (syn_c1c))))
  let syntaxFormula0223 : Wff := (.classMem (syn_copk (.cv y) (.cv n)) syntaxClass0054)
  let syntaxFormula0224 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (.cv x)))
      syntaxClass0055)
  let syntaxFormula0225 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (.cv x)))
      (syn_cins2k (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))))
  let syntaxFormula0226 : Wff := (.classMem (syn_copk (.cv n) (.cv x)) syntaxClass0057)
  let syntaxFormula0227 : Wff :=
    (.imp (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))
  let syntaxFormula0228 : Wff := (.neg syntaxFormula0227)
  let syntaxFormula0229 : Wff := (.classMem (.cv x) syntaxClass0058)
  let syntaxFormula0230 : Wff := (syn_wrex n (syn_cnnc) syntaxFormula0228)
  let syntaxFormula0231 : Wff :=
    (.imp (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))
      (syn_wne (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
  let syntaxFormula0232 : Wff := (syn_wral n (syn_cnnc) syntaxFormula0231)
  let syntaxFormula0233 : Wff := (.neg syntaxFormula0230)
  let syntaxFormula0234 : Wff := (.classMem (.cv x) syntaxClass0059)
  let syntaxFormula0235 : Wff := (syn_wo (.classEq (.cv x) (syn_c0)) syntaxFormula0232)
  let syntaxFormula0236 : Wff := (.classMem (syn_copk (.cv x) (.cv j)) syntaxClass0062)
  let syntaxFormula0237 : Wff :=
    (syn_wa (.classEq (.cv x) (syn_cplc (.cv j) (.cv j))) syntaxFormula0235)
  let syntaxClass0238 : Class := (syn_cimak syntaxClass0062 (syn_cvv))
  let syntaxFormula0239 : Wff := (.classMem (.cv j) syntaxClass0238)
  let syntaxFormula0240 : Wff :=
    (.imp (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0)) syntaxFormula0002)
  have p0000 := (Nominal.biimpRefl syntaxFormula0003)
  have p0001 := @g_vex j
  have p0002 := @g_elimakv x syntaxClass0062 (.cv j) dv_cache_0001 dv_cache_0002 p0001
  have p0003 := @g_elin (syn_copk (.cv x) (.cv j)) syntaxClass0024 syntaxClass0061
  have p0004 := @g_opkex (.cv x) (.cv j)
  have p0005 :=
    @g_elimak t syntaxClass0022 (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv x) (.cv j))
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0004
  have p0006 := @g_elpw121c y (.cv t) dv_cache_0006
  have p0007 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))))
      syntaxFormula0063 p0006
  have p0008 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) syntaxFormula0063
      y dv_cache_0007
  have p0009 :=
    @g_bitr4i syntaxFormula0064
      (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))))
        syntaxFormula0063)
      syntaxFormula0066 p0007 p0008
  have p0010 := @g_exbii syntaxFormula0064 syntaxFormula0066 t p0009
  have p0011 := (Nominal.biimpRefl syntaxFormula0067)
  have p0012 := @g_excom syntaxFormula0065 y t
  have p0013 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0064) (syn_wex t syntaxFormula0066)
      syntaxFormula0067 syntaxFormula0069 p0010 p0011 p0012
  have p0014 := @g_snex (syn_csn (syn_csn (.cv y)))
  have p0015 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv j))
  have p0016 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
      (syn_copk (.cv t) (syn_copk (.cv x) (.cv j)))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv j)))
      syntaxClass0022 p0015
  have p0017 :=
    @g_ceqsexv syntaxFormula0063 syntaxFormula0070 t (syn_csn (syn_csn (syn_csn (.cv y))))
      dv_cache_0008 dv_cache_0009 p0014 p0016
  have p0018 :=
    @g_elsymdif
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv j)))
      (syn_cins3k (syn_cssetk)) syntaxClass0021
  have p0019 := @g_snex (.cv y)
  have p0020 := @g_vex x
  have p0021 :=
    @g_otkelins3k (syn_csn (.cv y)) (.cv x) (.cv j) (syn_cssetk) p0019 p0020 p0001
  have p0022 := @g_vex y
  have p0023 := @g_elssetk (.cv y) (.cv x) p0022 p0020
  have p0024_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)) (.objMem y x)) :=
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
      p0023
  have p0024 :=
    @g_bitri syntaxFormula0071
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)) (.objMem y x) p0021
      p0024_e01_recanon
  have p0025 :=
    @g_otkelins2k (syn_csn (.cv y)) (.cv x) (.cv j) syntaxClass0020 p0019 p0020 p0001
  have p0026 := @g_opkex (syn_csn (.cv y)) (.cv j)
  have p0027 :=
    @g_elimak t syntaxClass0019 (syn_cpw1 (syn_cpw1 (syn_c1c)))
      (syn_copk (syn_csn (.cv y)) (.cv j)) dv_cache_0010 dv_cache_0004 dv_cache_0011 p0026
  have p0028 := @g_elpw121c b (.cv t) dv_cache_0012
  have p0029 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex b (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b))))))
      syntaxFormula0072 p0028
  have p0030 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b))))) syntaxFormula0072
      b dv_cache_0013
  have p0031 :=
    @g_bitr4i syntaxFormula0073
      (syn_wa (syn_wex b (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b))))))
        syntaxFormula0072)
      syntaxFormula0075 p0029 p0030
  have p0032 := @g_exbii syntaxFormula0073 syntaxFormula0075 t p0031
  have p0033 := (Nominal.biimpRefl syntaxFormula0076)
  have p0034 := @g_excom syntaxFormula0074 b t
  have p0035 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0073) (syn_wex t syntaxFormula0075)
      syntaxFormula0076 syntaxFormula0078 p0032 p0033 p0034
  have p0036 := @g_snex (syn_csn (syn_csn (.cv b)))
  have p0037 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv b))))
      (syn_copk (syn_csn (.cv y)) (.cv j))
  have p0038 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv b)))))
      (syn_copk (.cv t) (syn_copk (syn_csn (.cv y)) (.cv j))) syntaxClass0079
      syntaxClass0019 p0037
  have p0039 :=
    @g_ceqsexv syntaxFormula0072 syntaxFormula0080 t (syn_csn (syn_csn (syn_csn (.cv b))))
      dv_cache_0014 dv_cache_0015 p0036 p0038
  have p0040 := @g_elin syntaxClass0079 (syn_cins2k (syn_cssetk)) syntaxClass0018
  have p0041 := @g_snex (.cv b)
  have p0042 :=
    @g_otkelins2k (syn_csn (.cv b)) (syn_csn (.cv y)) (.cv j) (syn_cssetk) p0041 p0019
      p0001
  have p0043 := @g_vex b
  have p0044 := @g_elssetk (.cv b) (.cv j) p0043 p0001
  have p0045_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv b)) (.cv j)) (syn_cssetk)) (.objMem b j)) :=
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
      p0044
  have p0045 :=
    @g_bitri syntaxFormula0081
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv j)) (syn_cssetk)) (.objMem b j) p0042
      p0045_e01_recanon
  have p0046 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_copk (syn_csn (.cv y)) (.cv j))
  have p0047 :=
    @g_elimak t syntaxClass0017 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      syntaxClass0079 dv_cache_0016 dv_cache_0017 dv_cache_0018 p0046
  have p0048 := @g_elpw141c a (.cv t) dv_cache_0019
  have p0049 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))
      syntaxFormula0083 p0048
  have p0050 :=
    @g_n_19_41v
      (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
      syntaxFormula0083 a dv_cache_0020
  have p0051 :=
    @g_bitr4i syntaxFormula0084
      (syn_wa (syn_wex a
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))))
        syntaxFormula0083)
      syntaxFormula0086 p0049 p0050
  have p0052 := @g_exbii syntaxFormula0084 syntaxFormula0086 t p0051
  have p0053 := (Nominal.biimpRefl syntaxFormula0087)
  have p0054 := @g_excom syntaxFormula0085 a t
  have p0055 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0084) (syn_wex t syntaxFormula0086)
      syntaxFormula0087 syntaxFormula0089 p0052 p0053 p0054
  have p0056 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))
  have p0057 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a))))))
      syntaxClass0079
  have p0058 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
      syntaxClass0082 syntaxClass0090 syntaxClass0017 p0057
  have p0059 :=
    @g_ceqsexv syntaxFormula0083 syntaxFormula0091 t
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))) dv_cache_0021
      dv_cache_0022 p0056 p0058
  have p0060 :=
    @g_elin syntaxClass0090 (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0016
  have p0061 := @g_snex (syn_csn (syn_csn (.cv a)))
  have p0062 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv a))))
      (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_copk (syn_csn (.cv y)) (.cv j))
      (syn_cins2k (syn_cssetk)) p0061 p0036 p0026
  have p0063 := @g_snex (.cv a)
  have p0064 :=
    @g_otkelins2k (syn_csn (.cv a)) (syn_csn (.cv y)) (.cv j) (syn_cssetk) p0063 p0019
      p0001
  have p0065 := @g_vex a
  have p0066 := @g_elssetk (.cv a) (.cv j) p0065 p0001
  have p0067_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv a)) (.cv j)) (syn_cssetk)) (.objMem a j)) :=
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
      p0066
  have p0067 :=
    @g_n_3bitri syntaxFormula0092
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
          (syn_copk (syn_csn (.cv y)) (.cv j))) (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv a)) (.cv j)) (syn_cssetk)) (.objMem a j) p0062
      p0064 p0067_e02_recanon
  have p0068 := @g_elin syntaxClass0090 syntaxClass0009 syntaxClass0015
  have p0069 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (.cv a))))
      (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_copk (syn_csn (.cv y)) (.cv j))
      syntaxClass0008 p0061 p0036 p0026
  have p0070 := @g_snex (syn_csn (.cv a))
  have p0071 := @g_snex (syn_csn (.cv b))
  have p0072 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv a))) (syn_csn (syn_csn (.cv b))) syntaxClass0007
      p0070 p0071
  have p0073 :=
    @g_opksnelsik (syn_csn (.cv a)) (syn_csn (.cv b)) syntaxClass0006 p0063 p0041
  have p0074 := @g_opksnelsik (.cv a) (.cv b) syntaxClass0005 p0065 p0043
  have p0075 := @g_ndisjrelk (.cv a) (.cv b) p0065 p0043
  have p0076 :=
    @g_notbii syntaxFormula0093 (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0)) p0075
  have p0077 := @g_opkex (.cv a) (.cv b)
  have p0078 := @g_elcompl (syn_copk (.cv a) (.cv b)) syntaxClass0004 p0077
  have p0079 := (Nominal.biimpRefl (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0)))
  have p0080 :=
    @g_con2bii (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0))
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0079
  have p0081 :=
    @g_n_3bitr4i (.neg syntaxFormula0093)
      (.neg (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0)))
      (.classMem (syn_copk (.cv a) (.cv b)) syntaxClass0005)
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0076 p0078 p0080
  have p0082 :=
    @g_n_3bitri syntaxFormula0094
      (.classMem (syn_copk (syn_csn (.cv a)) (syn_csn (.cv b))) syntaxClass0006)
      (.classMem (syn_copk (.cv a) (.cv b)) syntaxClass0005)
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0073 p0074 p0081
  have p0083 :=
    @g_n_3bitri syntaxFormula0095
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv a))))
          (syn_csn (syn_csn (syn_csn (.cv b))))) syntaxClass0008)
      syntaxFormula0094 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0069 p0072 p0082
  have p0084 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))) syntaxClass0079
  have p0085 :=
    @g_elimak t syntaxClass0012 syntaxClass0013 syntaxClass0090 dv_cache_0023
      dv_cache_0024 dv_cache_0025 p0084
  have p0086 := @g_elpw171c x (.cv t) dv_cache_0026
  have p0087 := @g_anbi1i syntaxFormula0096 syntaxFormula0099 syntaxFormula0101 p0086
  have p0088 := @g_n_19_41v syntaxFormula0098 syntaxFormula0101 x dv_cache_0027
  have p0089 :=
    @g_bitr4i syntaxFormula0102 (syn_wa syntaxFormula0099 syntaxFormula0101)
      syntaxFormula0104 p0087 p0088
  have p0090 := @g_exbii syntaxFormula0102 syntaxFormula0104 t p0089
  have p0091 := (Nominal.biimpRefl syntaxFormula0105)
  have p0092 := @g_excom syntaxFormula0103 x t
  have p0093 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0102) (syn_wex t syntaxFormula0104)
      syntaxFormula0105 syntaxFormula0107 p0090 p0091 p0092
  have p0094 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
  have p0095 := @g_opkeq1 (.cv t) syntaxClass0097 syntaxClass0090
  have p0096 :=
    @g_eleq1d syntaxFormula0098 syntaxClass0100 syntaxClass0108 syntaxClass0012 p0095
  have p0097 :=
    @g_ceqsexv syntaxFormula0101 syntaxFormula0109 t syntaxClass0097 dv_cache_0028
      dv_cache_0029 p0094 p0096
  have p0098 :=
    @g_elsymdif syntaxClass0108
      (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) syntaxClass0011
  have p0099 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
  have p0100 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))) syntaxClass0079
      (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))) p0099 p0056 p0046
  have p0101 := @g_snex (syn_csn (syn_csn (syn_csn (.cv x))))
  have p0102 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_copk (syn_csn (.cv y)) (.cv j))
      (syn_cins3k (syn_csik (syn_cssetk))) p0101 p0036 p0026
  have p0103 := @g_snex (syn_csn (.cv x))
  have p0104 :=
    @g_otkelins3k (syn_csn (syn_csn (.cv x))) (syn_csn (.cv y)) (.cv j)
      (syn_csik (syn_cssetk)) p0103 p0019 p0001
  have p0105 := @g_snex (.cv x)
  have p0106 := @g_opksnelsik (syn_csn (.cv x)) (.cv y) (syn_cssetk) p0105 p0022
  have p0107 := @g_elssetk (.cv x) (.cv y) p0020 p0022
  have p0108_e02_recanon :
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
      p0107
  have p0108 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk (syn_csn (.cv y)) (.cv j))) (syn_cins3k (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv y)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y) p0104
      p0106 p0108_e02_recanon
  have p0109 :=
    @g_n_3bitri syntaxFormula0110
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          syntaxClass0079) (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk (syn_csn (.cv y)) (.cv j))) (syn_cins3k (syn_csik (syn_cssetk))))
      (.objMem x y) p0100 p0102 p0108
  have p0110 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))) syntaxClass0079
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0099 p0056
      p0046
  have p0111 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
  have p0112 := @g_snex (syn_csn (syn_csn (syn_csn (.cv a))))
  have p0113 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0111 p0112
  have p0114 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_csik (syn_csik (syn_csik (syn_cssetk))))
      p0101 p0061
  have p0115 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0116 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn (.cv a)))
      (syn_csik (syn_csik (syn_cssetk))) p0115 p0070
  have p0117 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv x))) (syn_csn (.cv a)) (syn_csik (syn_cssetk))
      p0103 p0063
  have p0118 := @g_opksnelsik (syn_csn (.cv x)) (.cv a) (syn_cssetk) p0105 p0065
  have p0119 := @g_elssetk (.cv x) (.cv a) p0020 p0065
  have p0120_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk)) (.objMem x a)) :=
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
      p0119
  have p0120 :=
    @g_n_3bitri syntaxFormula0111
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv a)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk)) (.objMem x a) p0117
      p0118 p0120_e02_recanon
  have p0121 :=
    @g_n_3bitri syntaxFormula0112 syntaxFormula0114 syntaxFormula0111 (.objMem x a) p0114
      p0116 p0120
  have p0122 :=
    @g_n_3bitri syntaxFormula0115
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))))
        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
      syntaxFormula0112 (.objMem x a) p0110 p0113 p0121
  have p0123 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv a)))))) syntaxClass0079
      (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0099 p0056 p0046
  have p0124 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_copk (syn_csn (.cv y)) (.cv j))
      (syn_csik (syn_csik (syn_csik (syn_cssetk)))) p0101 p0036 p0026
  have p0125 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn (.cv b)))
      (syn_csik (syn_csik (syn_cssetk))) p0115 p0071
  have p0126 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv x))) (syn_csn (.cv b)) (syn_csik (syn_cssetk))
      p0103 p0041
  have p0127 := @g_opksnelsik (syn_csn (.cv x)) (.cv b) (syn_cssetk) p0105 p0043
  have p0128 := @g_elssetk (.cv x) (.cv b) p0020 p0043
  have p0129_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv b)) (syn_cssetk)) (.objMem x b)) :=
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
      p0128
  have p0129 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv b)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv b)) (syn_cssetk)) (.objMem x b) p0127
      p0129_e01_recanon
  have p0130 :=
    @g_n_3bitri syntaxFormula0117 syntaxFormula0118
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv b)))
        (syn_csik (syn_cssetk)))
      (.objMem x b) p0125 p0126 p0129
  have p0131 :=
    @g_n_3bitri syntaxFormula0119
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          syntaxClass0079) (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      syntaxFormula0117 (.objMem x b) p0123 p0124 p0130
  have p0132 :=
    @g_orbi12i syntaxFormula0115 (.objMem x a) syntaxFormula0119 (.objMem x b) p0122 p0131
  have p0133 :=
    @g_elun syntaxClass0108 syntaxClass0010
      (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
  have p0134 := @g_elun (.cv x) (.cv a) (.cv b)
  have p0135_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) (syn_cun (.cv a) (.cv b)))
        (syn_wo (.objMem x a) (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl, syn_wo]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0134
  have p0135 :=
    @g_n_3bitr4i (syn_wo syntaxFormula0115 syntaxFormula0119)
      (syn_wo (.objMem x a) (.objMem x b)) syntaxFormula0120
      (.classMem (.cv x) (syn_cun (.cv a) (.cv b))) p0132 p0133 p0135_e02_recanon
  have p0136 :=
    @g_bibi12i syntaxFormula0110 (.objMem x y) syntaxFormula0120
      (.classMem (.cv x) (syn_cun (.cv a) (.cv b))) p0109 p0135
  have p0137 :=
    @g_notbii syntaxFormula0121
      (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b)))) p0136
  have p0138 :=
    @g_n_3bitri syntaxFormula0106 syntaxFormula0109 (.neg syntaxFormula0121)
      (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b))))) p0097
      p0098 p0137
  have p0139 :=
    @g_exbii syntaxFormula0106
      (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b))))) x p0138
  have p0140 :=
    @g_n_3bitri syntaxFormula0122 syntaxFormula0105 syntaxFormula0107
      (syn_wex x (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b))))))
      p0085 p0093 p0139
  have p0141 :=
    @g_notbii syntaxFormula0122
      (syn_wex x (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b))))))
      p0140
  have p0142 := @g_elcompl syntaxClass0090 syntaxClass0014 p0084
  have p0143 := @g_dfcleq x (.cv y) (syn_cun (.cv a) (.cv b)) dv_cache_0030 dv_cache_0031
  have p0144 :=
    @g_alex (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b)))) x
  have p0145_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classEq (.cv y) (syn_cun (.cv a) (.cv b)))
        (.all x (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
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
      p0143
  have p0145 :=
    @g_bitri (.classEq (.cv y) (syn_cun (.cv a) (.cv b)))
      (.all x (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b)))))
      (.neg (syn_wex x
          (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b)))))))
      p0145_e00_recanon p0144
  have p0146 :=
    @g_n_3bitr4i (.neg syntaxFormula0122)
      (.neg (syn_wex x
          (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b)))))))
      syntaxFormula0123 (.classEq (.cv y) (syn_cun (.cv a) (.cv b))) p0141 p0142 p0145
  have p0147 :=
    @g_anbi12i syntaxFormula0095 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      syntaxFormula0123 (.classEq (.cv y) (syn_cun (.cv a) (.cv b))) p0083 p0146
  have p0148 :=
    @g_bitri syntaxFormula0124 (syn_wa syntaxFormula0095 syntaxFormula0123)
      syntaxFormula0125 p0068 p0147
  have p0149 :=
    @g_anbi12i syntaxFormula0092 (.objMem a j) syntaxFormula0124 syntaxFormula0125 p0067
      p0148
  have p0150 :=
    @g_n_3bitri syntaxFormula0088 syntaxFormula0091
      (syn_wa syntaxFormula0092 syntaxFormula0124)
      (syn_wa (.objMem a j) syntaxFormula0125) p0059 p0060 p0149
  have p0151 :=
    @g_exbii syntaxFormula0088 (syn_wa (.objMem a j) syntaxFormula0125) a p0150
  have p0152 :=
    @g_n_3bitri syntaxFormula0126 syntaxFormula0087 syntaxFormula0089
      (syn_wex a (syn_wa (.objMem a j) syntaxFormula0125)) p0047 p0055 p0151
  have p0153 := (Nominal.biimpRefl syntaxFormula0127)
  have p0154_e01_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0127 (syn_wex a (syn_wa (.objMem a j) syntaxFormula0125))) :=
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
      p0153
  have p0154 :=
    @g_bitr4i syntaxFormula0126 (syn_wex a (syn_wa (.objMem a j) syntaxFormula0125))
      syntaxFormula0127 p0152 p0154_e01_recanon
  have p0155 :=
    @g_anbi12i syntaxFormula0081 (.objMem b j) syntaxFormula0126 syntaxFormula0127 p0045
      p0154
  have p0156 :=
    @g_n_3bitri syntaxFormula0077 syntaxFormula0080
      (syn_wa syntaxFormula0081 syntaxFormula0126)
      (syn_wa (.objMem b j) syntaxFormula0127) p0039 p0040 p0155
  have p0157 :=
    @g_exbii syntaxFormula0077 (syn_wa (.objMem b j) syntaxFormula0127) b p0156
  have p0158 :=
    @g_n_3bitri syntaxFormula0128 syntaxFormula0076 syntaxFormula0078
      (syn_wex b (syn_wa (.objMem b j) syntaxFormula0127)) p0027 p0035 p0157
  have p0159 := (Nominal.biimpRefl syntaxFormula0129)
  have p0160_e01_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0129 (syn_wex b (syn_wa (.objMem b j) syntaxFormula0127))) :=
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
      p0159
  have p0160 :=
    @g_bitr4i syntaxFormula0128 (syn_wex b (syn_wa (.objMem b j) syntaxFormula0127))
      syntaxFormula0129 p0158 p0160_e01_recanon
  have p0161 :=
    @g_rexcom syntaxFormula0125 b a (.cv j) (.cv j) dv_cache_0032 dv_cache_0033
      dv_cache_0034
  have p0162 :=
    @g_n_3bitri syntaxFormula0130 syntaxFormula0128 syntaxFormula0129 syntaxFormula0132
      p0025 p0160 p0161
  have p0163 :=
    @g_bibi12i syntaxFormula0071 (.objMem y x) syntaxFormula0130 syntaxFormula0132 p0024
      p0162
  have p0164 := @g_notbii syntaxFormula0133 (syn_wb (.objMem y x) syntaxFormula0132) p0163
  have p0165 :=
    @g_n_3bitri syntaxFormula0068 syntaxFormula0070 (.neg syntaxFormula0133)
      (.neg (syn_wb (.objMem y x) syntaxFormula0132)) p0017 p0018 p0164
  have p0166 :=
    @g_exbii syntaxFormula0068 (.neg (syn_wb (.objMem y x) syntaxFormula0132)) y p0165
  have p0167 :=
    @g_n_3bitri syntaxFormula0134 syntaxFormula0067 syntaxFormula0069
      (syn_wex y (.neg (syn_wb (.objMem y x) syntaxFormula0132))) p0005 p0013 p0166
  have p0168 :=
    @g_notbii syntaxFormula0134
      (syn_wex y (.neg (syn_wb (.objMem y x) syntaxFormula0132))) p0167
  have p0169 := @g_elcompl (syn_copk (.cv x) (.cv j)) syntaxClass0023 p0004
  have p0170 := @g_alex (syn_wb (.objMem y x) syntaxFormula0132) y
  have p0171 :=
    @g_n_3bitr4i (.neg syntaxFormula0134)
      (.neg (syn_wex y (.neg (syn_wb (.objMem y x) syntaxFormula0132)))) syntaxFormula0135
      (.all y (syn_wb (.objMem y x) syntaxFormula0132)) p0168 p0169 p0170
  have p0172 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addc y a b (.cv j)
      (.cv j) dv_cache_0035 dv_cache_0032 dv_cache_0033 dv_cache_0035 dv_cache_0032
      dv_cache_0033 dv_cache_0036 dv_cache_0037 dv_cache_0038
  have p0173 := @g_eqeq2i (syn_cplc (.cv j) (.cv j)) syntaxClass0136 (.cv x) p0172
  have p0174 := @g_eqabb syntaxFormula0132 y (.cv x) dv_cache_0039
  have p0175_e01_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0137 (.all y (syn_wb (.objMem y x) syntaxFormula0132))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb]
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
      p0174
  have p0175 :=
    @g_bitri (.classEq (.cv x) (syn_cplc (.cv j) (.cv j))) syntaxFormula0137
      (.all y (syn_wb (.objMem y x) syntaxFormula0132)) p0173 p0175_e01_recanon
  have p0176 :=
    @g_bitr4i syntaxFormula0135 (.all y (syn_wb (.objMem y x) syntaxFormula0132))
      (.classEq (.cv x) (syn_cplc (.cv j) (.cv j))) p0171 p0175
  have p0177 := @g_opkelxpk (.cv x) (.cv j) syntaxClass0060 (syn_cvv) p0020 p0001
  have p0178 :=
    @g_mpbiran2 syntaxFormula0138 syntaxFormula0139 (.classMem (.cv j) (syn_cvv)) p0001
      p0177
  have p0179 := @g_elun (.cv x) (syn_csn (syn_c0)) syntaxClass0059
  have p0180 := @g_elsnc (.cv x) (syn_c0) p0020
  have p0181 :=
    @g_elimak n syntaxClass0057 (syn_cnnc) (.cv x) dv_cache_0040 dv_cache_0041
      dv_cache_0042 p0020
  have p0182 := @g_opkex (.cv n) (.cv x)
  have p0183 :=
    @g_elimak t syntaxClass0056 (syn_cpw1 (syn_c1c)) (syn_copk (.cv n) (.cv x))
      dv_cache_0043 dv_cache_0044 dv_cache_0045 p0182
  have p0184 := @g_elpw11c y (.cv t) dv_cache_0006
  have p0185 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))) syntaxFormula0140 p0184
  have p0186 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv y)))) syntaxFormula0140 y
      dv_cache_0046
  have p0187 :=
    @g_bitr4i syntaxFormula0141
      (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))) syntaxFormula0140)
      syntaxFormula0143 p0185 p0186
  have p0188 := @g_exbii syntaxFormula0141 syntaxFormula0143 t p0187
  have p0189 := (Nominal.biimpRefl syntaxFormula0144)
  have p0190 := @g_excom syntaxFormula0142 y t
  have p0191 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0141) (syn_wex t syntaxFormula0143)
      syntaxFormula0144 syntaxFormula0146 p0188 p0189 p0190
  have p0192 := @g_snex (syn_csn (.cv y))
  have p0193 := @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (.cv x))
  have p0194 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv y))))
      (syn_copk (.cv t) (syn_copk (.cv n) (.cv x)))
      (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (.cv x))) syntaxClass0056
      p0193
  have p0195 :=
    @g_ceqsexv syntaxFormula0140 syntaxFormula0147 t (syn_csn (syn_csn (.cv y)))
      dv_cache_0047 dv_cache_0048 p0192 p0194
  have p0196 :=
    @g_elin (syn_copk (syn_csn (syn_csn (.cv y))) (syn_copk (.cv n) (.cv x)))
      syntaxClass0055
      (syn_cins2k (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv))))
  have p0197 := @g_vex n
  have p0198 := @g_otkelins3k (.cv y) (.cv n) (.cv x) syntaxClass0054 p0022 p0197 p0020
  have p0199 := @g_opkex (.cv y) (.cv n)
  have p0200 :=
    @g_elimak t syntaxClass0053 (syn_cpw1 (syn_c1c)) (syn_copk (.cv y) (.cv n))
      dv_cache_0049 dv_cache_0044 dv_cache_0050 p0199
  have p0201 := @g_elpw11c x (.cv t) dv_cache_0026
  have p0202 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))) syntaxFormula0148 p0201
  have p0203 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv x)))) syntaxFormula0148 x
      dv_cache_0051
  have p0204 :=
    @g_bitr4i syntaxFormula0149
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))) syntaxFormula0148)
      syntaxFormula0151 p0202 p0203
  have p0205 := @g_exbii syntaxFormula0149 syntaxFormula0151 t p0204
  have p0206 := (Nominal.biimpRefl syntaxFormula0152)
  have p0207 := @g_excom syntaxFormula0150 x t
  have p0208 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0149) (syn_wex t syntaxFormula0151)
      syntaxFormula0152 syntaxFormula0154 p0205 p0206 p0207
  have p0209 := @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv n))
  have p0210 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv x))))
      (syn_copk (.cv t) (syn_copk (.cv y) (.cv n)))
      (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv n))) syntaxClass0053
      p0209
  have p0211 :=
    @g_ceqsexv syntaxFormula0148 syntaxFormula0155 t (syn_csn (syn_csn (.cv x)))
      dv_cache_0052 dv_cache_0053 p0103 p0210
  have p0212 :=
    @g_elin (syn_copk (syn_csn (syn_csn (.cv x))) (syn_copk (.cv y) (.cv n)))
      syntaxClass0044 syntaxClass0052
  have p0213 := @g_opkex (.cv x) (.cv n)
  have p0214 :=
    @g_elimak t syntaxClass0041 (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv x) (.cv n))
      dv_cache_0054 dv_cache_0004 dv_cache_0055 p0213
  have p0215 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))))
      syntaxFormula0156 p0006
  have p0216 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))) syntaxFormula0156
      y dv_cache_0056
  have p0217 :=
    @g_bitr4i syntaxFormula0157
      (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))))
        syntaxFormula0156)
      syntaxFormula0159 p0215 p0216
  have p0218 := @g_exbii syntaxFormula0157 syntaxFormula0159 t p0217
  have p0219 := (Nominal.biimpRefl syntaxFormula0160)
  have p0220 := @g_excom syntaxFormula0158 y t
  have p0221 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0157) (syn_wex t syntaxFormula0159)
      syntaxFormula0160 syntaxFormula0162 p0218 p0219 p0220
  have p0222 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv n))
  have p0223 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
      (syn_copk (.cv t) (syn_copk (.cv x) (.cv n)))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv n)))
      syntaxClass0041 p0222
  have p0224 :=
    @g_ceqsexv syntaxFormula0156 syntaxFormula0163 t (syn_csn (syn_csn (syn_csn (.cv y))))
      dv_cache_0008 dv_cache_0057 p0014 p0223
  have p0225 :=
    @g_elsymdif
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) (.cv n)))
      (syn_cins3k (syn_cssetk)) syntaxClass0040
  have p0226 :=
    @g_otkelins3k (syn_csn (.cv y)) (.cv x) (.cv n) (syn_cssetk) p0019 p0020 p0197
  have p0227_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)) (.objMem y x)) :=
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
      p0023
  have p0227 :=
    @g_bitri syntaxFormula0164
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cssetk)) (.objMem y x) p0226
      p0227_e01_recanon
  have p0228 := @g_opkex (syn_csn (.cv y)) (.cv n)
  have p0229 :=
    @g_elimak t syntaxClass0038 (syn_cpw1 (syn_cpw1 (syn_c1c)))
      (syn_copk (syn_csn (.cv y)) (.cv n)) dv_cache_0058 dv_cache_0004 dv_cache_0059 p0228
  have p0230 := @g_elpw121c a (.cv t) dv_cache_0019
  have p0231 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))))
      syntaxFormula0165 p0230
  have p0232 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))) syntaxFormula0165
      a dv_cache_0060
  have p0233 :=
    @g_bitr4i syntaxFormula0166
      (syn_wa (syn_wex a (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))))
        syntaxFormula0165)
      syntaxFormula0168 p0231 p0232
  have p0234 := @g_exbii syntaxFormula0166 syntaxFormula0168 t p0233
  have p0235 := (Nominal.biimpRefl syntaxFormula0169)
  have p0236 := @g_excom syntaxFormula0167 a t
  have p0237 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0166) (syn_wex t syntaxFormula0168)
      syntaxFormula0169 syntaxFormula0171 p0234 p0235 p0236
  have p0238 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv a))))
      (syn_copk (syn_csn (.cv y)) (.cv n))
  have p0239 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv a)))))
      (syn_copk (.cv t) (syn_copk (syn_csn (.cv y)) (.cv n))) syntaxClass0172
      syntaxClass0038 p0238
  have p0240 :=
    @g_ceqsexv syntaxFormula0165 syntaxFormula0173 t (syn_csn (syn_csn (syn_csn (.cv a))))
      dv_cache_0061 dv_cache_0062 p0061 p0239
  have p0241 := @g_elin syntaxClass0172 (syn_cins2k (syn_cssetk)) syntaxClass0037
  have p0242 :=
    @g_otkelins2k (syn_csn (.cv a)) (syn_csn (.cv y)) (.cv n) (syn_cssetk) p0063 p0019
      p0197
  have p0243 := @g_elssetk (.cv a) (.cv n) p0065 p0197
  have p0244_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv a)) (.cv n)) (syn_cssetk)) (.objMem a n)) :=
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
      p0243
  have p0244 :=
    @g_bitri syntaxFormula0174
      (.classMem (syn_copk (syn_csn (.cv a)) (.cv n)) (syn_cssetk)) (.objMem a n) p0242
      p0244_e01_recanon
  have p0245 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (syn_csn (.cv y)) (.cv n))
  have p0246 :=
    @g_elimak t syntaxClass0036 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      syntaxClass0172 dv_cache_0063 dv_cache_0017 dv_cache_0064 p0245
  have p0247 := @g_elpw141c b (.cv t) dv_cache_0012
  have p0248 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wex b (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
      syntaxFormula0176 p0247
  have p0249 :=
    @g_n_19_41v
      (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
      syntaxFormula0176 b dv_cache_0065
  have p0250 :=
    @g_bitr4i syntaxFormula0177
      (syn_wa (syn_wex b
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))))
        syntaxFormula0176)
      syntaxFormula0179 p0248 p0249
  have p0251 := @g_exbii syntaxFormula0177 syntaxFormula0179 t p0250
  have p0252 := (Nominal.biimpRefl syntaxFormula0180)
  have p0253 := @g_excom syntaxFormula0178 b t
  have p0254 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0177) (syn_wex t syntaxFormula0179)
      syntaxFormula0180 syntaxFormula0182 p0251 p0252 p0253
  have p0255 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
  have p0256 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b))))))
      syntaxClass0172
  have p0257 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
      syntaxClass0175 syntaxClass0183 syntaxClass0036 p0256
  have p0258 :=
    @g_ceqsexv syntaxFormula0176 syntaxFormula0184 t
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) dv_cache_0066
      dv_cache_0067 p0255 p0257
  have p0259 :=
    @g_elin syntaxClass0183 (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0035
  have p0260 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv b))))
      (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (syn_csn (.cv y)) (.cv n))
      (syn_cins2k (syn_cssetk)) p0036 p0061 p0228
  have p0261 :=
    @g_otkelins2k (syn_csn (.cv b)) (syn_csn (.cv y)) (.cv n) (syn_cssetk) p0041 p0019
      p0197
  have p0262 := @g_elssetk (.cv b) (.cv n) p0043 p0197
  have p0263_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv b)) (.cv n)) (syn_cssetk)) (.objMem b n)) :=
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
      p0262
  have p0263 :=
    @g_n_3bitri syntaxFormula0185
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_copk (syn_csn (.cv y)) (.cv n))) (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv b)) (.cv n)) (syn_cssetk)) (.objMem b n) p0260
      p0261 p0263_e02_recanon
  have p0264 := @g_elin syntaxClass0183 syntaxClass0030 syntaxClass0034
  have p0265 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (.cv b))))
      (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (syn_csn (.cv y)) (.cv n))
      syntaxClass0028 p0036 p0061 p0228
  have p0266 :=
    @g_opkelcnvk (syn_csn (syn_csn (syn_csn (.cv b))))
      (syn_csn (syn_csn (syn_csn (.cv a)))) syntaxClass0027 p0036 p0061
  have p0267 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv a))) (syn_csn (syn_csn (.cv b))) syntaxClass0026
      p0070 p0071
  have p0268 :=
    @g_opksnelsik (syn_csn (.cv a)) (syn_csn (.cv b)) syntaxClass0025 p0063 p0041
  have p0269 := @g_opksnelsik (.cv a) (.cv b) syntaxClass0004 p0065 p0043
  have p0270 :=
    @g_bitri syntaxFormula0186 syntaxFormula0093
      (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0)) p0269 p0075
  have p0271 :=
    @g_n_3bitri syntaxFormula0187
      (.classMem (syn_copk (syn_csn (syn_csn (.cv a))) (syn_csn (syn_csn (.cv b))))
        syntaxClass0026)
      syntaxFormula0186 (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0)) p0267 p0268 p0270
  have p0272 :=
    @g_n_3bitri syntaxFormula0188
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv b))))
          (syn_csn (syn_csn (syn_csn (.cv a))))) syntaxClass0028)
      syntaxFormula0187 (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0)) p0265 p0266 p0271
  have p0273 :=
    @g_notbii syntaxFormula0188 (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0)) p0272
  have p0274 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0172
  have p0275 := @g_elcompl syntaxClass0183 syntaxClass0029 p0274
  have p0276 :=
    @g_n_3bitr4i (.neg syntaxFormula0188)
      (.neg (syn_wne (syn_cin (.cv a) (.cv b)) (syn_c0))) syntaxFormula0189
      (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0)) p0273 p0275 p0080
  have p0277 :=
    @g_elimak t syntaxClass0032 syntaxClass0013 syntaxClass0183 dv_cache_0068
      dv_cache_0024 dv_cache_0069 p0274
  have p0278 := @g_anbi1i syntaxFormula0096 syntaxFormula0099 syntaxFormula0191 p0086
  have p0279 := @g_n_19_41v syntaxFormula0098 syntaxFormula0191 x dv_cache_0070
  have p0280 :=
    @g_bitr4i syntaxFormula0192 (syn_wa syntaxFormula0099 syntaxFormula0191)
      syntaxFormula0194 p0278 p0279
  have p0281 := @g_exbii syntaxFormula0192 syntaxFormula0194 t p0280
  have p0282 := (Nominal.biimpRefl syntaxFormula0195)
  have p0283 := @g_excom syntaxFormula0193 x t
  have p0284 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0192) (syn_wex t syntaxFormula0194)
      syntaxFormula0195 syntaxFormula0197 p0281 p0282 p0283
  have p0285 := @g_opkeq1 (.cv t) syntaxClass0097 syntaxClass0183
  have p0286 :=
    @g_eleq1d syntaxFormula0098 syntaxClass0190 syntaxClass0198 syntaxClass0032 p0285
  have p0287 :=
    @g_ceqsexv syntaxFormula0191 syntaxFormula0199 t syntaxClass0097 dv_cache_0028
      dv_cache_0071 p0094 p0286
  have p0288 :=
    @g_elsymdif syntaxClass0198
      (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk))))) syntaxClass0031
  have p0289 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0172
      (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))) p0099 p0255 p0245
  have p0290 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (syn_csn (.cv y)) (.cv n))
      (syn_cins3k (syn_csik (syn_cssetk))) p0101 p0061 p0228
  have p0291 :=
    @g_otkelins3k (syn_csn (syn_csn (.cv x))) (syn_csn (.cv y)) (.cv n)
      (syn_csik (syn_cssetk)) p0103 p0019 p0197
  have p0292_e02_recanon :
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
      p0107
  have p0292 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk (syn_csn (.cv y)) (.cv n))) (syn_cins3k (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv y)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv y)) (syn_cssetk)) (.objMem x y) p0291
      p0106 p0292_e02_recanon
  have p0293 :=
    @g_n_3bitri syntaxFormula0200
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          syntaxClass0172) (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
          (syn_copk (syn_csn (.cv y)) (.cv n))) (syn_cins3k (syn_csik (syn_cssetk))))
      (.objMem x y) p0289 p0290 p0292
  have p0294 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0172
      (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0099 p0255 p0245
  have p0295 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv a)))) (syn_copk (syn_csn (.cv y)) (.cv n))
      (syn_csik (syn_csik (syn_csik (syn_cssetk)))) p0101 p0061 p0228
  have p0296_e01_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk)) (.objMem x a)) :=
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
      p0119
  have p0296 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv a)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv a)) (syn_cssetk)) (.objMem x a) p0118
      p0296_e01_recanon
  have p0297 :=
    @g_n_3bitri syntaxFormula0114 syntaxFormula0111
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv a)))
        (syn_csik (syn_cssetk)))
      (.objMem x a) p0116 p0117 p0296
  have p0298 :=
    @g_n_3bitri syntaxFormula0201
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          syntaxClass0172) (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      syntaxFormula0114 (.objMem x a) p0294 p0295 p0297
  have p0299 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))) syntaxClass0172
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0099 p0255
      p0245
  have p0300 := @g_snex (syn_csn (syn_csn (syn_csn (.cv b))))
  have p0301 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))
      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0111 p0300
  have p0302 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_csn (syn_csn (syn_csn (.cv b)))) (syn_csik (syn_csik (syn_csik (syn_cssetk))))
      p0101 p0036
  have p0303_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv x)) (.cv b)) (syn_cssetk)) (.objMem x b)) :=
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
      p0128
  have p0303 :=
    @g_n_3bitri syntaxFormula0118
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn (.cv b)))
        (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) (.cv b)) (syn_cssetk)) (.objMem x b) p0126
      p0127 p0303_e02_recanon
  have p0304 :=
    @g_n_3bitri syntaxFormula0202 syntaxFormula0117 syntaxFormula0118 (.objMem x b) p0302
      p0125 p0303
  have p0305 :=
    @g_n_3bitri syntaxFormula0203
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv b)))))))
        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))))
      syntaxFormula0202 (.objMem x b) p0299 p0301 p0304
  have p0306 :=
    @g_orbi12i syntaxFormula0201 (.objMem x a) syntaxFormula0203 (.objMem x b) p0298 p0305
  have p0307 :=
    @g_elun syntaxClass0198
      (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      syntaxClass0010
  have p0308_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv x) (syn_cun (.cv a) (.cv b)))
        (syn_wo (.objMem x a) (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl, syn_wo]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.neg
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · apply Nominal.RecanonTransportDev.TRecanonWff.neg
              exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classMem_objMem _ _
          · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0134
  have p0308 :=
    @g_n_3bitr4i (syn_wo syntaxFormula0201 syntaxFormula0203)
      (syn_wo (.objMem x a) (.objMem x b)) syntaxFormula0204
      (.classMem (.cv x) (syn_cun (.cv a) (.cv b))) p0306 p0307 p0308_e02_recanon
  have p0309 :=
    @g_bibi12i syntaxFormula0200 (.objMem x y) syntaxFormula0204
      (.classMem (.cv x) (syn_cun (.cv a) (.cv b))) p0293 p0308
  have p0310 :=
    @g_notbii syntaxFormula0205
      (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b)))) p0309
  have p0311 :=
    @g_n_3bitri syntaxFormula0196 syntaxFormula0199 (.neg syntaxFormula0205)
      (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b))))) p0287
      p0288 p0310
  have p0312 :=
    @g_exbii syntaxFormula0196
      (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b))))) x p0311
  have p0313 :=
    @g_n_3bitri syntaxFormula0206 syntaxFormula0195 syntaxFormula0197
      (syn_wex x (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b))))))
      p0277 p0284 p0312
  have p0314 :=
    @g_notbii syntaxFormula0206
      (syn_wex x (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b))))))
      p0313
  have p0315 := @g_elcompl syntaxClass0183 syntaxClass0033 p0274
  have p0316 :=
    @g_n_3bitr4i (.neg syntaxFormula0206)
      (.neg (syn_wex x
          (.neg (syn_wb (.objMem x y) (.classMem (.cv x) (syn_cun (.cv a) (.cv b)))))))
      syntaxFormula0207 (.classEq (.cv y) (syn_cun (.cv a) (.cv b))) p0314 p0315 p0145
  have p0317 :=
    @g_anbi12i syntaxFormula0189 (.classEq (syn_cin (.cv a) (.cv b)) (syn_c0))
      syntaxFormula0207 (.classEq (.cv y) (syn_cun (.cv a) (.cv b))) p0276 p0316
  have p0318 :=
    @g_bitri syntaxFormula0208 (syn_wa syntaxFormula0189 syntaxFormula0207)
      syntaxFormula0125 p0264 p0317
  have p0319 :=
    @g_anbi12i syntaxFormula0185 (.objMem b n) syntaxFormula0208 syntaxFormula0125 p0263
      p0318
  have p0320 :=
    @g_n_3bitri syntaxFormula0181 syntaxFormula0184
      (syn_wa syntaxFormula0185 syntaxFormula0208)
      (syn_wa (.objMem b n) syntaxFormula0125) p0258 p0259 p0319
  have p0321 :=
    @g_exbii syntaxFormula0181 (syn_wa (.objMem b n) syntaxFormula0125) b p0320
  have p0322 :=
    @g_n_3bitri syntaxFormula0209 syntaxFormula0180 syntaxFormula0182
      (syn_wex b (syn_wa (.objMem b n) syntaxFormula0125)) p0246 p0254 p0321
  have p0323 := (Nominal.biimpRefl syntaxFormula0210)
  have p0324_e01_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0210 (syn_wex b (syn_wa (.objMem b n) syntaxFormula0125))) :=
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
      p0323
  have p0324 :=
    @g_bitr4i syntaxFormula0209 (syn_wex b (syn_wa (.objMem b n) syntaxFormula0125))
      syntaxFormula0210 p0322 p0324_e01_recanon
  have p0325 :=
    @g_anbi12i syntaxFormula0174 (.objMem a n) syntaxFormula0209 syntaxFormula0210 p0244
      p0324
  have p0326 :=
    @g_n_3bitri syntaxFormula0170 syntaxFormula0173
      (syn_wa syntaxFormula0174 syntaxFormula0209)
      (syn_wa (.objMem a n) syntaxFormula0210) p0240 p0241 p0325
  have p0327 :=
    @g_exbii syntaxFormula0170 (syn_wa (.objMem a n) syntaxFormula0210) a p0326
  have p0328 :=
    @g_n_3bitri syntaxFormula0211 syntaxFormula0169 syntaxFormula0171
      (syn_wex a (syn_wa (.objMem a n) syntaxFormula0210)) p0229 p0237 p0327
  have p0329 :=
    @g_otkelins2k (syn_csn (.cv y)) (.cv x) (.cv n) syntaxClass0039 p0019 p0020 p0197
  have p0330 := (Nominal.biimpRefl syntaxFormula0212)
  have p0331_e02_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0212 (syn_wex a (syn_wa (.objMem a n) syntaxFormula0210))) :=
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
      p0330
  have p0331 :=
    @g_n_3bitr4i syntaxFormula0211 (syn_wex a (syn_wa (.objMem a n) syntaxFormula0210))
      syntaxFormula0213 syntaxFormula0212 p0328 p0329 p0331_e02_recanon
  have p0332 :=
    @g_bibi12i syntaxFormula0164 (.objMem y x) syntaxFormula0213 syntaxFormula0212 p0227
      p0331
  have p0333 := @g_notbii syntaxFormula0214 (syn_wb (.objMem y x) syntaxFormula0212) p0332
  have p0334 :=
    @g_n_3bitri syntaxFormula0161 syntaxFormula0163 (.neg syntaxFormula0214)
      (.neg (syn_wb (.objMem y x) syntaxFormula0212)) p0224 p0225 p0333
  have p0335 :=
    @g_exbii syntaxFormula0161 (.neg (syn_wb (.objMem y x) syntaxFormula0212)) y p0334
  have p0336 :=
    @g_n_3bitri syntaxFormula0215 syntaxFormula0160 syntaxFormula0162
      (syn_wex y (.neg (syn_wb (.objMem y x) syntaxFormula0212))) p0214 p0221 p0335
  have p0337 :=
    @g_notbii syntaxFormula0215
      (syn_wex y (.neg (syn_wb (.objMem y x) syntaxFormula0212))) p0336
  have p0338 := @g_elcompl (syn_copk (.cv x) (.cv n)) syntaxClass0042 p0213
  have p0339 := @g_alex (syn_wb (.objMem y x) syntaxFormula0212) y
  have p0340 :=
    @g_n_3bitr4i (.neg syntaxFormula0215)
      (.neg (syn_wex y (.neg (syn_wb (.objMem y x) syntaxFormula0212)))) syntaxFormula0216
      (.all y (syn_wb (.objMem y x) syntaxFormula0212)) p0337 p0338 p0339
  have p0341 := @g_otkelins2k (.cv x) (.cv y) (.cv n) syntaxClass0043 p0020 p0022 p0197
  have p0342 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_addc y a b (.cv n)
      (.cv n) dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0072 dv_cache_0073
      dv_cache_0074 dv_cache_0036 dv_cache_0037 dv_cache_0038
  have p0343 := @g_eqeq2i (syn_cplc (.cv n) (.cv n)) syntaxClass0217 (.cv x) p0342
  have p0344 := @g_eqabb syntaxFormula0212 y (.cv x) dv_cache_0039
  have p0345_e01_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0218 (.all y (syn_wb (.objMem y x) syntaxFormula0212))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb]
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
      p0344
  have p0345 :=
    @g_bitri (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) syntaxFormula0218
      (.all y (syn_wb (.objMem y x) syntaxFormula0212)) p0343 p0345_e01_recanon
  have p0346 :=
    @g_n_3bitr4i syntaxFormula0216 (.all y (syn_wb (.objMem y x) syntaxFormula0212))
      syntaxFormula0219 (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) p0340 p0341 p0345
  have p0347 := @g_opkelimagek (.cv x) (.cv y) syntaxClass0050 p0020 p0022
  have p0348 := @g_otkelins3k (.cv x) (.cv y) (.cv n) syntaxClass0051 p0020 p0022 p0197
  have p0349 := @g_dfaddc2 (.cv x) (syn_c1c)
  have p0350 := @g_eqeq2i (syn_cplc (.cv x) (syn_c1c)) syntaxClass0220 (.cv y) p0349
  have p0351 :=
    @g_n_3bitr4i (.classMem (syn_copk (.cv x) (.cv y)) syntaxClass0051)
      (.classEq (.cv y) syntaxClass0220) syntaxFormula0221
      (.classEq (.cv y) (syn_cplc (.cv x) (syn_c1c))) p0347 p0348 p0350
  have p0352 :=
    @g_anbi12i syntaxFormula0219 (.classEq (.cv x) (syn_cplc (.cv n) (.cv n)))
      syntaxFormula0221 (.classEq (.cv y) (syn_cplc (.cv x) (syn_c1c))) p0346 p0351
  have p0353 :=
    @g_n_3bitri syntaxFormula0153 syntaxFormula0155
      (syn_wa syntaxFormula0219 syntaxFormula0221) syntaxFormula0222 p0211 p0212 p0352
  have p0354 := @g_exbii syntaxFormula0153 syntaxFormula0222 x p0353
  have p0355 :=
    @g_n_3bitri syntaxFormula0223 syntaxFormula0152 syntaxFormula0154
      (syn_wex x syntaxFormula0222) p0200 p0208 p0354
  have p0356 := @g_addcex (.cv n) (.cv n) p0197 p0197
  have p0357 := @g_addceq1 (.cv x) (syn_cplc (.cv n) (.cv n)) (syn_c1c)
  have p0358 :=
    @g_eqeq2d (.classEq (.cv x) (syn_cplc (.cv n) (.cv n))) (syn_cplc (.cv x) (syn_c1c))
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (.cv y) p0357
  have p0359 :=
    @g_ceqsexv (.classEq (.cv y) (syn_cplc (.cv x) (syn_c1c)))
      (.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) x
      (syn_cplc (.cv n) (.cv n)) dv_cache_0075 dv_cache_0076 p0356 p0358
  have p0360 :=
    @g_n_3bitri syntaxFormula0224 syntaxFormula0223 (syn_wex x syntaxFormula0222)
      (.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) p0198 p0355 p0359
  have p0361 :=
    @g_otkelins2k (.cv y) (.cv n) (.cv x)
      (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv))) p0022 p0197 p0020
  have p0362 :=
    @g_eldif (syn_copk (.cv y) (.cv x)) (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv))
  have p0363 := @g_opkelidkg (.cv y) (.cv x) (syn_cvv) (syn_cvv)
  have p0364_e02_recanon :
    Nominal.NPrf
      (.imp (syn_wa (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv)))
        (syn_wb (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.objEq y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wa, syn_cvv, syn_wb, syn_copk, syn_cpr, syn_cun, syn_cnin,
          syn_wnan, syn_ccompl, syn_csn, syn_cidk, syn_wex]
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
      p0363
  have p0364 :=
    @g_mp2an (.classMem (.cv y) (syn_cvv)) (.classMem (.cv x) (syn_cvv))
      (syn_wb (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.objEq y x)) p0022 p0020
      p0364_e02_recanon
  have p0365 := @g_equcom y x
  have p0366 :=
    @g_bitri (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.objEq y x) (.objEq x y)
      p0364 p0365
  have p0367 := @g_opkelxpk (.cv y) (.cv x) (syn_csn (syn_c0)) (syn_cvv) p0022 p0020
  have p0368 :=
    @g_mpbiran2
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))
      (.classMem (.cv y) (syn_csn (syn_c0))) (.classMem (.cv x) (syn_cvv)) p0020 p0367
  have p0369 := @g_elsnc (.cv y) (syn_c0) p0022
  have p0370 :=
    @g_bitri
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))
      (.classMem (.cv y) (syn_csn (syn_c0))) (.classEq (.cv y) (syn_c0)) p0368 p0369
  have p0371 :=
    @g_notbii
      (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))
      (.classEq (.cv y) (syn_c0)) p0370
  have p0372 :=
    @g_anbi12i (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.objEq x y)
      (.neg (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv))))
      (.neg (.classEq (.cv y) (syn_c0))) p0366 p0371
  have p0373 :=
    @g_n_3bitri syntaxFormula0225
      (.classMem (syn_copk (.cv y) (.cv x))
        (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv))))
      (syn_wa (.classMem (syn_copk (.cv y) (.cv x)) (syn_cidk)) (.neg
          (.classMem (syn_copk (.cv y) (.cv x)) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))))
      (syn_wa (.objEq x y) (.neg (.classEq (.cv y) (syn_c0)))) p0361 p0362 p0372
  have p0374 :=
    @g_anbi12i syntaxFormula0224
      (.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) syntaxFormula0225
      (syn_wa (.objEq x y) (.neg (.classEq (.cv y) (syn_c0)))) p0360 p0373
  have p0375 :=
    @g_n_3bitri syntaxFormula0145 syntaxFormula0147
      (syn_wa syntaxFormula0224 syntaxFormula0225)
      (syn_wa (.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
        (syn_wa (.objEq x y) (.neg (.classEq (.cv y) (syn_c0)))))
      p0195 p0196 p0374
  have p0376 :=
    @g_exbii syntaxFormula0145
      (syn_wa (.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
        (syn_wa (.objEq x y) (.neg (.classEq (.cv y) (syn_c0)))))
      y p0375
  have p0377 :=
    @g_n_3bitri syntaxFormula0226 syntaxFormula0144 syntaxFormula0146
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
          (syn_wa (.objEq x y) (.neg (.classEq (.cv y) (syn_c0))))))
      p0183 p0191 p0376
  have p0378 := @g_n_1cex
  have p0379 := @g_addcex (syn_cplc (.cv n) (.cv n)) (syn_c1c) p0356 p0378
  have p0380 := @g_eqeq2 (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (.cv x)
  have p0381 := @g_eqeq1 (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)
  have p0382 :=
    @g_notbid (.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.classEq (.cv y) (syn_c0))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0381
  have p0383_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
        (syn_wb (.objEq x y)
          (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_cplc, syn_wrex, syn_wex, syn_wa, syn_c1c, syn_wb]
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · apply Nominal.RecanonTransportDev.TRecanonWff.neg
          apply Nominal.RecanonTransportDev.TRecanonWff.imp
          · apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
          · apply Nominal.RecanonTransportDev.TRecanonWff.neg
            apply Nominal.RecanonTransportDev.TRecanonWff.imp
            · exact Nominal.RecanonTransportDev.TRecanonWff.same _
            · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0380
  have p0383 :=
    @g_anbi12d (.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.objEq x y) (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.neg (.classEq (.cv y) (syn_c0)))
      (.neg (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))
      p0383_e00_recanon p0382
  have p0384 :=
    @g_ceqsexv (syn_wa (.objEq x y) (.neg (.classEq (.cv y) (syn_c0))))
      (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
        (.neg (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))
      y (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) dv_cache_0077 dv_cache_0078 p0379
      p0383
  have p0385 :=
    @g_annim (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))
  have p0386 :=
    @g_n_3bitri syntaxFormula0226
      (syn_wex y (syn_wa (.classEq (.cv y) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
          (syn_wa (.objEq x y) (.neg (.classEq (.cv y) (syn_c0))))))
      (syn_wa (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
        (.neg (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))))
      syntaxFormula0228 p0377 p0384 p0385
  have p0387 := @g_rexbii syntaxFormula0226 syntaxFormula0228 n (syn_cnnc) p0386
  have p0388 :=
    @g_bitri syntaxFormula0229 (syn_wrex n (syn_cnnc) syntaxFormula0226) syntaxFormula0230
      p0181 p0387
  have p0389 := @g_notbii syntaxFormula0229 syntaxFormula0230 p0388
  have p0390 := @g_elcompl (.cv x) syntaxClass0058 p0020
  have p0391 :=
    (Nominal.biimpRefl (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))
  have p0392 :=
    (Nominal.biimpRefl (syn_wne (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))))
  have p0393 :=
    @g_imbi12i (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))
      (.neg (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))
      (syn_wne (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.neg (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))) p0391
      p0392
  have p0394 :=
    @g_con34b (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))
      (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0))
  have p0395 :=
    @g_bitr4i syntaxFormula0231
      (.imp (.neg (.classEq (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)))
        (.neg (.classEq (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)))))
      syntaxFormula0227 p0393 p0394
  have p0396 := @g_ralbii syntaxFormula0231 syntaxFormula0227 n (syn_cnnc) p0395
  have p0397 := @g_dfral2 syntaxFormula0227 n (syn_cnnc)
  have p0398 :=
    @g_bitri syntaxFormula0232 (syn_wral n (syn_cnnc) syntaxFormula0227) syntaxFormula0233
      p0396 p0397
  have p0399 :=
    @g_n_3bitr4i (.neg syntaxFormula0229) syntaxFormula0233 syntaxFormula0234
      syntaxFormula0232 p0389 p0390 p0398
  have p0400 :=
    @g_orbi12i (.classMem (.cv x) (syn_csn (syn_c0))) (.classEq (.cv x) (syn_c0))
      syntaxFormula0234 syntaxFormula0232 p0180 p0399
  have p0401 :=
    @g_n_3bitri syntaxFormula0138 syntaxFormula0139
      (syn_wo (.classMem (.cv x) (syn_csn (syn_c0))) syntaxFormula0234) syntaxFormula0235
      p0178 p0179 p0400
  have p0402 :=
    @g_anbi12i syntaxFormula0135 (.classEq (.cv x) (syn_cplc (.cv j) (.cv j)))
      syntaxFormula0138 syntaxFormula0235 p0176 p0401
  have p0403 :=
    @g_bitri syntaxFormula0236 (syn_wa syntaxFormula0135 syntaxFormula0138)
      syntaxFormula0237 p0003 p0402
  have p0404 := @g_exbii syntaxFormula0236 syntaxFormula0237 x p0403
  have p0405 := @g_addcex (.cv j) (.cv j) p0001 p0001
  have p0406 := @g_eqeq1 (.cv x) (syn_cplc (.cv j) (.cv j)) (syn_c0)
  have p0407 :=
    @g_neeq1 (.cv x) (syn_cplc (.cv j) (.cv j))
      (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))
  have p0408 :=
    @g_imbi2d (.classEq (.cv x) (syn_cplc (.cv j) (.cv j)))
      (syn_wne (.cv x) (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c))) syntaxFormula0000
      (syn_wne (syn_cplc (syn_cplc (.cv n) (.cv n)) (syn_c1c)) (syn_c0)) p0407
  have p0409 :=
    @g_ralbidv (.classEq (.cv x) (syn_cplc (.cv j) (.cv j))) syntaxFormula0231
      syntaxFormula0001 n (syn_cnnc) dv_cache_0079 p0408
  have p0410 :=
    @g_orbi12d (.classEq (.cv x) (syn_cplc (.cv j) (.cv j))) (.classEq (.cv x) (syn_c0))
      (.classEq (syn_cplc (.cv j) (.cv j)) (syn_c0)) syntaxFormula0232 syntaxFormula0002
      p0406 p0409
  have p0411 :=
    @g_ceqsexv syntaxFormula0235 syntaxFormula0003 x (syn_cplc (.cv j) (.cv j))
      dv_cache_0080 dv_cache_0081 p0405 p0410
  have p0412 :=
    @g_n_3bitri syntaxFormula0239 (syn_wex x syntaxFormula0236)
      (syn_wex x syntaxFormula0237) syntaxFormula0003 p0002 p0404 p0411
  have p0413 := (Nominal.biimpRefl (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0)))
  have p0414 :=
    @g_imbi1i (syn_wne (syn_cplc (.cv j) (.cv j)) (syn_c0))
      (.neg (.classEq (syn_cplc (.cv j) (.cv j)) (syn_c0))) syntaxFormula0002 p0413
  have p0415 :=
    @g_n_3bitr4i syntaxFormula0003
      (.imp (.neg (.classEq (syn_cplc (.cv j) (.cv j)) (syn_c0))) syntaxFormula0002)
      syntaxFormula0239 syntaxFormula0240 p0000 p0412 p0414
  have p0416 := @g_eqabi syntaxFormula0240 j syntaxClass0238 dv_cache_0082 p0415
  have p0417 := @g_ssetkex
  have p0418 := @g_ins3kex (syn_cssetk) p0417
  have p0420 := @g_ins2kex (syn_cssetk) p0417
  have p0421 := @g_ins2kex (syn_cins2k (syn_cssetk)) p0420
  have p0422 := @g_inex (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)) p0418 p0420
  have p0424 := @g_pw1ex (syn_c1c) p0378
  have p0425 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0424
  have p0426 :=
    @g_imakex (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0422 p0425
  have p0427 := @g_complex syntaxClass0004 p0426
  have p0428 := @g_sikex syntaxClass0005 p0427
  have p0429 := @g_sikex syntaxClass0006 p0428
  have p0430 := @g_sikex syntaxClass0007 p0429
  have p0431 := @g_ins3kex syntaxClass0008 p0430
  have p0433 := @g_sikex (syn_cssetk) p0417
  have p0434 := @g_ins3kex (syn_csik (syn_cssetk)) p0433
  have p0435 := @g_ins2kex (syn_cins3k (syn_csik (syn_cssetk))) p0434
  have p0436 := @g_ins2kex (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))) p0435
  have p0437 := @g_sikex (syn_csik (syn_cssetk)) p0433
  have p0438 := @g_sikex (syn_csik (syn_csik (syn_cssetk))) p0437
  have p0439 := @g_sikex (syn_csik (syn_csik (syn_csik (syn_cssetk)))) p0438
  have p0440 := @g_sikex (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0439
  have p0441 :=
    @g_ins3kex (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0440
  have p0442 := @g_ins3kex (syn_csik (syn_csik (syn_csik (syn_cssetk)))) p0438
  have p0443 :=
    @g_ins2kex (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))) p0442
  have p0444 :=
    @g_unex syntaxClass0010
      (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk)))))) p0441 p0443
  have p0445 :=
    @g_symdifex (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
      syntaxClass0011 p0436 p0444
  have p0446 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0425
  have p0447 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0446
  have p0448 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0447
  have p0449 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))) p0448
  have p0450 :=
    @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0449
  have p0451 := @g_imakex syntaxClass0012 syntaxClass0013 p0445 p0450
  have p0452 := @g_complex syntaxClass0014 p0451
  have p0453 := @g_inex syntaxClass0009 syntaxClass0015 p0431 p0452
  have p0454 := @g_inex (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0016 p0421 p0453
  have p0455 :=
    @g_imakex syntaxClass0017 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0454
      p0447
  have p0456 := @g_inex (syn_cins2k (syn_cssetk)) syntaxClass0018 p0420 p0455
  have p0457 := @g_imakex syntaxClass0019 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0456 p0425
  have p0458 := @g_ins2kex syntaxClass0020 p0457
  have p0459 := @g_symdifex (syn_cins3k (syn_cssetk)) syntaxClass0021 p0418 p0458
  have p0460 := @g_imakex syntaxClass0022 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0459 p0425
  have p0461 := @g_complex syntaxClass0023 p0460
  have p0462 := @g_snex (syn_c0)
  have p0463 := @g_sikex syntaxClass0004 p0426
  have p0464 := @g_sikex syntaxClass0025 p0463
  have p0465 := @g_sikex syntaxClass0026 p0464
  have p0466 := @g_cnvkex syntaxClass0027 p0465
  have p0467 := @g_ins3kex syntaxClass0028 p0466
  have p0468 := @g_complex syntaxClass0029 p0467
  have p0469 :=
    @g_unex (syn_cins2k (syn_cins3k (syn_csik (syn_csik (syn_csik (syn_cssetk))))))
      syntaxClass0010 p0443 p0441
  have p0470 :=
    @g_symdifex (syn_cins2k (syn_cins2k (syn_cins3k (syn_csik (syn_cssetk)))))
      syntaxClass0031 p0436 p0469
  have p0471 := @g_imakex syntaxClass0032 syntaxClass0013 p0470 p0450
  have p0472 := @g_complex syntaxClass0033 p0471
  have p0473 := @g_inex syntaxClass0030 syntaxClass0034 p0468 p0472
  have p0474 := @g_inex (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0035 p0421 p0473
  have p0475 :=
    @g_imakex syntaxClass0036 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0474
      p0447
  have p0476 := @g_inex (syn_cins2k (syn_cssetk)) syntaxClass0037 p0420 p0475
  have p0477 := @g_imakex syntaxClass0038 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0476 p0425
  have p0478 := @g_ins2kex syntaxClass0039 p0477
  have p0479 := @g_symdifex (syn_cins3k (syn_cssetk)) syntaxClass0040 p0418 p0478
  have p0480 := @g_imakex syntaxClass0041 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0479 p0425
  have p0481 := @g_complex syntaxClass0042 p0480
  have p0482 := @g_ins2kex syntaxClass0043 p0481
  have p0483 := @g_addcexlem
  have p0484 := @g_imakex syntaxClass0049 (syn_cpw1 (syn_cpw1 (syn_c1c))) p0483 p0425
  have p0485 := @g_imagekex syntaxClass0050 p0484
  have p0486 := @g_ins3kex syntaxClass0051 p0485
  have p0487 := @g_inex syntaxClass0044 syntaxClass0052 p0482 p0486
  have p0488 := @g_imakex syntaxClass0053 (syn_cpw1 (syn_c1c)) p0487 p0424
  have p0489 := @g_ins3kex syntaxClass0054 p0488
  have p0490 := @g_idkex
  have p0491 := @g_vvex
  have p0492 := @g_xpkex (syn_csn (syn_c0)) (syn_cvv) p0462 p0491
  have p0493 := @g_difex (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)) p0490 p0492
  have p0494 :=
    @g_ins2kex (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv))) p0493
  have p0495 :=
    @g_inex syntaxClass0055
      (syn_cins2k (syn_cdif (syn_cidk) (syn_cxpk (syn_csn (syn_c0)) (syn_cvv)))) p0489
      p0494
  have p0496 := @g_imakex syntaxClass0056 (syn_cpw1 (syn_c1c)) p0495 p0424
  have p0497 := @g_nncex
  have p0498 := @g_imakex syntaxClass0057 (syn_cnnc) p0496 p0497
  have p0499 := @g_complex syntaxClass0058 p0498
  have p0500 := @g_unex (syn_csn (syn_c0)) syntaxClass0059 p0462 p0499
  have p0502 := @g_xpkex syntaxClass0060 (syn_cvv) p0500 p0491
  have p0503 := @g_inex syntaxClass0024 syntaxClass0061 p0461 p0502
  have p0505 := @g_imakex syntaxClass0062 (syn_cvv) p0503 p0491
  have p0506 :=
    @g_eqeltrri syntaxClass0238 (.cab j syntaxFormula0240) (syn_cvv) p0416 p0505
  exact p0506


end NFChoice.DirectNominalPrf.WPPReplay
