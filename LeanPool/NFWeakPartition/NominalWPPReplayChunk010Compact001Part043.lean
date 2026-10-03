/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk010Compact001Part042

/-! NF weak partition development: NominalWPPReplayChunk010Compact001Part043. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_setconslem3 (A : Class) (B : Class) (C : Class)
    (hyp_setconslem3_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_setconslem3_2 : Nominal.NPrf (.classMem B (syn_cvv)))
    (hyp_setconslem3_3 : Nominal.NPrf (.classMem C (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (.classEq A (syn_cop B C))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv ∪ C.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let t : Var := freshVar proofSupport 2
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_x_not_C : x ∉ C.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_y_not_C : y ∉ C.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_left _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_C : t ∉ C.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have dv_cache_0001 :
    t ∉
      ((syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                          (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                  (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0002 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
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
  have dv_cache_0003 : t ∉ ((syn_copk (syn_csn (syn_csn A)) (syn_copk B C))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_t_not_A, fresh_t_not_B, fresh_t_not_C, or_false, not_false_eq_true])
  have dv_cache_0004 : x ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0005 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_not_A, fresh_x_not_B, fresh_x_not_C,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0007 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B, fresh_t_not_C,
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
  have dv_cache_0009 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0010 : y ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_C, not_false_eq_true])
  have dv_cache_0011 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0012 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0013 : x ∉ (B).fv :=
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
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0014 : x ∉ (C).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_C, not_false_eq_true])
  have dv_cache_0015 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have p0000 := @g_opkex (syn_csn (syn_csn A)) (syn_copk B C)
  have p0001 :=
    @g_elimak t
      (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                    (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0000
  have p0002 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
  have p0003 := @g_elpw141c x (.cv t) dv_cache_0004
  have p0004 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
        (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                          (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                  (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0003
  have p0005 :=
    @g_n_19_41v
      (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
        (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                          (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                  (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      x dv_cache_0005
  have p0006 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wa (syn_wex x
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex x (syn_wa
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0004 p0005
  have p0007 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex x (syn_wa
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      t p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      x t
  have p0009 :=
    @g_bitr4i
      (syn_wex t
        (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wex t (syn_wex x (syn_wa
            (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wex x (syn_wex t (syn_wa
            (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      p0007 p0008
  have p0010 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cimak
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex t
        (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wex x (syn_wex t (syn_wa
            (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      p0001 p0002 p0009
  have p0011 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))
  have p0012 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
      (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))
  have p0013 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
      (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
      (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
        (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
      (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
            (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                    (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0012
  have p0014 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
        (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                          (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                  (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
        (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                          (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                  (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      t (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))) dv_cache_0006
      dv_cache_0007 p0011 p0013
  have p0015 :=
    @g_elsymdif
      (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
        (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
      (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                    (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                    (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                                (syn_cssetk))
                              (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0016 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0017 := @g_snex (syn_csn A)
  have p0018 := @g_opkex B C
  have p0019 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn A))
      (syn_copk B C) (syn_csik (syn_csik (syn_cssetk))) p0016 p0017 p0018
  have p0020 := @g_snex (syn_csn (.cv x))
  have p0021 := @g_snex A
  have p0022 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv x))) (syn_csn A) (syn_csik (syn_cssetk)) p0020
      p0021
  have p0023 := @g_snex (.cv x)
  have p0024 := @g_opksnelsik (syn_csn (.cv x)) A (syn_cssetk) p0023 hyp_setconslem3_1
  have p0025 := @g_vex x
  have p0026 := @g_elssetk (.cv x) A p0025 hyp_setconslem3_1
  have p0027 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn A)) (syn_csik (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) A) (syn_cssetk)) (.classMem (.cv x) A) p0024
      p0026
  have p0028 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn A)))
        (syn_csik (syn_csik (syn_cssetk))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv x))) (syn_csn A)) (syn_csik (syn_cssetk)))
      (.classMem (.cv x) A) p0019 p0022 p0027
  have p0029 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_csn (syn_csn A))
      (syn_copk B C)
      (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                    (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                    (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                  (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                          (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                              (syn_cssetk))
                            (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0016 p0017 p0018
  have p0030 :=
    @g_elun (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk B C))
      (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
  have p0031 :=
    @g_otkelins3k (syn_csn (.cv x)) B C
      (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                    (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      p0023 hyp_setconslem3_2 hyp_setconslem3_3
  have p0032 :=
    @g_setconslem1 y (.cv x) B dv_cache_0008 dv_cache_0009 p0025 hyp_setconslem3_2
  have p0033 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk B C)) (syn_cins3k
          (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
      (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
              (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                            (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y)))) p0031 p0032
  have p0034 :=
    @g_otkelins2k (syn_csn (.cv x)) B C
      (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                          (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                      (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0023 hyp_setconslem3_2 hyp_setconslem3_3
  have p0035 :=
    @g_setconslem2 y (.cv x) C dv_cache_0008 dv_cache_0010 p0025 hyp_setconslem3_3
  have p0036 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk B C)) (syn_cins2k
          (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                            (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                              (syn_cssetk))
                            (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (.classMem (syn_copk (syn_csn (.cv x)) C) (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                      (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_wrex y C (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      p0034 p0035
  have p0037 :=
    @g_orbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk B C)) (syn_cins3k
          (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                  (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                    (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
      (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk B C)) (syn_cins2k
          (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                            (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                                        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                              (syn_cssetk))
                            (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wrex y C (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))
      p0033 p0036
  have p0038 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))) (syn_cins2k (syn_cun (syn_cins3k
              (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                          (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                      (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk B C)) (syn_cun
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                    (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                                (syn_cssetk))
                              (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wo (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk B C))
          (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
        (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk B C)) (syn_cins2k
            (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                              (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                                (syn_cssetk))
                              (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wo (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y C
          (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      p0029 p0030 p0037
  have p0039 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
      (.classMem (.cv x) A)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))) (syn_cins2k (syn_cun (syn_cins3k
              (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                          (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                      (syn_cin (syn_cins3k (syn_cssetk))
                                        (syn_cins2k (syn_cssetk)))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
            (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_wo (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y C
          (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))
      p0028 p0038
  have p0040 :=
    @g_xchbinx
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
        (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                          (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                  (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
            (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))) (syn_cins2k (syn_cun (syn_cins3k
                (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                            (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                        (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                  (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wb (.classMem (.cv x) A) (syn_wo (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y))))
          (syn_wrex y C (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      p0015 p0039
  have p0041 :=
    @g_bitri
      (syn_wex t (syn_wa
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x))))))
          (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
        (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
              (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                          (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                  (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.neg (syn_wb (.classMem (.cv x) A)
          (syn_wo (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y C
              (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
      p0014 p0040
  have p0042 :=
    @g_exbii
      (syn_wex t (syn_wa
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (.neg (syn_wb (.classMem (.cv x) A)
          (syn_wo (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y C
              (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
      x p0041
  have p0043 :=
    @g_exnal
      (syn_wb (.classMem (.cv x) A) (syn_wo (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y))))
          (syn_wrex y C (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))
      x
  have p0044 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cimak
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_wex x (syn_wex t (syn_wa
            (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv x)))))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)))
              (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                    (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                    (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                            (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wex x (.neg (syn_wb (.classMem (.cv x) A)
            (syn_wo (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y C
                (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))))
      (.neg (.all x (syn_wb (.classMem (.cv x) A)
            (syn_wo (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y C
                (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c)))))))))
      p0010 p0042 p0043
  have p0045 :=
    @g_con2bii
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cimak
          (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                            (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                  (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.all x (syn_wb (.classMem (.cv x) A)
          (syn_wo (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y C
              (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
      p0044
  have p0046 :=
    @g_eqop x y A B C dv_cache_0011 dv_cache_0012 dv_cache_0009 dv_cache_0013
      dv_cache_0010 dv_cache_0014 dv_cache_0015
  have p0047 :=
    @g_elcompl (syn_copk (syn_csn (syn_csn A)) (syn_copk B C))
      (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k
            (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                    (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                  (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0000
  have p0048 :=
    @g_n_3bitr4ri
      (.all x (syn_wb (.classMem (.cv x) A)
          (syn_wo (syn_wrex y B (.classEq (.cv x) (syn_cphi (.cv y)))) (syn_wrex y C
              (.classEq (.cv x) (syn_cun (syn_cphi (.cv y)) (syn_csn (syn_c0c))))))))
      (.neg (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classEq A (syn_cop B C))
      (.classMem (syn_copk (syn_csn (syn_csn A)) (syn_copk B C)) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k (syn_cun
                  (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))) (syn_cins2k
                    (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0045 p0046 p0047
  exact p0048


end NFChoice.DirectNominalPrf.WPPReplay
