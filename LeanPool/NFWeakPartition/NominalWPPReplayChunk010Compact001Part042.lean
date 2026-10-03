/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block013

/-! NF weak partition development: NominalWPPReplayChunk010Compact001Part042. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_setconslem2 (x : Var) (A : Class) (B : Class) (dv_A_x : x ∉ A.fv)
    (dv_B_x : x ∉ B.fv) (hyp_setconslem1_1 : Nominal.NPrf (.classMem A (syn_cvv)))
    (hyp_setconslem1_2 : Nominal.NPrf (.classMem B (syn_cvv))) :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn A) B) (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                              (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                              (syn_cssetk))
                            (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_wrex x B (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ A.fv ∪ B.fv
  let t : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_t_ne_x : t ≠ x := by
    intro h
    exact
      fresh_t
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_t : x ≠ t := Ne.symm fresh_t_ne_x
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_t_not_B : t ∉ B.fv := by
    intro h
    exact fresh_t (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_ne_x : y ≠ x := by
    intro h
    exact
      fresh_y
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (Finset.mem_union_right _ (h)))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_t_ne_y : t ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_t : y ≠ t := Ne.symm fresh_t_ne_y
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have dv_cache_0001 : x ∉ ((Class.cv t)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_t, not_false_eq_true])
  have dv_cache_0002 :
    x ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv :=
    by
    clear dv_cache_0001
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_t, dv_A_x, dv_B_x, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0003 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_x,
          not_false_eq_true])
  have dv_cache_0004 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, fresh_t_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0005 :
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
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
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
  have dv_cache_0006 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_c1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0007 : t ∉ ((syn_copk (.cv x) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_A, or_false, not_false_eq_true])
  have dv_cache_0008 : y ∉ ((Class.cv t)).fv :=
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
          fresh_y_ne_t, not_false_eq_true])
  have dv_cache_0009 :
    y ∉
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      dv_cache_0006 dv_cache_0007 dv_cache_0008
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
          Finset.mem_singleton, fresh_y_ne_t, fresh_y_ne_x, fresh_y_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0010 : t ∉ ((syn_csn (syn_csn (syn_csn (.cv y))))).fv :=
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
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_y,
          not_false_eq_true])
  have dv_cache_0011 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
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
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, fresh_t_not_A,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0012 : z ∉ ((syn_csn (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_y,
          not_false_eq_true])
  have dv_cache_0013 : z ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0014 :
    z ∉
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
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
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
  have dv_cache_0015 : z ∉ ((syn_cssetk)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0017 : z ∉ ((syn_cphi (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_z_ne_x,
          not_false_eq_true])
  have dv_cache_0018 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0020 :
    t ∉
      ((syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
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
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0021 : t ∉ ((syn_copk (syn_csn A) B)).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn, Finset.mem_union,
          fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true])
  have p0000 := @g_elpw121c x (.cv t) dv_cache_0001
  have p0001 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_cin (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                    (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      p0000
  have p0002 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_cin (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                    (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      x dv_cache_0002
  have p0003 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wa (syn_wex x (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x))))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                              (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                              (syn_cssetk))
                            (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0001 p0002
  have p0004 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                              (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                              (syn_cssetk))
                            (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      t p0003
  have p0005 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
  have p0006 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      x t
  have p0007 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                              (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                              (syn_cssetk))
                            (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wex t (syn_wex x (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                                (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                                (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      p0004 p0005 p0006
  have p0008 := @g_snex (syn_csn (syn_csn (.cv x)))
  have p0009 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)
  have p0010 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
      (syn_copk (.cv t) (syn_copk (syn_csn A) B))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
      (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
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
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0009
  have p0011 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B)) (syn_cin (syn_cins2k (syn_cssetk))
          (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                    (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
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
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      t (syn_csn (syn_csn (syn_csn (.cv x)))) dv_cache_0003 dv_cache_0004 p0008 p0010
  have p0012 :=
    @g_elin (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
      (syn_cins2k (syn_cssetk))
      (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                              (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                    (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
  have p0013 := @g_snex (.cv x)
  have p0014 := @g_snex A
  have p0015 :=
    @g_otkelins2k (syn_csn (.cv x)) (syn_csn A) B (syn_cssetk) p0013 p0014
      hyp_setconslem1_2
  have p0016 := @g_vex x
  have p0017 := @g_elssetk (.cv x) B p0016 hyp_setconslem1_2
  have p0018 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv x)) B) (syn_cssetk)) (.classMem (.cv x) B) p0015
      p0017
  have p0019 :=
    @g_otkelins3k (syn_csn (.cv x)) (syn_csn A) B
      (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                              (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
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
      p0013 p0014 hyp_setconslem1_2
  have p0020 :=
    @g_opksnelsik (.cv x) A
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                              (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
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
      p0016 hyp_setconslem1_1
  have p0021 := @g_opkex (.cv x) A
  have p0022 :=
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
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (.cv x) A) dv_cache_0005 dv_cache_0006
      dv_cache_0007 p0021
  have p0023 := @g_elpw121c y (.cv t) dv_cache_0008
  have p0024 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
      (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A)) (syn_csymdif (syn_cins2k (syn_cssetk))
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
      p0023
  have p0025 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A)) (syn_csymdif (syn_cins2k (syn_cssetk))
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
      y dv_cache_0009
  have p0026 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      (syn_wa (syn_wex y (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y))))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      p0024 p0025
  have p0027 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      t p0026
  have p0028 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
  have p0029 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      y t
  have p0030 :=
    @g_n_3bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_c1c))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      (syn_wex t (syn_wex y (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      p0027 p0028 p0029
  have p0031 :=
    @g_bitri
      (.classMem (syn_copk (.cv x) A) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
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
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      p0022 p0030
  have p0032 := @g_snex (syn_csn (syn_csn (.cv y)))
  have p0033 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A)
  have p0034 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
      (syn_copk (.cv t) (syn_copk (.cv x) A))
      (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
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
      p0033
  have p0035 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A)) (syn_csymdif (syn_cins2k (syn_cssetk))
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
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
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
      t (syn_csn (syn_csn (syn_csn (.cv y)))) dv_cache_0010 dv_cache_0011 p0032 p0034
  have p0036 :=
    @g_elsymdif (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
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
  have p0037 := @g_snex (.cv y)
  have p0038 :=
    @g_otkelins2k (syn_csn (.cv y)) (.cv x) A (syn_cssetk) p0037 p0016 hyp_setconslem1_1
  have p0039 := @g_vex y
  have p0040 := @g_elssetk (.cv y) A p0039 hyp_setconslem1_1
  have p0041 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
        (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv y)) A) (syn_cssetk)) (.classMem (.cv y) A) p0038
      p0040
  have p0042 :=
    @g_otkelins3k (syn_csn (.cv y)) (.cv x) A
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
      p0037 p0016 hyp_setconslem1_1
  have p0043 := @g_vex z
  have p0044 := @g_elssetk (.cv y) (.cv z) p0039 p0043
  have p0045 :=
    @g_opkelimagek (.cv x) (.cv z)
      (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
      p0016 p0043
  have p0046 :=
    @g_opkelcnvk (.cv z) (.cv x)
      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))
      p0043 p0016
  have p0047 := @g_dfphi2 (.cv x)
  have p0048 :=
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
      (.cv z) p0047
  have p0049 :=
    @g_n_3bitr4i
      (.classMem (syn_copk (.cv x) (.cv z)) (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
      (.classEq (.cv z) (syn_cimak (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                    (syn_cins3k (syn_ccompl (syn_cimak
                          (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                          (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
            (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))) (.cv x)))
      (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      (.classEq (.cv z) (syn_cphi (.cv x))) p0045 p0046 p0048
  have p0050_e00_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv y)) (.cv z)) (syn_cssetk)) (.objMem y z)) :=
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
      p0044
  have p0050 :=
    @g_anbi12i (.classMem (syn_copk (syn_csn (.cv y)) (.cv z)) (syn_cssetk)) (.objMem y z)
      (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      (.classEq (.cv z) (syn_cphi (.cv x))) p0050_e00_recanon p0049
  have p0051 := @g_ancom (.objMem y z) (.classEq (.cv z) (syn_cphi (.cv x)))
  have p0052 :=
    @g_bitri
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) (.cv z)) (syn_cssetk))
        (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      (syn_wa (.objMem y z) (.classEq (.cv z) (syn_cphi (.cv x))))
      (syn_wa (.classEq (.cv z) (syn_cphi (.cv x))) (.objMem y z)) p0050 p0051
  have p0053 :=
    @g_exbii
      (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) (.cv z)) (syn_cssetk))
        (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                              (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))
      (syn_wa (.classEq (.cv z) (syn_cphi (.cv x))) (.objMem y z)) z p0052
  have p0054 :=
    @g_opkelcok z (syn_csn (.cv y)) (.cv x)
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
      (syn_cssetk) dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 p0037 p0016
  have p0055 := @g_phiex (.cv x) p0016
  have p0056 := @g_clel3 z (.cv y) (syn_cphi (.cv x)) dv_cache_0016 dv_cache_0017 p0055
  have p0057_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (.cv y) (syn_cphi (.cv x)))
        (syn_wex z (syn_wa (.classEq (.cv z) (syn_cphi (.cv x))) (.objMem y z)))) :=
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
      p0056
  have p0057 :=
    @g_n_3bitr4i
      (syn_wex z (syn_wa (.classMem (syn_copk (syn_csn (.cv y)) (.cv z)) (syn_cssetk))
          (.classMem (syn_copk (.cv z) (.cv x)) (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      (syn_wex z (syn_wa (.classEq (.cv z) (syn_cphi (.cv x))) (.objMem y z)))
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_ccomk (syn_ccnvk (syn_cimagek
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
      (.classMem (.cv y) (syn_cphi (.cv x))) p0053 p0054 p0057_e02_recanon
  have p0058 :=
    @g_opkelxpk (syn_csn (.cv y)) (.cv x) (syn_csn (syn_csn (syn_c0c))) (syn_cvv) p0037
      p0016
  have p0059 :=
    @g_mpbiran2
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))
      (.classMem (syn_csn (.cv y)) (syn_csn (syn_csn (syn_c0c))))
      (.classMem (.cv x) (syn_cvv)) p0016 p0058
  have p0060 := @g_sneqb (.cv y) (syn_c0c) p0039
  have p0061 := @g_elsnc (syn_csn (.cv y)) (syn_csn (syn_c0c)) p0037
  have p0062 := @g_elsnc (.cv y) (syn_c0c) p0039
  have p0063 :=
    @g_n_3bitr4i (.classEq (syn_csn (.cv y)) (syn_csn (syn_c0c)))
      (.classEq (.cv y) (syn_c0c))
      (.classMem (syn_csn (.cv y)) (syn_csn (syn_csn (syn_c0c))))
      (.classMem (.cv y) (syn_csn (syn_c0c))) p0060 p0061 p0062
  have p0064 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))
      (.classMem (syn_csn (.cv y)) (syn_csn (syn_csn (syn_c0c))))
      (.classMem (.cv y) (syn_csn (syn_c0c))) p0059 p0063
  have p0065 :=
    @g_orbi12i
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_ccomk (syn_ccnvk (syn_cimagek
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
      (.classMem (.cv y) (syn_cphi (.cv x)))
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))
      (.classMem (.cv y) (syn_csn (syn_c0c))) p0057 p0064
  have p0066 :=
    @g_elun (syn_copk (syn_csn (.cv y)) (.cv x))
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
  have p0067 := @g_elun (.cv y) (syn_cphi (.cv x)) (syn_csn (syn_c0c))
  have p0068 :=
    @g_n_3bitr4i
      (syn_wo (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_ccomk (syn_ccnvk (syn_cimagek
                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                  (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
                          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
            (syn_cssetk))) (.classMem (syn_copk (syn_csn (.cv y)) (.cv x))
          (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv))))
      (syn_wo (.classMem (.cv y) (syn_cphi (.cv x))) (.classMem (.cv y) (syn_csn (syn_c0c))))
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cun (syn_ccomk (syn_ccnvk
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
      (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0065 p0066
      p0067
  have p0069 :=
    @g_bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
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
      (.classMem (syn_copk (syn_csn (.cv y)) (.cv x)) (syn_cun (syn_ccomk (syn_ccnvk
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
      (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0042 p0068
  have p0070 :=
    @g_bibi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
        (syn_cins2k (syn_cssetk)))
      (.classMem (.cv y) A)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
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
      (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0041 p0069
  have p0071 :=
    @g_xchbinx
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
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
      (syn_wb (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
          (syn_cins2k (syn_cssetk)))
        (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
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
      (syn_wb (.classMem (.cv y) A)
        (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))
      p0036 p0070
  have p0072 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv y)))) (syn_copk (.cv x) A))
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
      (.neg (syn_wb (.classMem (.cv y) A)
          (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      p0035 p0071
  have p0073 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      (.neg (syn_wb (.classMem (.cv y) A)
          (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      y p0072
  have p0074 :=
    @g_exnal
      (syn_wb (.classMem (.cv y) A)
        (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))
      y
  have p0075 :=
    @g_n_3bitri
      (.classMem (syn_copk (.cv x) A) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
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
      (syn_wex y (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv y)))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) A))
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
      (syn_wex y (.neg (syn_wb (.classMem (.cv y) A)
            (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))))
      (.neg (.all y (syn_wb (.classMem (.cv y) A)
            (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))))
      p0031 p0073 p0074
  have p0076 :=
    @g_con2bii
      (.classMem (syn_copk (.cv x) A) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
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
      (.all y (syn_wb (.classMem (.cv y) A)
          (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      p0075
  have p0077 :=
    @g_dfcleq y A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))) dv_cache_0018
      dv_cache_0019
  have p0078 :=
    @g_elcompl (syn_copk (.cv x) A)
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
      p0021
  have p0079 :=
    @g_n_3bitr4ri
      (.all y (syn_wb (.classMem (.cv y) A)
          (.classMem (.cv y) (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      (.neg (.classMem (syn_copk (.cv x) A) (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
              (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                            (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
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
      (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))
      (.classMem (syn_copk (.cv x) A) (syn_ccompl (syn_cimak
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
      p0076 p0077 p0078
  have p0080 :=
    @g_n_3bitri
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (syn_csn (.cv x)) (syn_csn A)) (syn_csik (syn_ccompl (syn_cimak
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
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (.classMem (syn_copk (.cv x) A) (syn_ccompl (syn_cimak
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
      (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0019 p0020 p0079
  have p0081 :=
    @g_anbi12i
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_cins2k (syn_cssetk)))
      (.classMem (.cv x) B)
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_cins3k (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                  (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))) p0018 p0080
  have p0082 :=
    @g_n_3bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                              (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                              (syn_cssetk))
                            (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
        (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
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
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B))
          (syn_cins2k (syn_cssetk))) (.classMem
          (syn_copk (syn_csn (syn_csn (syn_csn (.cv x)))) (syn_copk (syn_csn A) B)) (syn_cins3k
            (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
                      (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                                    (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
                        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (.classMem (.cv x) B)
        (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))
      p0011 p0012 p0081
  have p0083 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
          (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                              (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                              (syn_cssetk))
                            (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wa (.classMem (.cv x) B)
        (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c)))))
      x p0082
  have p0084 :=
    @g_bitri
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex x (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (.cv x)))))
            (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                                (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))
      (syn_wex x (syn_wa (.classMem (.cv x) B)
          (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      p0007 p0083
  have p0085 := @g_opkex (syn_csn A) B
  have p0086 :=
    @g_elimak t
      (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
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
                (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) (syn_copk (syn_csn A) B) dv_cache_0020 dv_cache_0006
      dv_cache_0021 p0085
  have p0087 :=
    (Nominal.biimpRefl
      (syn_wrex x B (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
  have p0088 :=
    @g_n_3bitr4i
      (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (syn_csn A) B))
          (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex x (syn_wa (.classMem (.cv x) B)
          (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))))
      (.classMem (syn_copk (syn_csn A) B) (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
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
      (syn_wrex x B (.classEq A (syn_cun (syn_cphi (.cv x)) (syn_csn (syn_c0c))))) p0084
      p0086 p0087
  exact p0088


end NFChoice.DirectNominalPrf.WPPReplay
