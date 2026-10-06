/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk010Compact001Part046

/-! NF weak partition development: NominalWPPReplayChunk010Compact001Part047. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_setconslem7`. -/
@[expose]
noncomputable def gSetconslem7 (A : Class) (B : Class) (C : Class)
    (hyp_setconslem7_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_setconslem7_2 : Nominal.NPrf (.classMem B (synCvv)))
    (hyp_setconslem7_3 : Nominal.NPrf (.classMem C (synCvv))) :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (synCsn C)) (synCopk A B)) (synCcompl (synCimak
              (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                    (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                  (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
        (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (.classEq A (synCop B C))) :=
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
      ((synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
              (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                        (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c)))))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
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
  have dv_cache_0002 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
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
  have dv_cache_0003 : t ∉ ((synCopk (synCsn (synCsn C)) (synCopk A B))).fv :=
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
          fresh_t_not_C, fresh_t_not_A, fresh_t_not_B, or_false, not_false_eq_true])
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
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
          Finset.mem_singleton, fresh_x_ne_t, fresh_x_not_C, fresh_x_not_A, fresh_x_not_B,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 :
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (synCopk (synCsn (synCsn C)) (synCopk A B)))
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
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
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_not_C, fresh_t_not_A, fresh_t_not_B,
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
  have p0000 := @gOpkex (synCsn (synCsn C)) (synCopk A B)
  have p0001 :=
    @gElimak t
      (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
              (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                          (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
          (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                    (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                  (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synCopk (synCsn (synCsn C)) (synCopk A B)) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0000
  have p0002 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))))))
  have p0003 := @gElpw141c x (.cv t) dv_cache_0004
  have p0004 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
        (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
              (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                        (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      p0003
  have p0005 :=
    @gN1941v
      (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
        (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
              (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                        (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      x dv_cache_0005
  have p0006 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWa (synWex x
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWex x (synWa
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
            (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                    (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                  (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      p0004 p0005
  have p0007 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWex x (synWa
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
            (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                    (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                  (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      t p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      x t
  have p0009 :=
    @gBitr4i
      (synWex t
        (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
            (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                    (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                  (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      (synWex t (synWex x (synWa
            (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
              (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                    (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                  (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
        (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))))))))))
      (synWex x (synWex t (synWa
            (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
              (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                    (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                  (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
        (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))))))))))
      p0007 p0008
  have p0010 :=
    @gBitri
      (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWex t
        (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
            (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                    (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                  (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      (synWex x (synWex t (synWa
            (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
              (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                    (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                  (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
        (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))))))))))
      p0002 p0009
  have p0011 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn C)) (synCopk A B)) (synCimak
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
        (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWex x (synWex t (synWa
            (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
              (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                    (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                  (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
        (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))))))))))
      p0001 p0010
  have p0012 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv x)))))
  have p0013 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (synCopk (synCsn (synCsn C)) (synCopk A B))
  have p0014 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
      (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
        (synCopk (synCsn (synCsn C)) (synCopk A B)))
      (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
              (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                          (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
          (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                    (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                  (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      p0013
  have p0015 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
        (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
              (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                        (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B)))
        (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
              (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                        (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      t (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))) dv_cache_0006
      dv_cache_0007 p0012 p0014
  have p0016 :=
    @gElsymdif
      (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
        (synCopk (synCsn (synCsn C)) (synCopk A B)))
      (synCins2k (synCins3k (synCssetk)))
      (synCun (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                    (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                  (synCimak (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
        (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                  (synCins3k (synCsik (synCcompl (synCimak
                          (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk
                                  (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c))))))))
  have p0017 := @gSnex (synCsn (synCsn (.cv x)))
  have p0018 := @gSnex (synCsn C)
  have p0019 := @gOpkex A B
  have p0020 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn C))
      (synCopk A B) (synCins3k (synCssetk)) p0017 p0018 p0019
  have p0021 := @gSnex (.cv x)
  have p0022 :=
    @gOtkelins3k (synCsn (.cv x)) A B (synCssetk) p0021 hyp_setconslem7_1
      hyp_setconslem7_2
  have p0023 := @gVex x
  have p0024 := @gElssetk (.cv x) A p0023 hyp_setconslem7_1
  have p0025 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCins3k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) A) (synCssetk)) (.classMem (.cv x) A) p0022
      p0024
  have p0026 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B)))
        (synCins2k (synCins3k (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B))
        (synCins3k (synCssetk)))
      (.classMem (.cv x) A) p0020 p0025
  have p0027 :=
    @gElun
      (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
        (synCopk (synCsn (synCsn C)) (synCopk A B)))
      (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                    (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                (synCimak (synCin (synCins3k (synCssetk))
                                    (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
      (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                  (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                          (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
                                      (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                                (synCssetk))
                              (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))
  have p0028 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn C))
      (synCopk A B)
      (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      p0017 p0018 p0019
  have p0029 :=
    @gOtkelins2k (synCsn (.cv x)) A B
      (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek
                    (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      p0021 hyp_setconslem7_1 hyp_setconslem7_2
  have p0030 :=
    @gSetconslem1 y (.cv x) B dv_cache_0008 dv_cache_0009 p0023 hyp_setconslem7_2
  have p0031 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B)) (synCins2k
          (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
      (.classMem (synCopk (synCsn (.cv x)) B) (synCcomk (synCssetk) (synCsik (synCcnvk
              (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                            (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                  (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                          (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) p0029 p0030
  have p0032 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B))) (synCins2k (synCins2k
            (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                    (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCopk A B)) (synCins2k
          (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
      (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) p0028 p0031
  have p0033 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn C))
      (synCopk A B)
      (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                  (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                          (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                              (synCssetk))
                            (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
      p0017 p0018 p0019
  have p0034 := @gSnex (synCsn (.cv x))
  have p0035 := @gSnex C
  have p0036 :=
    @gOpksnelsik (synCsn (synCsn (.cv x))) (synCsn C)
      (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                  (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                          (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                                      (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                            (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))
      p0034 p0035
  have p0037 :=
    @gOpksnelsik (synCsn (.cv x)) C
      (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk
                          (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                      (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))
      p0021 hyp_setconslem7_3
  have p0038 :=
    @gSetconslem2 y (.cv x) C dv_cache_0008 dv_cache_0010 p0023 hyp_setconslem7_3
  have p0039 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn C)) (synCsik (synCimak
            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk
                              (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                              (synCssetk))
                            (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
      (.classMem (synCopk (synCsn (.cv x)) C) (synCimak (synCin (synCins2k (synCssetk))
            (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                      (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                            (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))
      (synWrex y C (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      p0037 p0038
  have p0040 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn C)))
        (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                    (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                            (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                                        (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                                (synCssetk))
                              (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn C)) (synCsik (synCimak
            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
                      (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk
                              (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                              (synCssetk))
                            (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
      (synWrex y C (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      p0036 p0039
  have p0041 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B))) (synCins3k (synCsik (synCsik
              (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                        (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn C)))
        (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                    (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                            (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                                        (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                                (synCssetk))
                              (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))
      (synWrex y C (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      p0033 p0040
  have p0042 :=
    @gOrbi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B))) (synCins2k (synCins2k
            (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                    (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
      (synWrex y B (.classEq (.cv x) (synCphi (.cv y))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B))) (synCins3k (synCsik (synCsik
              (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                        (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWrex y C (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      p0032 p0041
  have p0043 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B))) (synCun (synCins2k (synCins2k
              (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                          (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
          (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                    (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                  (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWo (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (synCopk (synCsn (synCsn C)) (synCopk A B))) (synCins2k (synCins2k
              (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                          (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk)
                          (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (synCopk (synCsn (synCsn C)) (synCopk A B))) (synCins3k (synCsik (synCsik
                (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                          (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                  (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y C
          (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      p0027 p0042
  have p0044 :=
    @gBibi12i
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B)))
        (synCins2k (synCins3k (synCssetk))))
      (.classMem (.cv x) A)
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B))) (synCun (synCins2k (synCins2k
              (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                          (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
          (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                    (synCins3k (synCsik (synCcompl (synCimak
                            (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                  (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))))
      (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y C
          (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      p0026 p0043
  have p0045 :=
    @gNotbii
      (synWb (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (synCopk (synCsn (synCsn C)) (synCopk A B)))
          (synCins2k (synCins3k (synCssetk)))) (.classMem
          (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
            (synCopk (synCsn (synCsn C)) (synCopk A B))) (synCun (synCins2k (synCins2k
                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
              (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                        (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (synWb (.classMem (.cv x) A) (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y))))
          (synWrex y C (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      p0044
  have p0046 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B)))
        (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
              (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                        (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (.neg (synWb (.classMem
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
              (synCopk (synCsn (synCsn C)) (synCopk A B)))
            (synCins2k (synCins3k (synCssetk)))) (.classMem
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
              (synCopk (synCsn (synCsn C)) (synCopk A B))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      (.neg (synWb (.classMem (.cv x) A)
          (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y C
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      p0016 p0045
  have p0047 :=
    @gBitri
      (synWex t (synWa
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
            (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                    (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                  (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
          (synCopk (synCsn (synCsn C)) (synCopk A B)))
        (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                            (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
              (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                        (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      (.neg (synWb (.classMem (.cv x) A)
          (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y C
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      p0015 p0046
  have p0048 :=
    @gExbii
      (synWex t (synWa
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
            (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                    (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                  (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      (.neg (synWb (.classMem (.cv x) A)
          (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y C
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      x p0047
  have p0049 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn C)) (synCopk A B)) (synCimak
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWex x (synWex t (synWa
            (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
            (.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn C)) (synCopk A B)))
              (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                    (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                  (synCins3k (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk))
                            (synCins3k (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
        (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                    (synCpw1 (synCpw1 (synC1c))))))))
                          (synCpw1 (synCpw1 (synC1c)))))))))))))
      (synWex x (.neg (synWb (.classMem (.cv x) A)
            (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y C
                (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))))
      p0011 p0048
  have p0050 :=
    @gExnal
      (synWb (.classMem (.cv x) A) (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y))))
          (synWrex y C (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      x
  have p0051 :=
    @gBitri
      (.classMem (synCopk (synCsn (synCsn C)) (synCopk A B)) (synCimak
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synWex x (.neg (synWb (.classMem (.cv x) A)
            (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y C
                (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))))
      (.neg (.all x (synWb (.classMem (.cv x) A)
            (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y C
                (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))))
      p0049 p0050
  have p0052 :=
    @gCon2bii
      (.classMem (synCopk (synCsn (synCsn C)) (synCopk A B)) (synCimak
          (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                          (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c)))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (.all x (synWb (.classMem (.cv x) A)
          (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y C
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      p0051
  have p0053 :=
    @gEqop x y A B C dv_cache_0011 dv_cache_0012 dv_cache_0009 dv_cache_0013
      dv_cache_0010 dv_cache_0014 dv_cache_0015
  have p0054 :=
    @gElcompl (synCopk (synCsn (synCsn C)) (synCopk A B))
      (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
              (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                          (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                      (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
              (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                        (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c)))))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0000
  have p0055 :=
    @gN3bitr4ri
      (.all x (synWb (.classMem (.cv x) A)
          (synWo (synWrex y B (.classEq (.cv x) (synCphi (.cv y)))) (synWrex y C
              (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))))
      (.neg (.classMem (synCopk (synCsn (synCsn C)) (synCopk A B)) (synCimak
            (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                    (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                  (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (.classEq A (synCop B C))
      (.classMem (synCopk (synCsn (synCsn C)) (synCopk A B)) (synCcompl (synCimak
            (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k (synCins2k
                    (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))) (synCins3k
                  (synCsik (synCsik (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                            (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c))))))))
                        (synCpw1 (synCpw1 (synC1c)))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0052 p0053 p0054
  exact p0055


end NFChoice.DirectNominalPrf.WPPReplay
