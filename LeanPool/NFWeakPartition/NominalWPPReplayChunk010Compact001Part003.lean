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

/-- Checked nominal proof certificate identified upstream as `g_evenodddisjlem1`. -/
@[expose]
noncomputable def gEvenodddisjlem1 (j : Var) (n : Var) (dv_j_n : j ≠ n) :
    Nominal.NPrf
      (.classMem (.cab j (.imp (synWne (synCplc (.cv j) (.cv j)) (synC0))
            (synWral n (synCnnc)
              (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
                (synWne (synCplc (.cv j) (.cv j))
                  (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))) (synCvv)) :=
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
      ((synCin (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                  (synCimak (synCin (synCins2k (synCssetk)) (synCimak
                        (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k
                              (synCsik (synCsik (synCsik (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak
                                (synCsymdif (synCins2k
                                    (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
                                    (synCins3k (synCsik (synCsik
        (synCsik (synCsik (synCsik (synCssetk))))))) (synCins2k (synCins3k
                                        (synCsik (synCsik (synCsik (synCssetk))))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))
          (synCxpk (synCun (synCsn (synC0)) (synCcompl (synCimak (synCimak (synCin
                      (synCins3k (synCimak (synCin (synCins2k (synCcompl (synCimak
                                  (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                                        (synCin (synCins2k (synCssetk)) (synCimak (synCin
        (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl (synCins3k (synCcnvk
        (synCsik (synCsik (synCsik (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak
        (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
        (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k
        (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                        (synCpw1 (synCpw1 (synC1c))))))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCins3k (synCimagek
                                (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c))))
                      (synCins2k
                        (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv)))))
                    (synCpw1 (synC1c))) (synCnnc)))) (synCvv)))).fv :=
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
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCimak
                  (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k (synCsik
                          (synCsik (synCsik (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak
                          (synCsymdif
                            (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
                            (synCun (synCins3k (synCsik (synCsik
                                    (synCsik (synCsik (synCsik (synCssetk))))))) (synCins2k
                                (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))))).fv :=
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
  have dv_cache_0004 : t ∉ ((synCpw1 (synCpw1 (synC1c)))).fv :=
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
  have dv_cache_0005 : t ∉ ((synCopk (.cv x) (.cv j))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv j)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCimak
                    (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k
                          (synCsik (synCsik (synCsik (synCcompl (synCimak
                                    (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak
                            (synCsymdif (synCins2k
                                (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
                                (synCins3k (synCsik (synCsik
                                      (synCsik (synCsik (synCsik (synCssetk)))))))
                                (synCins2k (synCins3k
                                    (synCsik (synCsik (synCsik (synCssetk)))))))) (synCpw1
                              (synCpw1 (synCpw1 (synCpw1
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have dv_cache_0008 : t ∉ ((synCsn (synCsn (synCsn (.cv y))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv j)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCimak
                    (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k
                          (synCsik (synCsik (synCsik (synCcompl (synCimak
                                    (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak
                            (synCsymdif (synCins2k
                                (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
                                (synCins3k (synCsik (synCsik
                                      (synCsik (synCsik (synCsik (synCssetk)))))))
                                (synCins2k (synCins3k
                                    (synCsik (synCsik (synCsik (synCssetk)))))))) (synCpw1
                              (synCpw1 (synCpw1 (synCpw1
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
      ((synCin (synCins2k (synCssetk)) (synCimak
            (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k (synCsik
                    (synCsik (synCsik (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
                      (synCun (synCins3k (synCsik
                            (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
                        (synCins2k
                          (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))))
                    (synCpw1 (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have dv_cache_0011 : t ∉ ((synCopk (synCsn (.cv y)) (.cv j))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv y)) (.cv j)))
          (synCin (synCins2k (synCssetk)) (synCimak
              (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k (synCsik
                      (synCsik (synCsik (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak
                      (synCsymdif
                        (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
                          (synCins3k (synCsik
                              (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
                          (synCins2k
                            (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))))
                      (synCpw1 (synCpw1 (synCpw1
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
  have dv_cache_0014 : t ∉ ((synCsn (synCsn (synCsn (.cv b))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
            (synCopk (synCsn (.cv y)) (.cv j))) (synCin (synCins2k (synCssetk)) (synCimak
              (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k (synCsik
                      (synCsik (synCsik (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak
                      (synCsymdif
                        (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
                          (synCins3k (synCsik
                              (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
                          (synCins2k
                            (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))))
                      (synCpw1 (synCpw1 (synCpw1
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
      ((synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k (synCsik (synCsik
                  (synCsik (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
                  (synCun (synCins3k
                      (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
                    (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))))
                (synCpw1 (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))).fv :=
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
  have dv_cache_0017 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
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
      ((synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCopk (synCsn (.cv y)) (.cv j)))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (synCsn (.cv b))))
              (synCopk (synCsn (.cv y)) (.cv j))))
          (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k (synCsik
                  (synCsik (synCsik (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
                    (synCun (synCins3k (synCsik
                          (synCsik (synCsik (synCsik (synCsik (synCssetk))))))) (synCins2k
                        (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))))) (synCpw1
                    (synCpw1 (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))).fv :=
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
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))
            (synCopk (synCsn (synCsn (synCsn (.cv b))))
              (synCopk (synCsn (.cv y)) (.cv j))))
          (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k (synCsik
                  (synCsik (synCsik (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
                    (synCun (synCins3k (synCsik
                          (synCsik (synCsik (synCsik (synCsik (synCssetk))))))) (synCins2k
                        (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))))) (synCpw1
                    (synCpw1 (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))).fv :=
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
      ((synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
            (synCins3k (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
            (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))))).fv :=
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
      ((synCpw1 (synCpw1
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
      ((synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))
          (synCopk (synCsn (synCsn (synCsn (.cv b))))
            (synCopk (synCsn (.cv y)) (.cv j))))).fv :=
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
      ((Wff.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))
              (synCopk (synCsn (synCsn (synCsn (.cv b))))
                (synCopk (synCsn (.cv y)) (.cv j)))))
          (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
              (synCins3k (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
              (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))))))).fv :=
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
      ((synCsn (synCsn
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))
              (synCopk (synCsn (synCsn (synCsn (.cv b))))
                (synCopk (synCsn (.cv y)) (.cv j)))))
          (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
              (synCins3k (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
              (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))))))).fv :=
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
  have dv_cache_0031 : x ∉ ((synCun (.cv a) (.cv b))).fv :=
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
      ((synCimak (synCin (synCins3k (synCimak (synCin (synCins2k (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                              (synCin (synCins2k (synCssetk)) (synCimak
                                  (synCin (synCins2k (synCins2k (synCssetk))) (synCin
                                      (synCcompl (synCins3k (synCcnvk (synCsik (synCsik
        (synCsik (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak (synCsymdif (synCins2k
        (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun (synCins2k (synCins3k
        (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k (synCsik (synCsik
        (synCsik (synCsik (synCsik (synCssetk))))))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCins3k (synCimagek (synCimak
                        (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c))))
            (synCins2k (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv)))))
          (synCpw1 (synC1c)))).fv :=
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
  have dv_cache_0041 : n ∉ ((synCnnc)).fv :=
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
      ((synCin (synCins3k (synCimak (synCin (synCins2k (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                            (synCin (synCins2k (synCssetk)) (synCimak
                                (synCin (synCins2k (synCins2k (synCssetk))) (synCin
                                    (synCcompl (synCins3k (synCcnvk (synCsik (synCsik
        (synCsik (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak (synCsymdif (synCins2k
        (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun (synCins2k (synCins3k
        (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k (synCsik (synCsik
        (synCsik (synCsik (synCsik (synCssetk))))))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCins3k (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))) (synCins2k
            (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv)))))).fv :=
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
  have dv_cache_0044 : t ∉ ((synCpw1 (synC1c))).fv :=
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
  have dv_cache_0045 : t ∉ ((synCopk (.cv n) (.cv x))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv n) (.cv x))) (synCin (synCins3k
              (synCimak (synCin (synCins2k (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                              (synCin (synCins2k (synCssetk)) (synCimak
                                  (synCin (synCins2k (synCins2k (synCssetk))) (synCin
                                      (synCcompl (synCins3k (synCcnvk (synCsik (synCsik
        (synCsik (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak (synCsymdif (synCins2k
        (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun (synCins2k (synCins3k
        (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k (synCsik (synCsik
        (synCsik (synCsik (synCsik (synCssetk))))))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCins3k (synCimagek (synCimak
                        (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))) (synCins2k
              (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv))))))).fv :=
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
  have dv_cache_0047 : t ∉ ((synCsn (synCsn (.cv y)))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (.cv x))) (synCin
            (synCins3k (synCimak (synCin (synCins2k (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                              (synCin (synCins2k (synCssetk)) (synCimak
                                  (synCin (synCins2k (synCins2k (synCssetk))) (synCin
                                      (synCcompl (synCins3k (synCcnvk (synCsik (synCsik
        (synCsik (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak (synCsymdif (synCins2k
        (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun (synCins2k (synCins3k
        (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k (synCsik (synCsik
        (synCsik (synCsik (synCsik (synCssetk))))))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCins3k (synCimagek (synCimak
                        (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))) (synCins2k
              (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv))))))).fv :=
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
      ((synCin (synCins2k (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                  (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCimak
                          (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl
                                (synCins3k (synCcnvk (synCsik (synCsik (synCsik (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak (synCsymdif (synCins2k
                                      (synCins2k (synCins3k (synCsik (synCssetk)))))
                                    (synCun (synCins2k (synCins3k
        (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k (synCsik (synCsik
        (synCsik (synCsik (synCsik (synCssetk))))))))) (synCpw1 (synCpw1 (synCpw1
                                        (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))
          (synCins3k (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have dv_cache_0050 : t ∉ ((synCopk (.cv y) (.cv n))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv n))) (synCin (synCins2k
              (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk)) (synCins2k
                      (synCimak (synCin (synCins2k (synCssetk)) (synCimak
                            (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl
                                  (synCins3k (synCcnvk (synCsik (synCsik (synCsik
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak (synCsymdif (synCins2k
                                        (synCins2k (synCins3k (synCsik (synCssetk)))))
                                      (synCun (synCins2k (synCins3k (synCsik
        (synCsik (synCsik (synCssetk)))))) (synCins3k (synCsik (synCsik (synCsik
        (synCsik (synCsik (synCssetk))))))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))
            (synCins3k (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
  have dv_cache_0052 : t ∉ ((synCsn (synCsn (.cv x)))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv n))) (synCin
            (synCins2k (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCimak
                            (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl
                                  (synCins3k (synCcnvk (synCsik (synCsik (synCsik
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak (synCsymdif (synCins2k
                                        (synCins2k (synCins3k (synCsik (synCssetk)))))
                                      (synCun (synCins2k (synCins3k (synCsik
        (synCsik (synCsik (synCssetk)))))) (synCins3k (synCsik (synCsik (synCsik
        (synCsik (synCsik (synCssetk))))))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c))))))
            (synCins3k (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
      ((synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
              (synCin (synCins2k (synCssetk)) (synCimak
                  (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl
                        (synCins3k (synCcnvk (synCsik (synCsik (synCsik (synCimak
                                    (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl
                        (synCimak (synCsymdif
                            (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
                            (synCun (synCins2k (synCins3k
                                  (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k
                                (synCsik (synCsik
                                    (synCsik (synCsik (synCsik (synCssetk))))))))) (synCpw1
                            (synCpw1 (synCpw1 (synCpw1
                                  (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))))).fv :=
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
  have dv_cache_0055 : t ∉ ((synCopk (.cv x) (.cv n))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv n)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCimak
                    (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl
                          (synCins3k (synCcnvk (synCsik (synCsik (synCsik (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl
                          (synCimak (synCsymdif (synCins2k
                                (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
                                (synCins2k (synCins3k
                                    (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k
                                  (synCsik (synCsik
                                      (synCsik (synCsik (synCsik (synCssetk)))))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv n)))
          (synCsymdif (synCins3k (synCssetk)) (synCins2k (synCimak
                (synCin (synCins2k (synCssetk)) (synCimak
                    (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl
                          (synCins3k (synCcnvk (synCsik (synCsik (synCsik (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl
                          (synCimak (synCsymdif (synCins2k
                                (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
                                (synCins2k (synCins3k
                                    (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k
                                  (synCsik (synCsik
                                      (synCsik (synCsik (synCsik (synCssetk)))))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1
                                    (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
      ((synCin (synCins2k (synCssetk)) (synCimak
            (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl (synCins3k
                    (synCcnvk (synCsik (synCsik (synCsik (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
                      (synCun (synCins2k
                          (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
                        (synCins3k (synCsik
                            (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))))
                    (synCpw1 (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
  have dv_cache_0059 : t ∉ ((synCopk (synCsn (.cv y)) (.cv n))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (.cv y)) (.cv n)))
          (synCin (synCins2k (synCssetk)) (synCimak
              (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl (synCins3k
                      (synCcnvk (synCsik (synCsik (synCsik (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak
                      (synCsymdif
                        (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
                          (synCins2k
                            (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
                          (synCins3k (synCsik
                              (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))))
                      (synCpw1 (synCpw1 (synCpw1
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
  have dv_cache_0061 : t ∉ ((synCsn (synCsn (synCsn (.cv a))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (.cv a))))
            (synCopk (synCsn (.cv y)) (.cv n))) (synCin (synCins2k (synCssetk)) (synCimak
              (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl (synCins3k
                      (synCcnvk (synCsik (synCsik (synCsik (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak
                      (synCsymdif
                        (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
                          (synCins2k
                            (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
                          (synCins3k (synCsik
                              (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))))
                      (synCpw1 (synCpw1 (synCpw1
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
      ((synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl (synCins3k
                (synCcnvk (synCsik (synCsik (synCsik (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
                  (synCun (synCins2k
                      (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k
                      (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))))
                (synCpw1 (synCpw1 (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))).fv :=
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
      ((synCopk (synCsn (synCsn (synCsn (.cv a))))
          (synCopk (synCsn (.cv y)) (.cv n)))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (synCsn (synCsn (synCsn (.cv a))))
              (synCopk (synCsn (.cv y)) (.cv n))))
          (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl (synCins3k
                  (synCcnvk (synCsik (synCsik (synCsik (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
                    (synCun (synCins2k
                        (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k
                        (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))).fv :=
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
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))
            (synCopk (synCsn (synCsn (synCsn (.cv a))))
              (synCopk (synCsn (.cv y)) (.cv n))))
          (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl (synCins3k
                  (synCcnvk (synCsik (synCsik (synCsik (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
                    (synCun (synCins2k
                        (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k
                        (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1
                          (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))))).fv :=
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
      ((synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
          (synCun (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
            (synCins3k (synCsik
                (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))))).fv :=
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
      ((synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))
          (synCopk (synCsn (synCsn (synCsn (.cv a))))
            (synCopk (synCsn (.cv y)) (.cv n))))).fv :=
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
      ((Wff.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))
              (synCopk (synCsn (synCsn (synCsn (.cv a))))
                (synCopk (synCsn (.cv y)) (.cv n)))))
          (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
              (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
              (synCins3k (synCsik
                  (synCsik (synCsik (synCsik (synCsik (synCssetk))))))))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn
                (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))
              (synCopk (synCsn (synCsn (synCsn (.cv a))))
                (synCopk (synCsn (.cv y)) (.cv n)))))
          (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
              (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
              (synCins3k (synCsik
                  (synCsik (synCsik (synCsik (synCsik (synCssetk))))))))))).fv :=
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
  have dv_cache_0075 : x ∉ ((synCplc (.cv n) (.cv n))).fv :=
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
    x ∉ ((Wff.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))).fv :=
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
  have dv_cache_0077 : y ∉ ((synCplc (synCplc (.cv n) (.cv n)) (synC1c))).fv :=
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
      ((synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) (.neg
            (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))).fv :=
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
  have dv_cache_0079 : n ∉ ((Wff.classEq (.cv x) (synCplc (.cv j) (.cv j)))).fv :=
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
  have dv_cache_0080 : x ∉ ((synCplc (.cv j) (.cv j))).fv :=
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
      ((synWo (.classEq (synCplc (.cv j) (.cv j)) (synC0)) (synWral n (synCnnc)
            (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
              (synWne (synCplc (.cv j) (.cv j))
                (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))))).fv :=
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
      ((synCimak (synCin (synCcompl (synCimak (synCsymdif (synCins3k (synCssetk))
                  (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCimak
                          (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCins3k
                                (synCsik (synCsik (synCsik (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c))))))))) (synCcompl (synCimak (synCsymdif (synCins2k
                                      (synCins2k (synCins3k (synCsik (synCssetk)))))
                                    (synCun (synCins3k (synCsik (synCsik (synCsik
        (synCsik (synCsik (synCssetk))))))) (synCins2k (synCins3k (synCsik
        (synCsik (synCsik (synCssetk)))))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))
            (synCxpk (synCun (synCsn (synC0)) (synCcompl (synCimak (synCimak (synCin
                        (synCins3k (synCimak (synCin (synCins2k (synCcompl (synCimak
                                    (synCsymdif (synCins3k (synCssetk)) (synCins2k
                                        (synCimak (synCin (synCins2k (synCssetk)) (synCimak
        (synCin (synCins2k (synCins2k (synCssetk))) (synCin (synCcompl (synCins3k
        (synCcnvk (synCsik (synCsik (synCsik (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))))))) (synCcompl (synCimak
        (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) (synCun
        (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))) (synCins3k
        (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk))))))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c)))))) (synCpw1 (synCpw1 (synC1c)))))) (synCins3k
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synC1c)))) (synCins2k
                          (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv)))))
                      (synCpw1 (synC1c))) (synCnnc)))) (synCvv))) (synCvv))).fv :=
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
    (synWne (synCplc (.cv j) (.cv j)) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
  let syntaxFormula0001 : Wff :=
    (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) syntaxFormula0000)
  let syntaxFormula0002 : Wff := (synWral n (synCnnc) syntaxFormula0001)
  let syntaxFormula0003 : Wff :=
    (synWo (.classEq (synCplc (.cv j) (.cv j)) (synC0)) syntaxFormula0002)
  let syntaxClass0004 : Class :=
    (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0005 : Class := (synCcompl syntaxClass0004)
  let syntaxClass0006 : Class := (synCsik syntaxClass0005)
  let syntaxClass0007 : Class := (synCsik syntaxClass0006)
  let syntaxClass0008 : Class := (synCsik syntaxClass0007)
  let syntaxClass0009 : Class := (synCins3k syntaxClass0008)
  let syntaxClass0010 : Class :=
    (synCins3k (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
  let syntaxClass0011 : Class :=
    (synCun syntaxClass0010
      (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))))
  let syntaxClass0012 : Class :=
    (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) syntaxClass0011)
  let syntaxClass0013 : Class :=
    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  let syntaxClass0014 : Class := (synCimak syntaxClass0012 syntaxClass0013)
  let syntaxClass0015 : Class := (synCcompl syntaxClass0014)
  let syntaxClass0016 : Class := (synCin syntaxClass0009 syntaxClass0015)
  let syntaxClass0017 : Class :=
    (synCin (synCins2k (synCins2k (synCssetk))) syntaxClass0016)
  let syntaxClass0018 : Class :=
    (synCimak syntaxClass0017 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  let syntaxClass0019 : Class := (synCin (synCins2k (synCssetk)) syntaxClass0018)
  let syntaxClass0020 : Class :=
    (synCimak syntaxClass0019 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0021 : Class := (synCins2k syntaxClass0020)
  let syntaxClass0022 : Class := (synCsymdif (synCins3k (synCssetk)) syntaxClass0021)
  let syntaxClass0023 : Class :=
    (synCimak syntaxClass0022 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0024 : Class := (synCcompl syntaxClass0023)
  let syntaxClass0025 : Class := (synCsik syntaxClass0004)
  let syntaxClass0026 : Class := (synCsik syntaxClass0025)
  let syntaxClass0027 : Class := (synCsik syntaxClass0026)
  let syntaxClass0028 : Class := (synCcnvk syntaxClass0027)
  let syntaxClass0029 : Class := (synCins3k syntaxClass0028)
  let syntaxClass0030 : Class := (synCcompl syntaxClass0029)
  let syntaxClass0031 : Class :=
    (synCun (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
      syntaxClass0010)
  let syntaxClass0032 : Class :=
    (synCsymdif (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) syntaxClass0031)
  let syntaxClass0033 : Class := (synCimak syntaxClass0032 syntaxClass0013)
  let syntaxClass0034 : Class := (synCcompl syntaxClass0033)
  let syntaxClass0035 : Class := (synCin syntaxClass0030 syntaxClass0034)
  let syntaxClass0036 : Class :=
    (synCin (synCins2k (synCins2k (synCssetk))) syntaxClass0035)
  let syntaxClass0037 : Class :=
    (synCimak syntaxClass0036 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  let syntaxClass0038 : Class := (synCin (synCins2k (synCssetk)) syntaxClass0037)
  let syntaxClass0039 : Class :=
    (synCimak syntaxClass0038 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0040 : Class := (synCins2k syntaxClass0039)
  let syntaxClass0041 : Class := (synCsymdif (synCins3k (synCssetk)) syntaxClass0040)
  let syntaxClass0042 : Class :=
    (synCimak syntaxClass0041 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0043 : Class := (synCcompl syntaxClass0042)
  let syntaxClass0044 : Class := (synCins2k syntaxClass0043)
  let syntaxClass0045 : Class := (synCins3k syntaxClass0005)
  let syntaxClass0046 : Class :=
    (synCun (synCins2k (synCins3k (synCssetk)))
      (synCins3k (synCsik (synCsik (synCssetk)))))
  let syntaxClass0047 : Class :=
    (synCsymdif (synCins2k (synCins2k (synCssetk))) syntaxClass0046)
  let syntaxClass0048 : Class :=
    (synCimak syntaxClass0047 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  let syntaxClass0049 : Class := (synCdif syntaxClass0045 syntaxClass0048)
  let syntaxClass0050 : Class :=
    (synCimak syntaxClass0049 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0051 : Class := (synCimagek syntaxClass0050)
  let syntaxClass0052 : Class := (synCins3k syntaxClass0051)
  let syntaxClass0053 : Class := (synCin syntaxClass0044 syntaxClass0052)
  let syntaxClass0054 : Class := (synCimak syntaxClass0053 (synCpw1 (synC1c)))
  let syntaxClass0055 : Class := (synCins3k syntaxClass0054)
  let syntaxClass0056 : Class :=
    (synCin syntaxClass0055
      (synCins2k (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv)))))
  let syntaxClass0057 : Class := (synCimak syntaxClass0056 (synCpw1 (synC1c)))
  let syntaxClass0058 : Class := (synCimak syntaxClass0057 (synCnnc))
  let syntaxClass0059 : Class := (synCcompl syntaxClass0058)
  let syntaxClass0060 : Class := (synCun (synCsn (synC0)) syntaxClass0059)
  let syntaxClass0061 : Class := (synCxpk syntaxClass0060 (synCvv))
  let syntaxClass0062 : Class := (synCin syntaxClass0024 syntaxClass0061)
  let syntaxFormula0063 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv j))) syntaxClass0022)
  let syntaxFormula0064 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0063)
  let syntaxFormula0065 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))) syntaxFormula0063)
  let syntaxFormula0066 : Wff := (synWex y syntaxFormula0065)
  let syntaxFormula0067 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0063)
  let syntaxFormula0068 : Wff := (synWex t syntaxFormula0065)
  let syntaxFormula0069 : Wff := (synWex y syntaxFormula0068)
  let syntaxFormula0070 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv j)))
      syntaxClass0022)
  let syntaxFormula0071 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv j)))
      (synCins3k (synCssetk)))
  let syntaxFormula0072 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv y)) (.cv j))) syntaxClass0019)
  let syntaxFormula0073 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0072)
  let syntaxFormula0074 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b))))) syntaxFormula0072)
  let syntaxFormula0075 : Wff := (synWex b syntaxFormula0074)
  let syntaxFormula0076 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0072)
  let syntaxFormula0077 : Wff := (synWex t syntaxFormula0074)
  let syntaxFormula0078 : Wff := (synWex b syntaxFormula0077)
  let syntaxClass0079 : Class :=
    (synCopk (synCsn (synCsn (synCsn (.cv b)))) (synCopk (synCsn (.cv y)) (.cv j)))
  let syntaxFormula0080 : Wff := (.classMem syntaxClass0079 syntaxClass0019)
  let syntaxFormula0081 : Wff := (.classMem syntaxClass0079 (synCins2k (synCssetk)))
  let syntaxClass0082 : Class := (synCopk (.cv t) syntaxClass0079)
  let syntaxFormula0083 : Wff := (.classMem syntaxClass0082 syntaxClass0017)
  let syntaxFormula0084 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      syntaxFormula0083)
  let syntaxFormula0085 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))))
      syntaxFormula0083)
  let syntaxFormula0086 : Wff := (synWex a syntaxFormula0085)
  let syntaxFormula0087 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0083)
  let syntaxFormula0088 : Wff := (synWex t syntaxFormula0085)
  let syntaxFormula0089 : Wff := (synWex a syntaxFormula0088)
  let syntaxClass0090 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0079)
  let syntaxFormula0091 : Wff := (.classMem syntaxClass0090 syntaxClass0017)
  let syntaxFormula0092 : Wff :=
    (.classMem syntaxClass0090 (synCins2k (synCins2k (synCssetk))))
  let syntaxFormula0093 : Wff := (.classMem (synCopk (.cv a) (.cv b)) syntaxClass0004)
  let syntaxFormula0094 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (synCsn (.cv b))))
      syntaxClass0007)
  let syntaxFormula0095 : Wff := (.classMem syntaxClass0090 syntaxClass0009)
  let syntaxFormula0096 : Wff := (.classMem (.cv t) syntaxClass0013)
  let syntaxClass0097 : Class :=
    (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))))
  let syntaxFormula0098 : Wff := (.classEq (.cv t) syntaxClass0097)
  let syntaxFormula0099 : Wff := (synWex x syntaxFormula0098)
  let syntaxClass0100 : Class := (synCopk (.cv t) syntaxClass0090)
  let syntaxFormula0101 : Wff := (.classMem syntaxClass0100 syntaxClass0012)
  let syntaxFormula0102 : Wff := (synWa syntaxFormula0096 syntaxFormula0101)
  let syntaxFormula0103 : Wff := (synWa syntaxFormula0098 syntaxFormula0101)
  let syntaxFormula0104 : Wff := (synWex x syntaxFormula0103)
  let syntaxFormula0105 : Wff := (synWrex t syntaxClass0013 syntaxFormula0101)
  let syntaxFormula0106 : Wff := (synWex t syntaxFormula0103)
  let syntaxFormula0107 : Wff := (synWex x syntaxFormula0106)
  let syntaxClass0108 : Class := (synCopk syntaxClass0097 syntaxClass0090)
  let syntaxFormula0109 : Wff := (.classMem syntaxClass0108 syntaxClass0012)
  let syntaxFormula0110 : Wff :=
    (.classMem syntaxClass0108 (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))))
  let syntaxFormula0111 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv a))))
      (synCsik (synCsik (synCssetk))))
  let syntaxFormula0112 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
        (synCsn (synCsn (synCsn (synCsn (.cv a))))))
      (synCsik (synCsik (synCsik (synCsik (synCssetk))))))
  let syntaxClass0113 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv a)))))
  let syntaxFormula0114 : Wff :=
    (.classMem syntaxClass0113 (synCsik (synCsik (synCsik (synCssetk)))))
  let syntaxFormula0115 : Wff := (.classMem syntaxClass0108 syntaxClass0010)
  let syntaxClass0116 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv b)))))
  let syntaxFormula0117 : Wff :=
    (.classMem syntaxClass0116 (synCsik (synCsik (synCsik (synCssetk)))))
  let syntaxFormula0118 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv b))))
      (synCsik (synCsik (synCssetk))))
  let syntaxFormula0119 : Wff :=
    (.classMem syntaxClass0108
      (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))))
  let syntaxFormula0120 : Wff := (.classMem syntaxClass0108 syntaxClass0011)
  let syntaxFormula0121 : Wff := (synWb syntaxFormula0110 syntaxFormula0120)
  let syntaxFormula0122 : Wff := (.classMem syntaxClass0090 syntaxClass0014)
  let syntaxFormula0123 : Wff := (.classMem syntaxClass0090 syntaxClass0015)
  let syntaxFormula0124 : Wff := (.classMem syntaxClass0090 syntaxClass0016)
  let syntaxFormula0125 : Wff :=
    (synWa (.classEq (synCin (.cv a) (.cv b)) (synC0))
      (.classEq (.cv y) (synCun (.cv a) (.cv b))))
  let syntaxFormula0126 : Wff := (.classMem syntaxClass0079 syntaxClass0018)
  let syntaxFormula0127 : Wff := (synWrex a (.cv j) syntaxFormula0125)
  let syntaxFormula0128 : Wff :=
    (.classMem (synCopk (synCsn (.cv y)) (.cv j)) syntaxClass0020)
  let syntaxFormula0129 : Wff := (synWrex b (.cv j) syntaxFormula0127)
  let syntaxFormula0130 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv j)))
      syntaxClass0021)
  let syntaxFormula0131 : Wff := (synWrex b (.cv j) syntaxFormula0125)
  let syntaxFormula0132 : Wff := (synWrex a (.cv j) syntaxFormula0131)
  let syntaxFormula0133 : Wff := (synWb syntaxFormula0071 syntaxFormula0130)
  let syntaxFormula0134 : Wff := (.classMem (synCopk (.cv x) (.cv j)) syntaxClass0023)
  let syntaxFormula0135 : Wff := (.classMem (synCopk (.cv x) (.cv j)) syntaxClass0024)
  let syntaxClass0136 : Class := (.cab y syntaxFormula0132)
  let syntaxFormula0137 : Wff := (.classEq (.cv x) syntaxClass0136)
  let syntaxFormula0138 : Wff := (.classMem (synCopk (.cv x) (.cv j)) syntaxClass0061)
  let syntaxFormula0139 : Wff := (.classMem (.cv x) syntaxClass0060)
  let syntaxFormula0140 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv n) (.cv x))) syntaxClass0056)
  let syntaxFormula0141 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0140)
  let syntaxFormula0142 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv y)))) syntaxFormula0140)
  let syntaxFormula0143 : Wff := (synWex y syntaxFormula0142)
  let syntaxFormula0144 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0140)
  let syntaxFormula0145 : Wff := (synWex t syntaxFormula0142)
  let syntaxFormula0146 : Wff := (synWex y syntaxFormula0145)
  let syntaxFormula0147 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (.cv x)))
      syntaxClass0056)
  let syntaxFormula0148 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv n))) syntaxClass0053)
  let syntaxFormula0149 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0148)
  let syntaxFormula0150 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv x)))) syntaxFormula0148)
  let syntaxFormula0151 : Wff := (synWex x syntaxFormula0150)
  let syntaxFormula0152 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0148)
  let syntaxFormula0153 : Wff := (synWex t syntaxFormula0150)
  let syntaxFormula0154 : Wff := (synWex x syntaxFormula0153)
  let syntaxFormula0155 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv n)))
      syntaxClass0053)
  let syntaxFormula0156 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv n))) syntaxClass0041)
  let syntaxFormula0157 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0156)
  let syntaxFormula0158 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))) syntaxFormula0156)
  let syntaxFormula0159 : Wff := (synWex y syntaxFormula0158)
  let syntaxFormula0160 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0156)
  let syntaxFormula0161 : Wff := (synWex t syntaxFormula0158)
  let syntaxFormula0162 : Wff := (synWex y syntaxFormula0161)
  let syntaxFormula0163 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv n)))
      syntaxClass0041)
  let syntaxFormula0164 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv n)))
      (synCins3k (synCssetk)))
  let syntaxFormula0165 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (synCsn (.cv y)) (.cv n))) syntaxClass0038)
  let syntaxFormula0166 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c)))) syntaxFormula0165)
  let syntaxFormula0167 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))) syntaxFormula0165)
  let syntaxFormula0168 : Wff := (synWex a syntaxFormula0167)
  let syntaxFormula0169 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synC1c))) syntaxFormula0165)
  let syntaxFormula0170 : Wff := (synWex t syntaxFormula0167)
  let syntaxFormula0171 : Wff := (synWex a syntaxFormula0170)
  let syntaxClass0172 : Class :=
    (synCopk (synCsn (synCsn (synCsn (.cv a)))) (synCopk (synCsn (.cv y)) (.cv n)))
  let syntaxFormula0173 : Wff := (.classMem syntaxClass0172 syntaxClass0038)
  let syntaxFormula0174 : Wff := (.classMem syntaxClass0172 (synCins2k (synCssetk)))
  let syntaxClass0175 : Class := (synCopk (.cv t) syntaxClass0172)
  let syntaxFormula0176 : Wff := (.classMem syntaxClass0175 syntaxClass0036)
  let syntaxFormula0177 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      syntaxFormula0176)
  let syntaxFormula0178 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
      syntaxFormula0176)
  let syntaxFormula0179 : Wff := (synWex b syntaxFormula0178)
  let syntaxFormula0180 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0176)
  let syntaxFormula0181 : Wff := (synWex t syntaxFormula0178)
  let syntaxFormula0182 : Wff := (synWex b syntaxFormula0181)
  let syntaxClass0183 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) syntaxClass0172)
  let syntaxFormula0184 : Wff := (.classMem syntaxClass0183 syntaxClass0036)
  let syntaxFormula0185 : Wff :=
    (.classMem syntaxClass0183 (synCins2k (synCins2k (synCssetk))))
  let syntaxFormula0186 : Wff :=
    (.classMem (synCopk (synCsn (.cv a)) (synCsn (.cv b))) syntaxClass0025)
  let syntaxFormula0187 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv a))))
        (synCsn (synCsn (synCsn (.cv b))))) syntaxClass0027)
  let syntaxFormula0188 : Wff := (.classMem syntaxClass0183 syntaxClass0029)
  let syntaxFormula0189 : Wff := (.classMem syntaxClass0183 syntaxClass0030)
  let syntaxClass0190 : Class := (synCopk (.cv t) syntaxClass0183)
  let syntaxFormula0191 : Wff := (.classMem syntaxClass0190 syntaxClass0032)
  let syntaxFormula0192 : Wff := (synWa syntaxFormula0096 syntaxFormula0191)
  let syntaxFormula0193 : Wff := (synWa syntaxFormula0098 syntaxFormula0191)
  let syntaxFormula0194 : Wff := (synWex x syntaxFormula0193)
  let syntaxFormula0195 : Wff := (synWrex t syntaxClass0013 syntaxFormula0191)
  let syntaxFormula0196 : Wff := (synWex t syntaxFormula0193)
  let syntaxFormula0197 : Wff := (synWex x syntaxFormula0196)
  let syntaxClass0198 : Class := (synCopk syntaxClass0097 syntaxClass0183)
  let syntaxFormula0199 : Wff := (.classMem syntaxClass0198 syntaxClass0032)
  let syntaxFormula0200 : Wff :=
    (.classMem syntaxClass0198 (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))))
  let syntaxFormula0201 : Wff :=
    (.classMem syntaxClass0198
      (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))))
  let syntaxFormula0202 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
        (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      (synCsik (synCsik (synCsik (synCsik (synCssetk))))))
  let syntaxFormula0203 : Wff := (.classMem syntaxClass0198 syntaxClass0010)
  let syntaxFormula0204 : Wff := (.classMem syntaxClass0198 syntaxClass0031)
  let syntaxFormula0205 : Wff := (synWb syntaxFormula0200 syntaxFormula0204)
  let syntaxFormula0206 : Wff := (.classMem syntaxClass0183 syntaxClass0033)
  let syntaxFormula0207 : Wff := (.classMem syntaxClass0183 syntaxClass0034)
  let syntaxFormula0208 : Wff := (.classMem syntaxClass0183 syntaxClass0035)
  let syntaxFormula0209 : Wff := (.classMem syntaxClass0172 syntaxClass0037)
  let syntaxFormula0210 : Wff := (synWrex b (.cv n) syntaxFormula0125)
  let syntaxFormula0211 : Wff :=
    (.classMem (synCopk (synCsn (.cv y)) (.cv n)) syntaxClass0039)
  let syntaxFormula0212 : Wff := (synWrex a (.cv n) syntaxFormula0210)
  let syntaxFormula0213 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv n)))
      syntaxClass0040)
  let syntaxFormula0214 : Wff := (synWb syntaxFormula0164 syntaxFormula0213)
  let syntaxFormula0215 : Wff := (.classMem (synCopk (.cv x) (.cv n)) syntaxClass0042)
  let syntaxFormula0216 : Wff := (.classMem (synCopk (.cv x) (.cv n)) syntaxClass0043)
  let syntaxClass0217 : Class := (.cab y syntaxFormula0212)
  let syntaxFormula0218 : Wff := (.classEq (.cv x) syntaxClass0217)
  let syntaxFormula0219 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv n)))
      syntaxClass0044)
  let syntaxClass0220 : Class := (synCimak syntaxClass0050 (.cv x))
  let syntaxFormula0221 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv n)))
      syntaxClass0052)
  let syntaxFormula0222 : Wff :=
    (synWa (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
      (.classEq (.cv y) (synCplc (.cv x) (synC1c))))
  let syntaxFormula0223 : Wff := (.classMem (synCopk (.cv y) (.cv n)) syntaxClass0054)
  let syntaxFormula0224 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (.cv x)))
      syntaxClass0055)
  let syntaxFormula0225 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (.cv x)))
      (synCins2k (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv)))))
  let syntaxFormula0226 : Wff := (.classMem (synCopk (.cv n) (.cv x)) syntaxClass0057)
  let syntaxFormula0227 : Wff :=
    (.imp (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
  let syntaxFormula0228 : Wff := (.neg syntaxFormula0227)
  let syntaxFormula0229 : Wff := (.classMem (.cv x) syntaxClass0058)
  let syntaxFormula0230 : Wff := (synWrex n (synCnnc) syntaxFormula0228)
  let syntaxFormula0231 : Wff :=
    (.imp (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (synWne (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
  let syntaxFormula0232 : Wff := (synWral n (synCnnc) syntaxFormula0231)
  let syntaxFormula0233 : Wff := (.neg syntaxFormula0230)
  let syntaxFormula0234 : Wff := (.classMem (.cv x) syntaxClass0059)
  let syntaxFormula0235 : Wff := (synWo (.classEq (.cv x) (synC0)) syntaxFormula0232)
  let syntaxFormula0236 : Wff := (.classMem (synCopk (.cv x) (.cv j)) syntaxClass0062)
  let syntaxFormula0237 : Wff :=
    (synWa (.classEq (.cv x) (synCplc (.cv j) (.cv j))) syntaxFormula0235)
  let syntaxClass0238 : Class := (synCimak syntaxClass0062 (synCvv))
  let syntaxFormula0239 : Wff := (.classMem (.cv j) syntaxClass0238)
  let syntaxFormula0240 : Wff :=
    (.imp (synWne (synCplc (.cv j) (.cv j)) (synC0)) syntaxFormula0002)
  have p0000 := (Nominal.biimpRefl syntaxFormula0003)
  have p0001 := @gVex j
  have p0002 := @gElimakv x syntaxClass0062 (.cv j) dv_cache_0001 dv_cache_0002 p0001
  have p0003 := @gElin (synCopk (.cv x) (.cv j)) syntaxClass0024 syntaxClass0061
  have p0004 := @gOpkex (.cv x) (.cv j)
  have p0005 :=
    @gElimak t syntaxClass0022 (synCpw1 (synCpw1 (synC1c))) (synCopk (.cv x) (.cv j))
      dv_cache_0003 dv_cache_0004 dv_cache_0005 p0004
  have p0006 := @gElpw121c y (.cv t) dv_cache_0006
  have p0007 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex y (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))))
      syntaxFormula0063 p0006
  have p0008 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))) syntaxFormula0063
      y dv_cache_0007
  have p0009 :=
    @gBitr4i syntaxFormula0064
      (synWa (synWex y (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))))
        syntaxFormula0063)
      syntaxFormula0066 p0007 p0008
  have p0010 := @gExbii syntaxFormula0064 syntaxFormula0066 t p0009
  have p0011 := (Nominal.biimpRefl syntaxFormula0067)
  have p0012 := @gExcom syntaxFormula0065 y t
  have p0013 :=
    @gN3bitr4i (synWex t syntaxFormula0064) (synWex t syntaxFormula0066)
      syntaxFormula0067 syntaxFormula0069 p0010 p0011 p0012
  have p0014 := @gSnex (synCsn (synCsn (.cv y)))
  have p0015 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv j))
  have p0016 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
      (synCopk (.cv t) (synCopk (.cv x) (.cv j)))
      (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv j)))
      syntaxClass0022 p0015
  have p0017 :=
    @gCeqsexv syntaxFormula0063 syntaxFormula0070 t (synCsn (synCsn (synCsn (.cv y))))
      dv_cache_0008 dv_cache_0009 p0014 p0016
  have p0018 :=
    @gElsymdif
      (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv j)))
      (synCins3k (synCssetk)) syntaxClass0021
  have p0019 := @gSnex (.cv y)
  have p0020 := @gVex x
  have p0021 :=
    @gOtkelins3k (synCsn (.cv y)) (.cv x) (.cv j) (synCssetk) p0019 p0020 p0001
  have p0022 := @gVex y
  have p0023 := @gElssetk (.cv y) (.cv x) p0022 p0020
  have p0024_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCssetk)) (.objMem y x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gBitri syntaxFormula0071
      (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCssetk)) (.objMem y x) p0021
      p0024_e01_recanon
  have p0025 :=
    @gOtkelins2k (synCsn (.cv y)) (.cv x) (.cv j) syntaxClass0020 p0019 p0020 p0001
  have p0026 := @gOpkex (synCsn (.cv y)) (.cv j)
  have p0027 :=
    @gElimak t syntaxClass0019 (synCpw1 (synCpw1 (synC1c)))
      (synCopk (synCsn (.cv y)) (.cv j)) dv_cache_0010 dv_cache_0004 dv_cache_0011 p0026
  have p0028 := @gElpw121c b (.cv t) dv_cache_0012
  have p0029 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b))))))
      syntaxFormula0072 p0028
  have p0030 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b))))) syntaxFormula0072
      b dv_cache_0013
  have p0031 :=
    @gBitr4i syntaxFormula0073
      (synWa (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b))))))
        syntaxFormula0072)
      syntaxFormula0075 p0029 p0030
  have p0032 := @gExbii syntaxFormula0073 syntaxFormula0075 t p0031
  have p0033 := (Nominal.biimpRefl syntaxFormula0076)
  have p0034 := @gExcom syntaxFormula0074 b t
  have p0035 :=
    @gN3bitr4i (synWex t syntaxFormula0073) (synWex t syntaxFormula0075)
      syntaxFormula0076 syntaxFormula0078 p0032 p0033 p0034
  have p0036 := @gSnex (synCsn (synCsn (.cv b)))
  have p0037 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv b))))
      (synCopk (synCsn (.cv y)) (.cv j))
  have p0038 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv b)))))
      (synCopk (.cv t) (synCopk (synCsn (.cv y)) (.cv j))) syntaxClass0079
      syntaxClass0019 p0037
  have p0039 :=
    @gCeqsexv syntaxFormula0072 syntaxFormula0080 t (synCsn (synCsn (synCsn (.cv b))))
      dv_cache_0014 dv_cache_0015 p0036 p0038
  have p0040 := @gElin syntaxClass0079 (synCins2k (synCssetk)) syntaxClass0018
  have p0041 := @gSnex (.cv b)
  have p0042 :=
    @gOtkelins2k (synCsn (.cv b)) (synCsn (.cv y)) (.cv j) (synCssetk) p0041 p0019
      p0001
  have p0043 := @gVex b
  have p0044 := @gElssetk (.cv b) (.cv j) p0043 p0001
  have p0045_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv b)) (.cv j)) (synCssetk)) (.objMem b j)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gBitri syntaxFormula0081
      (.classMem (synCopk (synCsn (.cv b)) (.cv j)) (synCssetk)) (.objMem b j) p0042
      p0045_e01_recanon
  have p0046 :=
    @gOpkex (synCsn (synCsn (synCsn (.cv b)))) (synCopk (synCsn (.cv y)) (.cv j))
  have p0047 :=
    @gElimak t syntaxClass0017 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      syntaxClass0079 dv_cache_0016 dv_cache_0017 dv_cache_0018 p0046
  have p0048 := @gElpw141c a (.cv t) dv_cache_0019
  have p0049 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex a (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))))
      syntaxFormula0083 p0048
  have p0050 :=
    @gN1941v
      (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))))
      syntaxFormula0083 a dv_cache_0020
  have p0051 :=
    @gBitr4i syntaxFormula0084
      (synWa (synWex a
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))))
        syntaxFormula0083)
      syntaxFormula0086 p0049 p0050
  have p0052 := @gExbii syntaxFormula0084 syntaxFormula0086 t p0051
  have p0053 := (Nominal.biimpRefl syntaxFormula0087)
  have p0054 := @gExcom syntaxFormula0085 a t
  have p0055 :=
    @gN3bitr4i (synWex t syntaxFormula0084) (synWex t syntaxFormula0086)
      syntaxFormula0087 syntaxFormula0089 p0052 p0053 p0054
  have p0056 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv a)))))
  have p0057 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a))))))
      syntaxClass0079
  have p0058 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))))
      syntaxClass0082 syntaxClass0090 syntaxClass0017 p0057
  have p0059 :=
    @gCeqsexv syntaxFormula0083 syntaxFormula0091 t
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) dv_cache_0021
      dv_cache_0022 p0056 p0058
  have p0060 :=
    @gElin syntaxClass0090 (synCins2k (synCins2k (synCssetk))) syntaxClass0016
  have p0061 := @gSnex (synCsn (synCsn (.cv a)))
  have p0062 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv a))))
      (synCsn (synCsn (synCsn (.cv b)))) (synCopk (synCsn (.cv y)) (.cv j))
      (synCins2k (synCssetk)) p0061 p0036 p0026
  have p0063 := @gSnex (.cv a)
  have p0064 :=
    @gOtkelins2k (synCsn (.cv a)) (synCsn (.cv y)) (.cv j) (synCssetk) p0063 p0019
      p0001
  have p0065 := @gVex a
  have p0066 := @gElssetk (.cv a) (.cv j) p0065 p0001
  have p0067_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv a)) (.cv j)) (synCssetk)) (.objMem a j)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gN3bitri syntaxFormula0092
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv a))))
          (synCopk (synCsn (.cv y)) (.cv j))) (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv a)) (.cv j)) (synCssetk)) (.objMem a j) p0062
      p0064 p0067_e02_recanon
  have p0068 := @gElin syntaxClass0090 syntaxClass0009 syntaxClass0015
  have p0069 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (.cv a))))
      (synCsn (synCsn (synCsn (.cv b)))) (synCopk (synCsn (.cv y)) (.cv j))
      syntaxClass0008 p0061 p0036 p0026
  have p0070 := @gSnex (synCsn (.cv a))
  have p0071 := @gSnex (synCsn (.cv b))
  have p0072 :=
    @gOpksnelsik (synCsn (synCsn (.cv a))) (synCsn (synCsn (.cv b))) syntaxClass0007
      p0070 p0071
  have p0073 :=
    @gOpksnelsik (synCsn (.cv a)) (synCsn (.cv b)) syntaxClass0006 p0063 p0041
  have p0074 := @gOpksnelsik (.cv a) (.cv b) syntaxClass0005 p0065 p0043
  have p0075 := @gNdisjrelk (.cv a) (.cv b) p0065 p0043
  have p0076 :=
    @gNotbii syntaxFormula0093 (synWne (synCin (.cv a) (.cv b)) (synC0)) p0075
  have p0077 := @gOpkex (.cv a) (.cv b)
  have p0078 := @gElcompl (synCopk (.cv a) (.cv b)) syntaxClass0004 p0077
  have p0079 := (Nominal.biimpRefl (synWne (synCin (.cv a) (.cv b)) (synC0)))
  have p0080 :=
    @gCon2bii (synWne (synCin (.cv a) (.cv b)) (synC0))
      (.classEq (synCin (.cv a) (.cv b)) (synC0)) p0079
  have p0081 :=
    @gN3bitr4i (.neg syntaxFormula0093)
      (.neg (synWne (synCin (.cv a) (.cv b)) (synC0)))
      (.classMem (synCopk (.cv a) (.cv b)) syntaxClass0005)
      (.classEq (synCin (.cv a) (.cv b)) (synC0)) p0076 p0078 p0080
  have p0082 :=
    @gN3bitri syntaxFormula0094
      (.classMem (synCopk (synCsn (.cv a)) (synCsn (.cv b))) syntaxClass0006)
      (.classMem (synCopk (.cv a) (.cv b)) syntaxClass0005)
      (.classEq (synCin (.cv a) (.cv b)) (synC0)) p0073 p0074 p0081
  have p0083 :=
    @gN3bitri syntaxFormula0095
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv a))))
          (synCsn (synCsn (synCsn (.cv b))))) syntaxClass0008)
      syntaxFormula0094 (.classEq (synCin (.cv a) (.cv b)) (synC0)) p0069 p0072 p0082
  have p0084 :=
    @gOpkex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0079
  have p0085 :=
    @gElimak t syntaxClass0012 syntaxClass0013 syntaxClass0090 dv_cache_0023
      dv_cache_0024 dv_cache_0025 p0084
  have p0086 := @gElpw171c x (.cv t) dv_cache_0026
  have p0087 := @gAnbi1i syntaxFormula0096 syntaxFormula0099 syntaxFormula0101 p0086
  have p0088 := @gN1941v syntaxFormula0098 syntaxFormula0101 x dv_cache_0027
  have p0089 :=
    @gBitr4i syntaxFormula0102 (synWa syntaxFormula0099 syntaxFormula0101)
      syntaxFormula0104 p0087 p0088
  have p0090 := @gExbii syntaxFormula0102 syntaxFormula0104 t p0089
  have p0091 := (Nominal.biimpRefl syntaxFormula0105)
  have p0092 := @gExcom syntaxFormula0103 x t
  have p0093 :=
    @gN3bitr4i (synWex t syntaxFormula0102) (synWex t syntaxFormula0104)
      syntaxFormula0105 syntaxFormula0107 p0090 p0091 p0092
  have p0094 :=
    @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))))
  have p0095 := @gOpkeq1 (.cv t) syntaxClass0097 syntaxClass0090
  have p0096 :=
    @gEleq1d syntaxFormula0098 syntaxClass0100 syntaxClass0108 syntaxClass0012 p0095
  have p0097 :=
    @gCeqsexv syntaxFormula0101 syntaxFormula0109 t syntaxClass0097 dv_cache_0028
      dv_cache_0029 p0094 p0096
  have p0098 :=
    @gElsymdif syntaxClass0108
      (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) syntaxClass0011
  have p0099 := @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
  have p0100 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0079
      (synCins2k (synCins3k (synCsik (synCssetk)))) p0099 p0056 p0046
  have p0101 := @gSnex (synCsn (synCsn (synCsn (.cv x))))
  have p0102 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv b)))) (synCopk (synCsn (.cv y)) (.cv j))
      (synCins3k (synCsik (synCssetk))) p0101 p0036 p0026
  have p0103 := @gSnex (synCsn (.cv x))
  have p0104 :=
    @gOtkelins3k (synCsn (synCsn (.cv x))) (synCsn (.cv y)) (.cv j)
      (synCsik (synCssetk)) p0103 p0019 p0001
  have p0105 := @gSnex (.cv x)
  have p0106 := @gOpksnelsik (synCsn (.cv x)) (.cv y) (synCssetk) p0105 p0022
  have p0107 := @gElssetk (.cv x) (.cv y) p0020 p0022
  have p0108_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk (synCsn (.cv y)) (.cv j))) (synCins3k (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv y)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y) p0104
      p0106 p0108_e02_recanon
  have p0109 :=
    @gN3bitri syntaxFormula0110
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          syntaxClass0079) (synCins2k (synCins3k (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk (synCsn (.cv y)) (.cv j))) (synCins3k (synCsik (synCssetk))))
      (.objMem x y) p0100 p0102 p0108
  have p0110 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0079
      (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))) p0099 p0056
      p0046
  have p0111 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv x)))))
  have p0112 := @gSnex (synCsn (synCsn (synCsn (.cv a))))
  have p0113 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (synCsn (synCsn (synCsn (synCsn (.cv a)))))
      (synCsik (synCsik (synCsik (synCsik (synCssetk))))) p0111 p0112
  have p0114 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv a)))) (synCsik (synCsik (synCsik (synCssetk))))
      p0101 p0061
  have p0115 := @gSnex (synCsn (synCsn (.cv x)))
  have p0116 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv a)))
      (synCsik (synCsik (synCssetk))) p0115 p0070
  have p0117 :=
    @gOpksnelsik (synCsn (synCsn (.cv x))) (synCsn (.cv a)) (synCsik (synCssetk))
      p0103 p0063
  have p0118 := @gOpksnelsik (synCsn (.cv x)) (.cv a) (synCssetk) p0105 p0065
  have p0119 := @gElssetk (.cv x) (.cv a) p0020 p0065
  have p0120_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk)) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gN3bitri syntaxFormula0111
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv a)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk)) (.objMem x a) p0117
      p0118 p0120_e02_recanon
  have p0121 :=
    @gN3bitri syntaxFormula0112 syntaxFormula0114 syntaxFormula0111 (.objMem x a) p0114
      p0116 p0120
  have p0122 :=
    @gN3bitri syntaxFormula0115
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))))
        (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
      syntaxFormula0112 (.objMem x a) p0110 p0113 p0121
  have p0123 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv a)))))) syntaxClass0079
      (synCins3k (synCsik (synCsik (synCsik (synCssetk))))) p0099 p0056 p0046
  have p0124 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv b)))) (synCopk (synCsn (.cv y)) (.cv j))
      (synCsik (synCsik (synCsik (synCssetk)))) p0101 p0036 p0026
  have p0125 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (.cv x)))) (synCsn (synCsn (.cv b)))
      (synCsik (synCsik (synCssetk))) p0115 p0071
  have p0126 :=
    @gOpksnelsik (synCsn (synCsn (.cv x))) (synCsn (.cv b)) (synCsik (synCssetk))
      p0103 p0041
  have p0127 := @gOpksnelsik (synCsn (.cv x)) (.cv b) (synCssetk) p0105 p0043
  have p0128 := @gElssetk (.cv x) (.cv b) p0020 p0043
  have p0129_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCssetk)) (.objMem x b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv b)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCssetk)) (.objMem x b) p0127
      p0129_e01_recanon
  have p0130 :=
    @gN3bitri syntaxFormula0117 syntaxFormula0118
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv b)))
        (synCsik (synCssetk)))
      (.objMem x b) p0125 p0126 p0129
  have p0131 :=
    @gN3bitri syntaxFormula0119
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          syntaxClass0079) (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
      syntaxFormula0117 (.objMem x b) p0123 p0124 p0130
  have p0132 :=
    @gOrbi12i syntaxFormula0115 (.objMem x a) syntaxFormula0119 (.objMem x b) p0122 p0131
  have p0133 :=
    @gElun syntaxClass0108 syntaxClass0010
      (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
  have p0134 := @gElun (.cv x) (.cv a) (.cv b)
  have p0135_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) (synCun (.cv a) (.cv b)))
        (synWo (.objMem x a) (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCun, synCnin, synWnan, synWa, synCcompl, synWo]
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
    @gN3bitr4i (synWo syntaxFormula0115 syntaxFormula0119)
      (synWo (.objMem x a) (.objMem x b)) syntaxFormula0120
      (.classMem (.cv x) (synCun (.cv a) (.cv b))) p0132 p0133 p0135_e02_recanon
  have p0136 :=
    @gBibi12i syntaxFormula0110 (.objMem x y) syntaxFormula0120
      (.classMem (.cv x) (synCun (.cv a) (.cv b))) p0109 p0135
  have p0137 :=
    @gNotbii syntaxFormula0121
      (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b)))) p0136
  have p0138 :=
    @gN3bitri syntaxFormula0106 syntaxFormula0109 (.neg syntaxFormula0121)
      (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b))))) p0097
      p0098 p0137
  have p0139 :=
    @gExbii syntaxFormula0106
      (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b))))) x p0138
  have p0140 :=
    @gN3bitri syntaxFormula0122 syntaxFormula0105 syntaxFormula0107
      (synWex x (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b))))))
      p0085 p0093 p0139
  have p0141 :=
    @gNotbii syntaxFormula0122
      (synWex x (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b))))))
      p0140
  have p0142 := @gElcompl syntaxClass0090 syntaxClass0014 p0084
  have p0143 := @gDfcleq x (.cv y) (synCun (.cv a) (.cv b)) dv_cache_0030 dv_cache_0031
  have p0144 :=
    @gAlex (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b)))) x
  have p0145_e00_recanon :
    Nominal.NPrf
      (synWb (.classEq (.cv y) (synCun (.cv a) (.cv b)))
        (.all x (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b)))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCun, synCnin, synWnan, synWa, synCcompl]
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
    @gBitri (.classEq (.cv y) (synCun (.cv a) (.cv b)))
      (.all x (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b)))))
      (.neg (synWex x
          (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b)))))))
      p0145_e00_recanon p0144
  have p0146 :=
    @gN3bitr4i (.neg syntaxFormula0122)
      (.neg (synWex x
          (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b)))))))
      syntaxFormula0123 (.classEq (.cv y) (synCun (.cv a) (.cv b))) p0141 p0142 p0145
  have p0147 :=
    @gAnbi12i syntaxFormula0095 (.classEq (synCin (.cv a) (.cv b)) (synC0))
      syntaxFormula0123 (.classEq (.cv y) (synCun (.cv a) (.cv b))) p0083 p0146
  have p0148 :=
    @gBitri syntaxFormula0124 (synWa syntaxFormula0095 syntaxFormula0123)
      syntaxFormula0125 p0068 p0147
  have p0149 :=
    @gAnbi12i syntaxFormula0092 (.objMem a j) syntaxFormula0124 syntaxFormula0125 p0067
      p0148
  have p0150 :=
    @gN3bitri syntaxFormula0088 syntaxFormula0091
      (synWa syntaxFormula0092 syntaxFormula0124)
      (synWa (.objMem a j) syntaxFormula0125) p0059 p0060 p0149
  have p0151 :=
    @gExbii syntaxFormula0088 (synWa (.objMem a j) syntaxFormula0125) a p0150
  have p0152 :=
    @gN3bitri syntaxFormula0126 syntaxFormula0087 syntaxFormula0089
      (synWex a (synWa (.objMem a j) syntaxFormula0125)) p0047 p0055 p0151
  have p0153 := (Nominal.biimpRefl syntaxFormula0127)
  have p0154_e01_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0127 (synWex a (synWa (.objMem a j) syntaxFormula0125))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWex, synWa]
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
    @gBitr4i syntaxFormula0126 (synWex a (synWa (.objMem a j) syntaxFormula0125))
      syntaxFormula0127 p0152 p0154_e01_recanon
  have p0155 :=
    @gAnbi12i syntaxFormula0081 (.objMem b j) syntaxFormula0126 syntaxFormula0127 p0045
      p0154
  have p0156 :=
    @gN3bitri syntaxFormula0077 syntaxFormula0080
      (synWa syntaxFormula0081 syntaxFormula0126)
      (synWa (.objMem b j) syntaxFormula0127) p0039 p0040 p0155
  have p0157 :=
    @gExbii syntaxFormula0077 (synWa (.objMem b j) syntaxFormula0127) b p0156
  have p0158 :=
    @gN3bitri syntaxFormula0128 syntaxFormula0076 syntaxFormula0078
      (synWex b (synWa (.objMem b j) syntaxFormula0127)) p0027 p0035 p0157
  have p0159 := (Nominal.biimpRefl syntaxFormula0129)
  have p0160_e01_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0129 (synWex b (synWa (.objMem b j) syntaxFormula0127))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWex, synWa]
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
    @gBitr4i syntaxFormula0128 (synWex b (synWa (.objMem b j) syntaxFormula0127))
      syntaxFormula0129 p0158 p0160_e01_recanon
  have p0161 :=
    @gRexcom syntaxFormula0125 b a (.cv j) (.cv j) dv_cache_0032 dv_cache_0033
      dv_cache_0034
  have p0162 :=
    @gN3bitri syntaxFormula0130 syntaxFormula0128 syntaxFormula0129 syntaxFormula0132
      p0025 p0160 p0161
  have p0163 :=
    @gBibi12i syntaxFormula0071 (.objMem y x) syntaxFormula0130 syntaxFormula0132 p0024
      p0162
  have p0164 := @gNotbii syntaxFormula0133 (synWb (.objMem y x) syntaxFormula0132) p0163
  have p0165 :=
    @gN3bitri syntaxFormula0068 syntaxFormula0070 (.neg syntaxFormula0133)
      (.neg (synWb (.objMem y x) syntaxFormula0132)) p0017 p0018 p0164
  have p0166 :=
    @gExbii syntaxFormula0068 (.neg (synWb (.objMem y x) syntaxFormula0132)) y p0165
  have p0167 :=
    @gN3bitri syntaxFormula0134 syntaxFormula0067 syntaxFormula0069
      (synWex y (.neg (synWb (.objMem y x) syntaxFormula0132))) p0005 p0013 p0166
  have p0168 :=
    @gNotbii syntaxFormula0134
      (synWex y (.neg (synWb (.objMem y x) syntaxFormula0132))) p0167
  have p0169 := @gElcompl (synCopk (.cv x) (.cv j)) syntaxClass0023 p0004
  have p0170 := @gAlex (synWb (.objMem y x) syntaxFormula0132) y
  have p0171 :=
    @gN3bitr4i (.neg syntaxFormula0134)
      (.neg (synWex y (.neg (synWb (.objMem y x) syntaxFormula0132)))) syntaxFormula0135
      (.all y (synWb (.objMem y x) syntaxFormula0132)) p0168 p0169 p0170
  have p0172 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAddc y a b (.cv j)
      (.cv j) dv_cache_0035 dv_cache_0032 dv_cache_0033 dv_cache_0035 dv_cache_0032
      dv_cache_0033 dv_cache_0036 dv_cache_0037 dv_cache_0038
  have p0173 := @gEqeq2i (synCplc (.cv j) (.cv j)) syntaxClass0136 (.cv x) p0172
  have p0174 := @gEqabb syntaxFormula0132 y (.cv x) dv_cache_0039
  have p0175_e01_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0137 (.all y (synWb (.objMem y x) syntaxFormula0132))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb]
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
    @gBitri (.classEq (.cv x) (synCplc (.cv j) (.cv j))) syntaxFormula0137
      (.all y (synWb (.objMem y x) syntaxFormula0132)) p0173 p0175_e01_recanon
  have p0176 :=
    @gBitr4i syntaxFormula0135 (.all y (synWb (.objMem y x) syntaxFormula0132))
      (.classEq (.cv x) (synCplc (.cv j) (.cv j))) p0171 p0175
  have p0177 := @gOpkelxpk (.cv x) (.cv j) syntaxClass0060 (synCvv) p0020 p0001
  have p0178 :=
    @gMpbiran2 syntaxFormula0138 syntaxFormula0139 (.classMem (.cv j) (synCvv)) p0001
      p0177
  have p0179 := @gElun (.cv x) (synCsn (synC0)) syntaxClass0059
  have p0180 := @gElsnc (.cv x) (synC0) p0020
  have p0181 :=
    @gElimak n syntaxClass0057 (synCnnc) (.cv x) dv_cache_0040 dv_cache_0041
      dv_cache_0042 p0020
  have p0182 := @gOpkex (.cv n) (.cv x)
  have p0183 :=
    @gElimak t syntaxClass0056 (synCpw1 (synC1c)) (synCopk (.cv n) (.cv x))
      dv_cache_0043 dv_cache_0044 dv_cache_0045 p0182
  have p0184 := @gElpw11c y (.cv t) dv_cache_0006
  have p0185 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex y (.classEq (.cv t) (synCsn (synCsn (.cv y))))) syntaxFormula0140 p0184
  have p0186 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv y)))) syntaxFormula0140 y
      dv_cache_0046
  have p0187 :=
    @gBitr4i syntaxFormula0141
      (synWa (synWex y (.classEq (.cv t) (synCsn (synCsn (.cv y))))) syntaxFormula0140)
      syntaxFormula0143 p0185 p0186
  have p0188 := @gExbii syntaxFormula0141 syntaxFormula0143 t p0187
  have p0189 := (Nominal.biimpRefl syntaxFormula0144)
  have p0190 := @gExcom syntaxFormula0142 y t
  have p0191 :=
    @gN3bitr4i (synWex t syntaxFormula0141) (synWex t syntaxFormula0143)
      syntaxFormula0144 syntaxFormula0146 p0188 p0189 p0190
  have p0192 := @gSnex (synCsn (.cv y))
  have p0193 := @gOpkeq1 (.cv t) (synCsn (synCsn (.cv y))) (synCopk (.cv n) (.cv x))
  have p0194 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv y))))
      (synCopk (.cv t) (synCopk (.cv n) (.cv x)))
      (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (.cv x))) syntaxClass0056
      p0193
  have p0195 :=
    @gCeqsexv syntaxFormula0140 syntaxFormula0147 t (synCsn (synCsn (.cv y)))
      dv_cache_0047 dv_cache_0048 p0192 p0194
  have p0196 :=
    @gElin (synCopk (synCsn (synCsn (.cv y))) (synCopk (.cv n) (.cv x)))
      syntaxClass0055
      (synCins2k (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv))))
  have p0197 := @gVex n
  have p0198 := @gOtkelins3k (.cv y) (.cv n) (.cv x) syntaxClass0054 p0022 p0197 p0020
  have p0199 := @gOpkex (.cv y) (.cv n)
  have p0200 :=
    @gElimak t syntaxClass0053 (synCpw1 (synC1c)) (synCopk (.cv y) (.cv n))
      dv_cache_0049 dv_cache_0044 dv_cache_0050 p0199
  have p0201 := @gElpw11c x (.cv t) dv_cache_0026
  have p0202 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex x (.classEq (.cv t) (synCsn (synCsn (.cv x))))) syntaxFormula0148 p0201
  have p0203 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv x)))) syntaxFormula0148 x
      dv_cache_0051
  have p0204 :=
    @gBitr4i syntaxFormula0149
      (synWa (synWex x (.classEq (.cv t) (synCsn (synCsn (.cv x))))) syntaxFormula0148)
      syntaxFormula0151 p0202 p0203
  have p0205 := @gExbii syntaxFormula0149 syntaxFormula0151 t p0204
  have p0206 := (Nominal.biimpRefl syntaxFormula0152)
  have p0207 := @gExcom syntaxFormula0150 x t
  have p0208 :=
    @gN3bitr4i (synWex t syntaxFormula0149) (synWex t syntaxFormula0151)
      syntaxFormula0152 syntaxFormula0154 p0205 p0206 p0207
  have p0209 := @gOpkeq1 (.cv t) (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv n))
  have p0210 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv x))))
      (synCopk (.cv t) (synCopk (.cv y) (.cv n)))
      (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv n))) syntaxClass0053
      p0209
  have p0211 :=
    @gCeqsexv syntaxFormula0148 syntaxFormula0155 t (synCsn (synCsn (.cv x)))
      dv_cache_0052 dv_cache_0053 p0103 p0210
  have p0212 :=
    @gElin (synCopk (synCsn (synCsn (.cv x))) (synCopk (.cv y) (.cv n)))
      syntaxClass0044 syntaxClass0052
  have p0213 := @gOpkex (.cv x) (.cv n)
  have p0214 :=
    @gElimak t syntaxClass0041 (synCpw1 (synCpw1 (synC1c))) (synCopk (.cv x) (.cv n))
      dv_cache_0054 dv_cache_0004 dv_cache_0055 p0213
  have p0215 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex y (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))))
      syntaxFormula0156 p0006
  have p0216 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))) syntaxFormula0156
      y dv_cache_0056
  have p0217 :=
    @gBitr4i syntaxFormula0157
      (synWa (synWex y (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y))))))
        syntaxFormula0156)
      syntaxFormula0159 p0215 p0216
  have p0218 := @gExbii syntaxFormula0157 syntaxFormula0159 t p0217
  have p0219 := (Nominal.biimpRefl syntaxFormula0160)
  have p0220 := @gExcom syntaxFormula0158 y t
  have p0221 :=
    @gN3bitr4i (synWex t syntaxFormula0157) (synWex t syntaxFormula0159)
      syntaxFormula0160 syntaxFormula0162 p0218 p0219 p0220
  have p0222 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv n))
  have p0223 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv y)))))
      (synCopk (.cv t) (synCopk (.cv x) (.cv n)))
      (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv n)))
      syntaxClass0041 p0222
  have p0224 :=
    @gCeqsexv syntaxFormula0156 syntaxFormula0163 t (synCsn (synCsn (synCsn (.cv y))))
      dv_cache_0008 dv_cache_0057 p0014 p0223
  have p0225 :=
    @gElsymdif
      (synCopk (synCsn (synCsn (synCsn (.cv y)))) (synCopk (.cv x) (.cv n)))
      (synCins3k (synCssetk)) syntaxClass0040
  have p0226 :=
    @gOtkelins3k (synCsn (.cv y)) (.cv x) (.cv n) (synCssetk) p0019 p0020 p0197
  have p0227_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCssetk)) (.objMem y x)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gBitri syntaxFormula0164
      (.classMem (synCopk (synCsn (.cv y)) (.cv x)) (synCssetk)) (.objMem y x) p0226
      p0227_e01_recanon
  have p0228 := @gOpkex (synCsn (.cv y)) (.cv n)
  have p0229 :=
    @gElimak t syntaxClass0038 (synCpw1 (synCpw1 (synC1c)))
      (synCopk (synCsn (.cv y)) (.cv n)) dv_cache_0058 dv_cache_0004 dv_cache_0059 p0228
  have p0230 := @gElpw121c a (.cv t) dv_cache_0019
  have p0231 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synC1c))))
      (synWex a (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))))
      syntaxFormula0165 p0230
  have p0232 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))) syntaxFormula0165
      a dv_cache_0060
  have p0233 :=
    @gBitr4i syntaxFormula0166
      (synWa (synWex a (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a))))))
        syntaxFormula0165)
      syntaxFormula0168 p0231 p0232
  have p0234 := @gExbii syntaxFormula0166 syntaxFormula0168 t p0233
  have p0235 := (Nominal.biimpRefl syntaxFormula0169)
  have p0236 := @gExcom syntaxFormula0167 a t
  have p0237 :=
    @gN3bitr4i (synWex t syntaxFormula0166) (synWex t syntaxFormula0168)
      syntaxFormula0169 syntaxFormula0171 p0234 p0235 p0236
  have p0238 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (.cv a))))
      (synCopk (synCsn (.cv y)) (.cv n))
  have p0239 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (.cv a)))))
      (synCopk (.cv t) (synCopk (synCsn (.cv y)) (.cv n))) syntaxClass0172
      syntaxClass0038 p0238
  have p0240 :=
    @gCeqsexv syntaxFormula0165 syntaxFormula0173 t (synCsn (synCsn (synCsn (.cv a))))
      dv_cache_0061 dv_cache_0062 p0061 p0239
  have p0241 := @gElin syntaxClass0172 (synCins2k (synCssetk)) syntaxClass0037
  have p0242 :=
    @gOtkelins2k (synCsn (.cv a)) (synCsn (.cv y)) (.cv n) (synCssetk) p0063 p0019
      p0197
  have p0243 := @gElssetk (.cv a) (.cv n) p0065 p0197
  have p0244_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv a)) (.cv n)) (synCssetk)) (.objMem a n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gBitri syntaxFormula0174
      (.classMem (synCopk (synCsn (.cv a)) (.cv n)) (synCssetk)) (.objMem a n) p0242
      p0244_e01_recanon
  have p0245 :=
    @gOpkex (synCsn (synCsn (synCsn (.cv a)))) (synCopk (synCsn (.cv y)) (.cv n))
  have p0246 :=
    @gElimak t syntaxClass0036 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      syntaxClass0172 dv_cache_0063 dv_cache_0017 dv_cache_0064 p0245
  have p0247 := @gElpw141c b (.cv t) dv_cache_0012
  have p0248 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex b (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))))
      syntaxFormula0176 p0247
  have p0249 :=
    @gN1941v
      (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
      syntaxFormula0176 b dv_cache_0065
  have p0250 :=
    @gBitr4i syntaxFormula0177
      (synWa (synWex b
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))))
        syntaxFormula0176)
      syntaxFormula0179 p0248 p0249
  have p0251 := @gExbii syntaxFormula0177 syntaxFormula0179 t p0250
  have p0252 := (Nominal.biimpRefl syntaxFormula0180)
  have p0253 := @gExcom syntaxFormula0178 b t
  have p0254 :=
    @gN3bitr4i (synWex t syntaxFormula0177) (synWex t syntaxFormula0179)
      syntaxFormula0180 syntaxFormula0182 p0251 p0252 p0253
  have p0255 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv b)))))
  have p0256 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b))))))
      syntaxClass0172
  have p0257 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
      syntaxClass0175 syntaxClass0183 syntaxClass0036 p0256
  have p0258 :=
    @gCeqsexv syntaxFormula0176 syntaxFormula0184 t
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) dv_cache_0066
      dv_cache_0067 p0255 p0257
  have p0259 :=
    @gElin syntaxClass0183 (synCins2k (synCins2k (synCssetk))) syntaxClass0035
  have p0260 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv b))))
      (synCsn (synCsn (synCsn (.cv a)))) (synCopk (synCsn (.cv y)) (.cv n))
      (synCins2k (synCssetk)) p0036 p0061 p0228
  have p0261 :=
    @gOtkelins2k (synCsn (.cv b)) (synCsn (.cv y)) (.cv n) (synCssetk) p0041 p0019
      p0197
  have p0262 := @gElssetk (.cv b) (.cv n) p0043 p0197
  have p0263_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv b)) (.cv n)) (synCssetk)) (.objMem b n)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gN3bitri syntaxFormula0185
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCopk (synCsn (.cv y)) (.cv n))) (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv b)) (.cv n)) (synCssetk)) (.objMem b n) p0260
      p0261 p0263_e02_recanon
  have p0264 := @gElin syntaxClass0183 syntaxClass0030 syntaxClass0034
  have p0265 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (.cv b))))
      (synCsn (synCsn (synCsn (.cv a)))) (synCopk (synCsn (.cv y)) (.cv n))
      syntaxClass0028 p0036 p0061 p0228
  have p0266 :=
    @gOpkelcnvk (synCsn (synCsn (synCsn (.cv b))))
      (synCsn (synCsn (synCsn (.cv a)))) syntaxClass0027 p0036 p0061
  have p0267 :=
    @gOpksnelsik (synCsn (synCsn (.cv a))) (synCsn (synCsn (.cv b))) syntaxClass0026
      p0070 p0071
  have p0268 :=
    @gOpksnelsik (synCsn (.cv a)) (synCsn (.cv b)) syntaxClass0025 p0063 p0041
  have p0269 := @gOpksnelsik (.cv a) (.cv b) syntaxClass0004 p0065 p0043
  have p0270 :=
    @gBitri syntaxFormula0186 syntaxFormula0093
      (synWne (synCin (.cv a) (.cv b)) (synC0)) p0269 p0075
  have p0271 :=
    @gN3bitri syntaxFormula0187
      (.classMem (synCopk (synCsn (synCsn (.cv a))) (synCsn (synCsn (.cv b))))
        syntaxClass0026)
      syntaxFormula0186 (synWne (synCin (.cv a) (.cv b)) (synC0)) p0267 p0268 p0270
  have p0272 :=
    @gN3bitri syntaxFormula0188
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv b))))
          (synCsn (synCsn (synCsn (.cv a))))) syntaxClass0028)
      syntaxFormula0187 (synWne (synCin (.cv a) (.cv b)) (synC0)) p0265 p0266 p0271
  have p0273 :=
    @gNotbii syntaxFormula0188 (synWne (synCin (.cv a) (.cv b)) (synC0)) p0272
  have p0274 :=
    @gOpkex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) syntaxClass0172
  have p0275 := @gElcompl syntaxClass0183 syntaxClass0029 p0274
  have p0276 :=
    @gN3bitr4i (.neg syntaxFormula0188)
      (.neg (synWne (synCin (.cv a) (.cv b)) (synC0))) syntaxFormula0189
      (.classEq (synCin (.cv a) (.cv b)) (synC0)) p0273 p0275 p0080
  have p0277 :=
    @gElimak t syntaxClass0032 syntaxClass0013 syntaxClass0183 dv_cache_0068
      dv_cache_0024 dv_cache_0069 p0274
  have p0278 := @gAnbi1i syntaxFormula0096 syntaxFormula0099 syntaxFormula0191 p0086
  have p0279 := @gN1941v syntaxFormula0098 syntaxFormula0191 x dv_cache_0070
  have p0280 :=
    @gBitr4i syntaxFormula0192 (synWa syntaxFormula0099 syntaxFormula0191)
      syntaxFormula0194 p0278 p0279
  have p0281 := @gExbii syntaxFormula0192 syntaxFormula0194 t p0280
  have p0282 := (Nominal.biimpRefl syntaxFormula0195)
  have p0283 := @gExcom syntaxFormula0193 x t
  have p0284 :=
    @gN3bitr4i (synWex t syntaxFormula0192) (synWex t syntaxFormula0194)
      syntaxFormula0195 syntaxFormula0197 p0281 p0282 p0283
  have p0285 := @gOpkeq1 (.cv t) syntaxClass0097 syntaxClass0183
  have p0286 :=
    @gEleq1d syntaxFormula0098 syntaxClass0190 syntaxClass0198 syntaxClass0032 p0285
  have p0287 :=
    @gCeqsexv syntaxFormula0191 syntaxFormula0199 t syntaxClass0097 dv_cache_0028
      dv_cache_0071 p0094 p0286
  have p0288 :=
    @gElsymdif syntaxClass0198
      (synCins2k (synCins2k (synCins3k (synCsik (synCssetk))))) syntaxClass0031
  have p0289 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) syntaxClass0172
      (synCins2k (synCins3k (synCsik (synCssetk)))) p0099 p0255 p0245
  have p0290 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv a)))) (synCopk (synCsn (.cv y)) (.cv n))
      (synCins3k (synCsik (synCssetk))) p0101 p0061 p0228
  have p0291 :=
    @gOtkelins3k (synCsn (synCsn (.cv x))) (synCsn (.cv y)) (.cv n)
      (synCsik (synCssetk)) p0103 p0019 p0197
  have p0292_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gN3bitri
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk (synCsn (.cv y)) (.cv n))) (synCins3k (synCsik (synCssetk))))
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv y)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv y)) (synCssetk)) (.objMem x y) p0291
      p0106 p0292_e02_recanon
  have p0293 :=
    @gN3bitri syntaxFormula0200
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          syntaxClass0172) (synCins2k (synCins3k (synCsik (synCssetk)))))
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (.cv x)))))
          (synCopk (synCsn (.cv y)) (.cv n))) (synCins3k (synCsik (synCssetk))))
      (.objMem x y) p0289 p0290 p0292
  have p0294 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) syntaxClass0172
      (synCins3k (synCsik (synCsik (synCsik (synCssetk))))) p0099 p0255 p0245
  have p0295 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv a)))) (synCopk (synCsn (.cv y)) (.cv n))
      (synCsik (synCsik (synCsik (synCssetk)))) p0101 p0061 p0228
  have p0296_e01_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk)) (.objMem x a)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gBitri
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv a)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv a)) (synCssetk)) (.objMem x a) p0118
      p0296_e01_recanon
  have p0297 :=
    @gN3bitri syntaxFormula0114 syntaxFormula0111
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv a)))
        (synCsik (synCssetk)))
      (.objMem x a) p0116 p0117 p0296
  have p0298 :=
    @gN3bitri syntaxFormula0201
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          syntaxClass0172) (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
      syntaxFormula0114 (.objMem x a) p0294 p0295 p0297
  have p0299 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))) syntaxClass0172
      (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))) p0099 p0255
      p0245
  have p0300 := @gSnex (synCsn (synCsn (synCsn (.cv b))))
  have p0301 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x))))))
      (synCsn (synCsn (synCsn (synCsn (.cv b)))))
      (synCsik (synCsik (synCsik (synCsik (synCssetk))))) p0111 p0300
  have p0302 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (.cv x)))))
      (synCsn (synCsn (synCsn (.cv b)))) (synCsik (synCsik (synCsik (synCssetk))))
      p0101 p0036
  have p0303_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCssetk)) (.objMem x b)) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCopk, synCpr, synCun, synCnin, synWnan, synWa,
          synCcompl, synCsn, synCssetk, synWex]
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
    @gN3bitri syntaxFormula0118
      (.classMem (synCopk (synCsn (synCsn (.cv x))) (synCsn (.cv b)))
        (synCsik (synCssetk)))
      (.classMem (synCopk (synCsn (.cv x)) (.cv b)) (synCssetk)) (.objMem x b) p0126
      p0127 p0303_e02_recanon
  have p0304 :=
    @gN3bitri syntaxFormula0202 syntaxFormula0117 syntaxFormula0118 (.objMem x b) p0302
      p0125 p0303
  have p0305 :=
    @gN3bitri syntaxFormula0203
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv x)))))))
          (synCsn (synCsn (synCsn (synCsn (synCsn (.cv b)))))))
        (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))))
      syntaxFormula0202 (.objMem x b) p0299 p0301 p0304
  have p0306 :=
    @gOrbi12i syntaxFormula0201 (.objMem x a) syntaxFormula0203 (.objMem x b) p0298 p0305
  have p0307 :=
    @gElun syntaxClass0198
      (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
      syntaxClass0010
  have p0308_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (.cv x) (synCun (.cv a) (.cv b)))
        (synWo (.objMem x a) (.objMem x b))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCun, synCnin, synWnan, synWa, synCcompl, synWo]
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
    @gN3bitr4i (synWo syntaxFormula0201 syntaxFormula0203)
      (synWo (.objMem x a) (.objMem x b)) syntaxFormula0204
      (.classMem (.cv x) (synCun (.cv a) (.cv b))) p0306 p0307 p0308_e02_recanon
  have p0309 :=
    @gBibi12i syntaxFormula0200 (.objMem x y) syntaxFormula0204
      (.classMem (.cv x) (synCun (.cv a) (.cv b))) p0293 p0308
  have p0310 :=
    @gNotbii syntaxFormula0205
      (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b)))) p0309
  have p0311 :=
    @gN3bitri syntaxFormula0196 syntaxFormula0199 (.neg syntaxFormula0205)
      (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b))))) p0287
      p0288 p0310
  have p0312 :=
    @gExbii syntaxFormula0196
      (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b))))) x p0311
  have p0313 :=
    @gN3bitri syntaxFormula0206 syntaxFormula0195 syntaxFormula0197
      (synWex x (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b))))))
      p0277 p0284 p0312
  have p0314 :=
    @gNotbii syntaxFormula0206
      (synWex x (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b))))))
      p0313
  have p0315 := @gElcompl syntaxClass0183 syntaxClass0033 p0274
  have p0316 :=
    @gN3bitr4i (.neg syntaxFormula0206)
      (.neg (synWex x
          (.neg (synWb (.objMem x y) (.classMem (.cv x) (synCun (.cv a) (.cv b)))))))
      syntaxFormula0207 (.classEq (.cv y) (synCun (.cv a) (.cv b))) p0314 p0315 p0145
  have p0317 :=
    @gAnbi12i syntaxFormula0189 (.classEq (synCin (.cv a) (.cv b)) (synC0))
      syntaxFormula0207 (.classEq (.cv y) (synCun (.cv a) (.cv b))) p0276 p0316
  have p0318 :=
    @gBitri syntaxFormula0208 (synWa syntaxFormula0189 syntaxFormula0207)
      syntaxFormula0125 p0264 p0317
  have p0319 :=
    @gAnbi12i syntaxFormula0185 (.objMem b n) syntaxFormula0208 syntaxFormula0125 p0263
      p0318
  have p0320 :=
    @gN3bitri syntaxFormula0181 syntaxFormula0184
      (synWa syntaxFormula0185 syntaxFormula0208)
      (synWa (.objMem b n) syntaxFormula0125) p0258 p0259 p0319
  have p0321 :=
    @gExbii syntaxFormula0181 (synWa (.objMem b n) syntaxFormula0125) b p0320
  have p0322 :=
    @gN3bitri syntaxFormula0209 syntaxFormula0180 syntaxFormula0182
      (synWex b (synWa (.objMem b n) syntaxFormula0125)) p0246 p0254 p0321
  have p0323 := (Nominal.biimpRefl syntaxFormula0210)
  have p0324_e01_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0210 (synWex b (synWa (.objMem b n) syntaxFormula0125))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWex, synWa]
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
    @gBitr4i syntaxFormula0209 (synWex b (synWa (.objMem b n) syntaxFormula0125))
      syntaxFormula0210 p0322 p0324_e01_recanon
  have p0325 :=
    @gAnbi12i syntaxFormula0174 (.objMem a n) syntaxFormula0209 syntaxFormula0210 p0244
      p0324
  have p0326 :=
    @gN3bitri syntaxFormula0170 syntaxFormula0173
      (synWa syntaxFormula0174 syntaxFormula0209)
      (synWa (.objMem a n) syntaxFormula0210) p0240 p0241 p0325
  have p0327 :=
    @gExbii syntaxFormula0170 (synWa (.objMem a n) syntaxFormula0210) a p0326
  have p0328 :=
    @gN3bitri syntaxFormula0211 syntaxFormula0169 syntaxFormula0171
      (synWex a (synWa (.objMem a n) syntaxFormula0210)) p0229 p0237 p0327
  have p0329 :=
    @gOtkelins2k (synCsn (.cv y)) (.cv x) (.cv n) syntaxClass0039 p0019 p0020 p0197
  have p0330 := (Nominal.biimpRefl syntaxFormula0212)
  have p0331_e02_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0212 (synWex a (synWa (.objMem a n) syntaxFormula0210))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synWex, synWa]
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
    @gN3bitr4i syntaxFormula0211 (synWex a (synWa (.objMem a n) syntaxFormula0210))
      syntaxFormula0213 syntaxFormula0212 p0328 p0329 p0331_e02_recanon
  have p0332 :=
    @gBibi12i syntaxFormula0164 (.objMem y x) syntaxFormula0213 syntaxFormula0212 p0227
      p0331
  have p0333 := @gNotbii syntaxFormula0214 (synWb (.objMem y x) syntaxFormula0212) p0332
  have p0334 :=
    @gN3bitri syntaxFormula0161 syntaxFormula0163 (.neg syntaxFormula0214)
      (.neg (synWb (.objMem y x) syntaxFormula0212)) p0224 p0225 p0333
  have p0335 :=
    @gExbii syntaxFormula0161 (.neg (synWb (.objMem y x) syntaxFormula0212)) y p0334
  have p0336 :=
    @gN3bitri syntaxFormula0215 syntaxFormula0160 syntaxFormula0162
      (synWex y (.neg (synWb (.objMem y x) syntaxFormula0212))) p0214 p0221 p0335
  have p0337 :=
    @gNotbii syntaxFormula0215
      (synWex y (.neg (synWb (.objMem y x) syntaxFormula0212))) p0336
  have p0338 := @gElcompl (synCopk (.cv x) (.cv n)) syntaxClass0042 p0213
  have p0339 := @gAlex (synWb (.objMem y x) syntaxFormula0212) y
  have p0340 :=
    @gN3bitr4i (.neg syntaxFormula0215)
      (.neg (synWex y (.neg (synWb (.objMem y x) syntaxFormula0212)))) syntaxFormula0216
      (.all y (synWb (.objMem y x) syntaxFormula0212)) p0337 p0338 p0339
  have p0341 := @gOtkelins2k (.cv x) (.cv y) (.cv n) syntaxClass0043 p0020 p0022 p0197
  have p0342 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfAddc y a b (.cv n)
      (.cv n) dv_cache_0072 dv_cache_0073 dv_cache_0074 dv_cache_0072 dv_cache_0073
      dv_cache_0074 dv_cache_0036 dv_cache_0037 dv_cache_0038
  have p0343 := @gEqeq2i (synCplc (.cv n) (.cv n)) syntaxClass0217 (.cv x) p0342
  have p0344 := @gEqabb syntaxFormula0212 y (.cv x) dv_cache_0039
  have p0345_e01_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0218 (.all y (synWb (.objMem y x) syntaxFormula0212))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb]
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
    @gBitri (.classEq (.cv x) (synCplc (.cv n) (.cv n))) syntaxFormula0218
      (.all y (synWb (.objMem y x) syntaxFormula0212)) p0343 p0345_e01_recanon
  have p0346 :=
    @gN3bitr4i syntaxFormula0216 (.all y (synWb (.objMem y x) syntaxFormula0212))
      syntaxFormula0219 (.classEq (.cv x) (synCplc (.cv n) (.cv n))) p0340 p0341 p0345
  have p0347 := @gOpkelimagek (.cv x) (.cv y) syntaxClass0050 p0020 p0022
  have p0348 := @gOtkelins3k (.cv x) (.cv y) (.cv n) syntaxClass0051 p0020 p0022 p0197
  have p0349 := @gDfaddc2 (.cv x) (synC1c)
  have p0350 := @gEqeq2i (synCplc (.cv x) (synC1c)) syntaxClass0220 (.cv y) p0349
  have p0351 :=
    @gN3bitr4i (.classMem (synCopk (.cv x) (.cv y)) syntaxClass0051)
      (.classEq (.cv y) syntaxClass0220) syntaxFormula0221
      (.classEq (.cv y) (synCplc (.cv x) (synC1c))) p0347 p0348 p0350
  have p0352 :=
    @gAnbi12i syntaxFormula0219 (.classEq (.cv x) (synCplc (.cv n) (.cv n)))
      syntaxFormula0221 (.classEq (.cv y) (synCplc (.cv x) (synC1c))) p0346 p0351
  have p0353 :=
    @gN3bitri syntaxFormula0153 syntaxFormula0155
      (synWa syntaxFormula0219 syntaxFormula0221) syntaxFormula0222 p0211 p0212 p0352
  have p0354 := @gExbii syntaxFormula0153 syntaxFormula0222 x p0353
  have p0355 :=
    @gN3bitri syntaxFormula0223 syntaxFormula0152 syntaxFormula0154
      (synWex x syntaxFormula0222) p0200 p0208 p0354
  have p0356 := @gAddcex (.cv n) (.cv n) p0197 p0197
  have p0357 := @gAddceq1 (.cv x) (synCplc (.cv n) (.cv n)) (synC1c)
  have p0358 :=
    @gEqeq2d (.classEq (.cv x) (synCplc (.cv n) (.cv n))) (synCplc (.cv x) (synC1c))
      (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (.cv y) p0357
  have p0359 :=
    @gCeqsexv (.classEq (.cv y) (synCplc (.cv x) (synC1c)))
      (.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) x
      (synCplc (.cv n) (.cv n)) dv_cache_0075 dv_cache_0076 p0356 p0358
  have p0360 :=
    @gN3bitri syntaxFormula0224 syntaxFormula0223 (synWex x syntaxFormula0222)
      (.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) p0198 p0355 p0359
  have p0361 :=
    @gOtkelins2k (.cv y) (.cv n) (.cv x)
      (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv))) p0022 p0197 p0020
  have p0362 :=
    @gEldif (synCopk (.cv y) (.cv x)) (synCidk) (synCxpk (synCsn (synC0)) (synCvv))
  have p0363 := @gOpkelidkg (.cv y) (.cv x) (synCvv) (synCvv)
  have p0364_e02_recanon :
    Nominal.NPrf
      (.imp (synWa (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCvv)))
        (synWb (.classMem (synCopk (.cv y) (.cv x)) (synCidk)) (.objEq y x))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWa, synCvv, synWb, synCopk, synCpr, synCun, synCnin,
          synWnan, synCcompl, synCsn, synCidk, synWex]
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
    @gMp2an (.classMem (.cv y) (synCvv)) (.classMem (.cv x) (synCvv))
      (synWb (.classMem (synCopk (.cv y) (.cv x)) (synCidk)) (.objEq y x)) p0022 p0020
      p0364_e02_recanon
  have p0365 := @gEqucom y x
  have p0366 :=
    @gBitri (.classMem (synCopk (.cv y) (.cv x)) (synCidk)) (.objEq y x) (.objEq x y)
      p0364 p0365
  have p0367 := @gOpkelxpk (.cv y) (.cv x) (synCsn (synC0)) (synCvv) p0022 p0020
  have p0368 :=
    @gMpbiran2
      (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCsn (synC0)) (synCvv)))
      (.classMem (.cv y) (synCsn (synC0))) (.classMem (.cv x) (synCvv)) p0020 p0367
  have p0369 := @gElsnc (.cv y) (synC0) p0022
  have p0370 :=
    @gBitri
      (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCsn (synC0)) (synCvv)))
      (.classMem (.cv y) (synCsn (synC0))) (.classEq (.cv y) (synC0)) p0368 p0369
  have p0371 :=
    @gNotbii
      (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCsn (synC0)) (synCvv)))
      (.classEq (.cv y) (synC0)) p0370
  have p0372 :=
    @gAnbi12i (.classMem (synCopk (.cv y) (.cv x)) (synCidk)) (.objEq x y)
      (.neg (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCsn (synC0)) (synCvv))))
      (.neg (.classEq (.cv y) (synC0))) p0366 p0371
  have p0373 :=
    @gN3bitri syntaxFormula0225
      (.classMem (synCopk (.cv y) (.cv x))
        (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv))))
      (synWa (.classMem (synCopk (.cv y) (.cv x)) (synCidk)) (.neg
          (.classMem (synCopk (.cv y) (.cv x)) (synCxpk (synCsn (synC0)) (synCvv)))))
      (synWa (.objEq x y) (.neg (.classEq (.cv y) (synC0)))) p0361 p0362 p0372
  have p0374 :=
    @gAnbi12i syntaxFormula0224
      (.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) syntaxFormula0225
      (synWa (.objEq x y) (.neg (.classEq (.cv y) (synC0)))) p0360 p0373
  have p0375 :=
    @gN3bitri syntaxFormula0145 syntaxFormula0147
      (synWa syntaxFormula0224 syntaxFormula0225)
      (synWa (.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synWa (.objEq x y) (.neg (.classEq (.cv y) (synC0)))))
      p0195 p0196 p0374
  have p0376 :=
    @gExbii syntaxFormula0145
      (synWa (.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synWa (.objEq x y) (.neg (.classEq (.cv y) (synC0)))))
      y p0375
  have p0377 :=
    @gN3bitri syntaxFormula0226 syntaxFormula0144 syntaxFormula0146
      (synWex y (synWa (.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWa (.objEq x y) (.neg (.classEq (.cv y) (synC0))))))
      p0183 p0191 p0376
  have p0378 := @gN1cex
  have p0379 := @gAddcex (synCplc (.cv n) (.cv n)) (synC1c) p0356 p0378
  have p0380 := @gEqeq2 (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (.cv x)
  have p0381 := @gEqeq1 (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)
  have p0382 :=
    @gNotbid (.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq (.cv y) (synC0))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) p0381
  have p0383_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (synWb (.objEq x y)
          (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synCplc, synWrex, synWex, synWa, synC1c, synWb]
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
    @gAnbi12d (.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.objEq x y) (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.neg (.classEq (.cv y) (synC0)))
      (.neg (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      p0383_e00_recanon p0382
  have p0384 :=
    @gCeqsexv (synWa (.objEq x y) (.neg (.classEq (.cv y) (synC0))))
      (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (.neg (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      y (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) dv_cache_0077 dv_cache_0078 p0379
      p0383
  have p0385 :=
    @gAnnim (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
  have p0386 :=
    @gN3bitri syntaxFormula0226
      (synWex y (synWa (.classEq (.cv y) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
          (synWa (.objEq x y) (.neg (.classEq (.cv y) (synC0))))))
      (synWa (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
        (.neg (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))))
      syntaxFormula0228 p0377 p0384 p0385
  have p0387 := @gRexbii syntaxFormula0226 syntaxFormula0228 n (synCnnc) p0386
  have p0388 :=
    @gBitri syntaxFormula0229 (synWrex n (synCnnc) syntaxFormula0226) syntaxFormula0230
      p0181 p0387
  have p0389 := @gNotbii syntaxFormula0229 syntaxFormula0230 p0388
  have p0390 := @gElcompl (.cv x) syntaxClass0058 p0020
  have p0391 :=
    (Nominal.biimpRefl (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
  have p0392 :=
    (Nominal.biimpRefl (synWne (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))))
  have p0393 :=
    @gImbi12i (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
      (.neg (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
      (synWne (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.neg (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))) p0391
      p0392
  have p0394 :=
    @gCon34b (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))
      (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0))
  have p0395 :=
    @gBitr4i syntaxFormula0231
      (.imp (.neg (.classEq (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)))
        (.neg (.classEq (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c)))))
      syntaxFormula0227 p0393 p0394
  have p0396 := @gRalbii syntaxFormula0231 syntaxFormula0227 n (synCnnc) p0395
  have p0397 := @gDfral2 syntaxFormula0227 n (synCnnc)
  have p0398 :=
    @gBitri syntaxFormula0232 (synWral n (synCnnc) syntaxFormula0227) syntaxFormula0233
      p0396 p0397
  have p0399 :=
    @gN3bitr4i (.neg syntaxFormula0229) syntaxFormula0233 syntaxFormula0234
      syntaxFormula0232 p0389 p0390 p0398
  have p0400 :=
    @gOrbi12i (.classMem (.cv x) (synCsn (synC0))) (.classEq (.cv x) (synC0))
      syntaxFormula0234 syntaxFormula0232 p0180 p0399
  have p0401 :=
    @gN3bitri syntaxFormula0138 syntaxFormula0139
      (synWo (.classMem (.cv x) (synCsn (synC0))) syntaxFormula0234) syntaxFormula0235
      p0178 p0179 p0400
  have p0402 :=
    @gAnbi12i syntaxFormula0135 (.classEq (.cv x) (synCplc (.cv j) (.cv j)))
      syntaxFormula0138 syntaxFormula0235 p0176 p0401
  have p0403 :=
    @gBitri syntaxFormula0236 (synWa syntaxFormula0135 syntaxFormula0138)
      syntaxFormula0237 p0003 p0402
  have p0404 := @gExbii syntaxFormula0236 syntaxFormula0237 x p0403
  have p0405 := @gAddcex (.cv j) (.cv j) p0001 p0001
  have p0406 := @gEqeq1 (.cv x) (synCplc (.cv j) (.cv j)) (synC0)
  have p0407 :=
    @gNeeq1 (.cv x) (synCplc (.cv j) (.cv j))
      (synCplc (synCplc (.cv n) (.cv n)) (synC1c))
  have p0408 :=
    @gImbi2d (.classEq (.cv x) (synCplc (.cv j) (.cv j)))
      (synWne (.cv x) (synCplc (synCplc (.cv n) (.cv n)) (synC1c))) syntaxFormula0000
      (synWne (synCplc (synCplc (.cv n) (.cv n)) (synC1c)) (synC0)) p0407
  have p0409 :=
    @gRalbidv (.classEq (.cv x) (synCplc (.cv j) (.cv j))) syntaxFormula0231
      syntaxFormula0001 n (synCnnc) dv_cache_0079 p0408
  have p0410 :=
    @gOrbi12d (.classEq (.cv x) (synCplc (.cv j) (.cv j))) (.classEq (.cv x) (synC0))
      (.classEq (synCplc (.cv j) (.cv j)) (synC0)) syntaxFormula0232 syntaxFormula0002
      p0406 p0409
  have p0411 :=
    @gCeqsexv syntaxFormula0235 syntaxFormula0003 x (synCplc (.cv j) (.cv j))
      dv_cache_0080 dv_cache_0081 p0405 p0410
  have p0412 :=
    @gN3bitri syntaxFormula0239 (synWex x syntaxFormula0236)
      (synWex x syntaxFormula0237) syntaxFormula0003 p0002 p0404 p0411
  have p0413 := (Nominal.biimpRefl (synWne (synCplc (.cv j) (.cv j)) (synC0)))
  have p0414 :=
    @gImbi1i (synWne (synCplc (.cv j) (.cv j)) (synC0))
      (.neg (.classEq (synCplc (.cv j) (.cv j)) (synC0))) syntaxFormula0002 p0413
  have p0415 :=
    @gN3bitr4i syntaxFormula0003
      (.imp (.neg (.classEq (synCplc (.cv j) (.cv j)) (synC0))) syntaxFormula0002)
      syntaxFormula0239 syntaxFormula0240 p0000 p0412 p0414
  have p0416 := @gEqabi syntaxFormula0240 j syntaxClass0238 dv_cache_0082 p0415
  have p0417 := @gSsetkex
  have p0418 := @gIns3kex (synCssetk) p0417
  have p0420 := @gIns2kex (synCssetk) p0417
  have p0421 := @gIns2kex (synCins2k (synCssetk)) p0420
  have p0422 := @gInex (synCins3k (synCssetk)) (synCins2k (synCssetk)) p0418 p0420
  have p0424 := @gPw1ex (synC1c) p0378
  have p0425 := @gPw1ex (synCpw1 (synC1c)) p0424
  have p0426 :=
    @gImakex (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))) p0422 p0425
  have p0427 := @gComplex syntaxClass0004 p0426
  have p0428 := @gSikex syntaxClass0005 p0427
  have p0429 := @gSikex syntaxClass0006 p0428
  have p0430 := @gSikex syntaxClass0007 p0429
  have p0431 := @gIns3kex syntaxClass0008 p0430
  have p0433 := @gSikex (synCssetk) p0417
  have p0434 := @gIns3kex (synCsik (synCssetk)) p0433
  have p0435 := @gIns2kex (synCins3k (synCsik (synCssetk))) p0434
  have p0436 := @gIns2kex (synCins2k (synCins3k (synCsik (synCssetk)))) p0435
  have p0437 := @gSikex (synCsik (synCssetk)) p0433
  have p0438 := @gSikex (synCsik (synCsik (synCssetk))) p0437
  have p0439 := @gSikex (synCsik (synCsik (synCsik (synCssetk)))) p0438
  have p0440 := @gSikex (synCsik (synCsik (synCsik (synCsik (synCssetk))))) p0439
  have p0441 :=
    @gIns3kex (synCsik (synCsik (synCsik (synCsik (synCsik (synCssetk)))))) p0440
  have p0442 := @gIns3kex (synCsik (synCsik (synCsik (synCssetk)))) p0438
  have p0443 :=
    @gIns2kex (synCins3k (synCsik (synCsik (synCsik (synCssetk))))) p0442
  have p0444 :=
    @gUnex syntaxClass0010
      (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk)))))) p0441 p0443
  have p0445 :=
    @gSymdifex (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
      syntaxClass0011 p0436 p0444
  have p0446 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0425
  have p0447 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0446
  have p0448 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0447
  have p0449 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0448
  have p0450 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0449
  have p0451 := @gImakex syntaxClass0012 syntaxClass0013 p0445 p0450
  have p0452 := @gComplex syntaxClass0014 p0451
  have p0453 := @gInex syntaxClass0009 syntaxClass0015 p0431 p0452
  have p0454 := @gInex (synCins2k (synCins2k (synCssetk))) syntaxClass0016 p0421 p0453
  have p0455 :=
    @gImakex syntaxClass0017 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0454
      p0447
  have p0456 := @gInex (synCins2k (synCssetk)) syntaxClass0018 p0420 p0455
  have p0457 := @gImakex syntaxClass0019 (synCpw1 (synCpw1 (synC1c))) p0456 p0425
  have p0458 := @gIns2kex syntaxClass0020 p0457
  have p0459 := @gSymdifex (synCins3k (synCssetk)) syntaxClass0021 p0418 p0458
  have p0460 := @gImakex syntaxClass0022 (synCpw1 (synCpw1 (synC1c))) p0459 p0425
  have p0461 := @gComplex syntaxClass0023 p0460
  have p0462 := @gSnex (synC0)
  have p0463 := @gSikex syntaxClass0004 p0426
  have p0464 := @gSikex syntaxClass0025 p0463
  have p0465 := @gSikex syntaxClass0026 p0464
  have p0466 := @gCnvkex syntaxClass0027 p0465
  have p0467 := @gIns3kex syntaxClass0028 p0466
  have p0468 := @gComplex syntaxClass0029 p0467
  have p0469 :=
    @gUnex (synCins2k (synCins3k (synCsik (synCsik (synCsik (synCssetk))))))
      syntaxClass0010 p0443 p0441
  have p0470 :=
    @gSymdifex (synCins2k (synCins2k (synCins3k (synCsik (synCssetk)))))
      syntaxClass0031 p0436 p0469
  have p0471 := @gImakex syntaxClass0032 syntaxClass0013 p0470 p0450
  have p0472 := @gComplex syntaxClass0033 p0471
  have p0473 := @gInex syntaxClass0030 syntaxClass0034 p0468 p0472
  have p0474 := @gInex (synCins2k (synCins2k (synCssetk))) syntaxClass0035 p0421 p0473
  have p0475 :=
    @gImakex syntaxClass0036 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0474
      p0447
  have p0476 := @gInex (synCins2k (synCssetk)) syntaxClass0037 p0420 p0475
  have p0477 := @gImakex syntaxClass0038 (synCpw1 (synCpw1 (synC1c))) p0476 p0425
  have p0478 := @gIns2kex syntaxClass0039 p0477
  have p0479 := @gSymdifex (synCins3k (synCssetk)) syntaxClass0040 p0418 p0478
  have p0480 := @gImakex syntaxClass0041 (synCpw1 (synCpw1 (synC1c))) p0479 p0425
  have p0481 := @gComplex syntaxClass0042 p0480
  have p0482 := @gIns2kex syntaxClass0043 p0481
  have p0483 := @gAddcexlem
  have p0484 := @gImakex syntaxClass0049 (synCpw1 (synCpw1 (synC1c))) p0483 p0425
  have p0485 := @gImagekex syntaxClass0050 p0484
  have p0486 := @gIns3kex syntaxClass0051 p0485
  have p0487 := @gInex syntaxClass0044 syntaxClass0052 p0482 p0486
  have p0488 := @gImakex syntaxClass0053 (synCpw1 (synC1c)) p0487 p0424
  have p0489 := @gIns3kex syntaxClass0054 p0488
  have p0490 := @gIdkex
  have p0491 := @gVvex
  have p0492 := @gXpkex (synCsn (synC0)) (synCvv) p0462 p0491
  have p0493 := @gDifex (synCidk) (synCxpk (synCsn (synC0)) (synCvv)) p0490 p0492
  have p0494 :=
    @gIns2kex (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv))) p0493
  have p0495 :=
    @gInex syntaxClass0055
      (synCins2k (synCdif (synCidk) (synCxpk (synCsn (synC0)) (synCvv)))) p0489
      p0494
  have p0496 := @gImakex syntaxClass0056 (synCpw1 (synC1c)) p0495 p0424
  have p0497 := @gNncex
  have p0498 := @gImakex syntaxClass0057 (synCnnc) p0496 p0497
  have p0499 := @gComplex syntaxClass0058 p0498
  have p0500 := @gUnex (synCsn (synC0)) syntaxClass0059 p0462 p0499
  have p0502 := @gXpkex syntaxClass0060 (synCvv) p0500 p0491
  have p0503 := @gInex syntaxClass0024 syntaxClass0061 p0461 p0502
  have p0505 := @gImakex syntaxClass0062 (synCvv) p0503 p0491
  have p0506 :=
    @gEqeltrri syntaxClass0238 (.cab j syntaxFormula0240) (synCvv) p0416 p0505
  exact p0506


end NFChoice.DirectNominalPrf.WPPReplay
