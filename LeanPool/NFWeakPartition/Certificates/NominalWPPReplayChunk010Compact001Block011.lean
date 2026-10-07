/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block010

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part030`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfop2lem2`. -/
@[expose]
noncomputable def gDfop2lem2 (x : Var) (y : Var) (B : Class) (dv_B_x : x ∉ B.fv)
    (dv_B_y : y ∉ B.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (.classEq (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c))))) B) (.cab x (synWrex y B
            (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))) :=
  by
  have dv_cache_0001 :
    y ∉
      ((synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                  (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                (synCdif (synCins3k (synCcompl (synCimak
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
            (synCpw1 (synCpw1 (synC1c)))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
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
  have dv_cache_0002 : y ∉ (B).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [dv_B_y, not_false_eq_true])
  have dv_cache_0003 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          (Ne.symm dv_x_y), not_false_eq_true])
  have dv_cache_0004 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0005 :
    x ∉
      ((synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                  (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                                (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c))))) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union, dv_B_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 := @gVex x
  have p0001 :=
    @gElimak y
      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                              (synCdif (synCins3k (synCcompl (synCimak
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
      B (.cv x) dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0002 := @gDfop2lem1 y x dv_cache_0004
  have p0003 :=
    @gRexbii
      (.classMem (synCopk (.cv y) (.cv x)) (synCcompl (synCimak
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
      (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))) y B p0002
  have p0004 :=
    @gBitri
      (.classMem (.cv x) (synCimak (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c))))) B))
      (synWrex y B (.classMem (synCopk (.cv y) (.cv x)) (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c)))))))
      (synWrex y B (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))
      p0001 p0003
  have p0005 :=
    @gEqabi
      (synWrex y B (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))) x
      (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
            (synCpw1 (synCpw1 (synC1c))))) B)
      dv_cache_0005 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_dfop2`. -/
@[expose]
noncomputable def gDfop2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCop A B) (synCun (synCimak (synCimagek (synCun (synCin (synCimagek
                    (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A)
          (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                    (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                                  (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                (synCpw1 (synCpw1 (synC1c))))) B))) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
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
  have dv_cache_0003 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0004 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0005 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0006 :
    y ∉
      ((synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
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
  have dv_cache_0007 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                        (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOp x y A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @gVex x
  have p0002 :=
    @gElimak y
      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      A (.cv x) dv_cache_0006 dv_cache_0002 dv_cache_0007 p0001
  have p0003 := @gDfphi2 (.cv y)
  have p0004 :=
    @gEqeq2i (synCphi (.cv y))
      (synCimak (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) (.cv y))
      (.cv x) p0003
  have p0005 := @gVex y
  have p0006 :=
    @gOpkelimagek (.cv y) (.cv x)
      (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      p0005 p0001
  have p0007 :=
    @gBitr4i (.classEq (.cv x) (synCphi (.cv y)))
      (.classEq (.cv x) (synCimak (synCun (synCin (synCimagek (synCimak (synCdif
                    (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))) (.cv y)))
      (.classMem (synCopk (.cv y) (.cv x)) (synCimagek (synCun (synCin (synCimagek
                (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
      p0004 p0006
  have p0008 :=
    @gRexbii (.classEq (.cv x) (synCphi (.cv y)))
      (.classMem (synCopk (.cv y) (.cv x)) (synCimagek (synCun (synCin (synCimagek
                (synCimak (synCdif (synCins3k (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
      y A p0007
  have p0009 :=
    @gBicomi (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))
      (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) (synCimagek (synCun (synCin
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      p0008
  have p0010 :=
    @gBitri
      (.classMem (.cv x) (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak
                    (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A))
      (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) (synCimagek (synCun (synCin
                (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      (synWrex y A (.classEq (.cv x) (synCphi (.cv y)))) p0002 p0009
  have p0011 :=
    @gEqabi (synWrex y A (.classEq (.cv x) (synCphi (.cv y)))) x
      (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A)
      dv_cache_0008 p0010
  have p0012 := @gDfop2lem2 x y B dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0013 :=
    @gUneq12i
      (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A)
      (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y)))))
      (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
            (synCpw1 (synCpw1 (synC1c))))) B)
      (.cab x (synWrex y B
          (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c))))))
      p0011 p0012
  have p0014 :=
    @gEqtr4i (synCop A B)
      (synCun (.cab x (synWrex y A (.classEq (.cv x) (synCphi (.cv y))))) (.cab x
          (synWrex y B (.classEq (.cv x) (synCun (synCphi (.cv y)) (synCsn (synC0c)))))))
      (synCun (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A) (synCimak
          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                    (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                  (synCdif (synCins3k (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c))))) B))
      p0000 p0013
  exact p0014

/-- Checked nominal proof certificate identified upstream as `g_dfproj12`. -/
@[expose]
noncomputable def gDfproj12 (A : Class) :
    Nominal.NPrf
      (.classEq (synCproj1 A) (synCimak (synCcnvk (synCimagek (synCun (synCin (synCimagek
                    (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCphi (.cv x))).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_y_ne_x,
          not_false_eq_true])
  have dv_cache_0003 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0004 :
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
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
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
  have dv_cache_0005 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((synCimak (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
                        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfProj1 x A
      dv_cache_0001
  have p0001 := @gVex x
  have p0002 := @gVex y
  have p0003 :=
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
      p0001 p0002
  have p0004 :=
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
      p0002 p0001
  have p0005 := @gDfphi2 (.cv x)
  have p0006 :=
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
      (.cv y) p0005
  have p0007 :=
    @gN3bitr4ri
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
      (.classEq (.cv y) (synCphi (.cv x))) p0003 p0004 p0006
  have p0008 :=
    @gRexbii (.classEq (.cv y) (synCphi (.cv x)))
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
      y A p0007
  have p0009 := @gRisset y (synCphi (.cv x)) A dv_cache_0002 dv_cache_0003
  have p0010 :=
    @gElimak y
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
      A (.cv x) dv_cache_0004 dv_cache_0003 dv_cache_0005 p0001
  have p0011 :=
    @gN3bitr4ri (synWrex y A (.classEq (.cv y) (synCphi (.cv x))))
      (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCimagek (synCun
                (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      (.classMem (synCphi (.cv x)) A)
      (.classMem (.cv x) (synCimak (synCcnvk (synCimagek (synCun (synCin (synCimagek
                    (synCimak (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) A))
      p0008 p0009 p0010
  have p0012 :=
    @gEqabi (.classMem (synCphi (.cv x)) A) x
      (synCimak (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) A)
      dv_cache_0006 p0011
  have p0013 :=
    @gEqtr4i (synCproj1 A) (.cab x (.classMem (synCphi (.cv x)) A))
      (synCimak (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) A)
      p0000 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part031`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfproj22`. -/
@[expose]
noncomputable def gDfproj22 (A : Class) :
    Nominal.NPrf
      (.classEq (synCproj2 A) (synCimak (synCcnvk (synCcompl (synCimak
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
                (synCpw1 (synCpw1 (synC1c)))))) A)) :=
  by
  let proofSupport : Finset Var := A.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
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
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have dv_cache_0001 : x ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0002 : x ≠ y := by
    clear dv_cache_0001
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0003 :
    y ∉
      ((synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                  (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                                (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
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
  have dv_cache_0004 : y ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0005 : y ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_x, not_false_eq_true])
  have dv_cache_0006 : y ∉ ((synCun (synCphi (.cv x)) (synCsn (synC0c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
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
  have dv_cache_0007 :
    x ∉
      ((synCimak (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                (synCpw1 (synCpw1 (synC1c)))))) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfProj2 x A
      dv_cache_0001
  have p0001 := @gVex y
  have p0002 := @gVex x
  have p0003 :=
    @gOpkelcnvk (.cv y) (.cv x)
      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                              (synCdif (synCins3k (synCcompl (synCimak
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
      p0001 p0002
  have p0004 := @gDfop2lem1 x y dv_cache_0002
  have p0005 :=
    @gBitri
      (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c)))))))
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
      (.classEq (.cv y) (synCun (synCphi (.cv x)) (synCsn (synC0c)))) p0003 p0004
  have p0006 :=
    @gRexbii
      (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c)))))))
      (.classEq (.cv y) (synCun (synCphi (.cv x)) (synCsn (synC0c)))) y A p0005
  have p0007 :=
    @gElimak y
      (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
      A (.cv x) dv_cache_0003 dv_cache_0004 dv_cache_0005 p0002
  have p0008 :=
    @gRisset y (synCun (synCphi (.cv x)) (synCsn (synC0c))) A dv_cache_0006
      dv_cache_0004
  have p0009 :=
    @gN3bitr4i
      (synWrex y A (.classMem (synCopk (.cv y) (.cv x)) (synCcnvk (synCcompl (synCimak
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
                (synCpw1 (synCpw1 (synC1c))))))))
      (synWrex y A (.classEq (.cv y) (synCun (synCphi (.cv x)) (synCsn (synC0c)))))
      (.classMem (.cv x) (synCimak (synCcnvk (synCcompl (synCimak
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
                (synCpw1 (synCpw1 (synC1c)))))) A))
      (.classMem (synCun (synCphi (.cv x)) (synCsn (synC0c))) A) p0006 p0007 p0008
  have p0010 :=
    @gEqabi (.classMem (synCun (synCphi (.cv x)) (synCsn (synC0c))) A) x
      (synCimak (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c)))))) A)
      dv_cache_0007 p0009
  have p0011 :=
    @gEqtr4i (synCproj2 A)
      (.cab x (.classMem (synCun (synCphi (.cv x)) (synCsn (synC0c))) A))
      (synCimak (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c)))))) A)
      p0000 p0010
  exact p0011

/-- Checked nominal proof certificate identified upstream as `g_opeq1`. -/
@[expose]
noncomputable def gOpeq1 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCop A C) (synCop B C))) :=
  by
  have p0000 :=
    @gImakeq2 A B
      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
  have p0001 :=
    @gUneq1d (.classEq A B)
      (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A)
      (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) B)
      (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
            (synCpw1 (synCpw1 (synC1c))))) C)
      p0000
  have p0002 := @gDfop2 A C
  have p0003 := @gDfop2 B C
  have p0004 :=
    @gN3eqtr4g (.classEq A B)
      (synCun (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A) (synCimak
          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                    (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                  (synCdif (synCins3k (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c))))) C))
      (synCun (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) B) (synCimak
          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                    (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                  (synCdif (synCins3k (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c))))) C))
      (synCop A C) (synCop B C) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_opeq2`. -/
@[expose]
noncomputable def gOpeq2 (A : Class) (B : Class) (C : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCop C A) (synCop C B))) :=
  by
  have p0000 :=
    @gImakeq2 A B
      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                              (synCdif (synCins3k (synCcompl (synCimak
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
  have p0001 :=
    @gUneq2d (.classEq A B)
      (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
            (synCpw1 (synCpw1 (synC1c))))) A)
      (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
            (synCpw1 (synCpw1 (synC1c))))) B)
      (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) C)
      p0000
  have p0002 := @gDfop2 C A
  have p0003 := @gDfop2 C B
  have p0004 :=
    @gN3eqtr4g (.classEq A B)
      (synCun (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) C) (synCimak
          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                    (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                  (synCdif (synCins3k (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c))))) A))
      (synCun (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) C) (synCimak
          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                    (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                  (synCdif (synCins3k (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c))))) B))
      (synCop C A) (synCop C B) p0001 p0002 p0003
  exact p0004

/-- Checked nominal proof certificate identified upstream as `g_opeq12`. -/
@[expose]
noncomputable def gOpeq12 (A : Class) (B : Class) (C : Class) (D : Class) :
    Nominal.NPrf
      (.imp (synWa (.classEq A B) (.classEq C D)) (.classEq (synCop A C) (synCop B D))) :=
  by
  have p0000 := @gOpeq1 A B C
  have p0001 := @gOpeq2 C D B
  have p0002 :=
    @gSylan9eq (.classEq A B) (.classEq C D) (synCop A C) (synCop B C) (synCop B D)
      p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_opeq1i`. -/
@[expose]
noncomputable def gOpeq1i (A : Class) (B : Class) (C : Class)
    (hyp_opeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCop A C) (synCop B C)) :=
  by
  have p0000 := @gOpeq1 A B C
  have p0001 := Nominal.mp hyp_opeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opeq2i`. -/
@[expose]
noncomputable def gOpeq2i (A : Class) (B : Class) (C : Class)
    (hyp_opeq1i_1 : Nominal.NPrf (.classEq A B)) :
    Nominal.NPrf (.classEq (synCop C A) (synCop C B)) :=
  by
  have p0000 := @gOpeq2 A B C
  have p0001 := Nominal.mp hyp_opeq1i_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opeq12i`. -/
@[expose]
noncomputable def gOpeq12i (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_opeq1i_1 : Nominal.NPrf (.classEq A B))
    (hyp_opeq12i_2 : Nominal.NPrf (.classEq C D)) :
    Nominal.NPrf (.classEq (synCop A C) (synCop B D)) :=
  by
  have p0000 := @gOpeq1i A B C hyp_opeq1i_1
  have p0001 := @gOpeq2i C D B hyp_opeq12i_2
  have p0002 := @gEqtri (synCop A C) (synCop B C) (synCop B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_opeq1d`. -/
@[expose]
noncomputable def gOpeq1d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_opeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCop A C) (synCop B C))) :=
  by
  have p0000 := @gOpeq1 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCop A C) (synCop B C)) hyp_opeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opeq2d`. -/
@[expose]
noncomputable def gOpeq2d (ph : Wff) (A : Class) (B : Class) (C : Class)
    (hyp_opeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B))) :
    Nominal.NPrf (.imp ph (.classEq (synCop C A) (synCop C B))) :=
  by
  have p0000 := @gOpeq2 A B C
  have p0001 :=
    @gSyl ph (.classEq A B) (.classEq (synCop C A) (synCop C B)) hyp_opeq1d_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_opeq12d`. -/
@[expose]
noncomputable def gOpeq12d (ph : Wff) (A : Class) (B : Class) (C : Class) (D : Class)
    (hyp_opeq1d_1 : Nominal.NPrf (.imp ph (.classEq A B)))
    (hyp_opeq12d_2 : Nominal.NPrf (.imp ph (.classEq C D))) :
    Nominal.NPrf (.imp ph (.classEq (synCop A C) (synCop B D))) :=
  by
  have p0000 := @gOpeq1d ph A B C hyp_opeq1d_1
  have p0001 := @gOpeq2d ph C D B hyp_opeq12d_2
  have p0002 := @gEqtrd ph (synCop A C) (synCop B C) (synCop B D) p0000 p0001
  exact p0002

/-- Checked nominal proof certificate identified upstream as `g_opexg`. -/
@[expose]
noncomputable def gOpexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCop A B) (synCvv))) :=
  by
  have p0000 := @gDfop2 A B
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
    @gImagekex
      (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      p0017
  have p0019 :=
    @gImakexg
      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      A (synCvv) V
  have p0020 :=
    @gMpan
      (.classMem (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) (synCvv))
      (.classMem A V)
      (.classMem (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A) (synCvv))
      p0018 p0019
  have p0021 := @gSsetkex
  have p0022 := @gIns2kex (synCssetk) p0021
  have p0023 :=
    @gCnvkex
      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      p0018
  have p0025 :=
    @gCokex
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
      (synCssetk) p0023 p0021
  have p0026 := @gSnex (synCsn (synC0c))
  have p0028 := @gXpkex (synCsn (synCsn (synC0c))) (synCvv) p0026 p0008
  have p0029 :=
    @gUnex
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
      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)) p0025 p0028
  have p0030 :=
    @gIns3kex
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
      p0029
  have p0031 :=
    @gSymdifex (synCins2k (synCssetk))
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
      p0022 p0030
  have p0032 :=
    @gImakex
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
      (synCpw1 (synCpw1 (synC1c))) p0031 p0004
  have p0033 :=
    @gComplex
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
      p0032
  have p0034 :=
    @gImakexg
      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                              (synCdif (synCins3k (synCcompl (synCimak
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
      B (synCvv) W
  have p0035 :=
    @gMpan
      (.classMem (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
            (synCpw1 (synCpw1 (synC1c))))) (synCvv))
      (.classMem B W)
      (.classMem (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c))))) B) (synCvv))
      p0033 p0034
  have p0036 :=
    @gUnexg
      (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A)
      (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
            (synCpw1 (synCpw1 (synC1c))))) B)
      (synCvv) (synCvv)
  have p0037 :=
    @gSyl2an (.classMem A V)
      (.classMem (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A) (synCvv))
      (.classMem (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c))))) B) (synCvv))
      (.classMem (synCun (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A)
          (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                    (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                                  (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                (synCpw1 (synCpw1 (synC1c))))) B)) (synCvv))
      (.classMem B W) p0020 p0035 p0036
  have p0038 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCop A B)
      (synCun (synCimak (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))) A) (synCimak
          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                    (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                  (synCdif (synCins3k (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synC1c))))) B))
      (synCvv) p0000 p0037
  exact p0038

/-- Checked nominal proof certificate identified upstream as `g_opex`. -/
@[expose]
noncomputable def gOpex (A : Class) (B : Class)
    (hyp_opex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_opex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCop A B) (synCvv)) :=
  by
  have p0000 := @gOpexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCop A B) (synCvv)) hyp_opex_1 hyp_opex_2 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_proj1eq`. -/
@[expose]
noncomputable def gProj1eq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCproj1 A) (synCproj1 B))) :=
  by
  have p0000 :=
    @gImakeq2 A B
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
  have p0001 := @gDfproj12 A
  have p0002 := @gDfproj12 B
  have p0003 :=
    @gN3eqtr4g (.classEq A B)
      (synCimak (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) A)
      (synCimak (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) B)
      (synCproj1 A) (synCproj1 B) p0000 p0001 p0002
  exact p0003

/-- Checked nominal proof certificate identified upstream as `g_proj2eq`. -/
@[expose]
noncomputable def gProj2eq (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq A B) (.classEq (synCproj2 A) (synCproj2 B))) :=
  by
  have p0000 :=
    @gImakeq2 A B
      (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
  have p0001 := @gDfproj22 A
  have p0002 := @gDfproj22 B
  have p0003 :=
    @gN3eqtr4g (.classEq A B)
      (synCimak (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c)))))) A)
      (synCimak (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c)))))) B)
      (synCproj2 A) (synCproj2 B) p0000 p0001 p0002
  exact p0003


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part032`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_proj1exg`. -/
@[expose]
noncomputable def gProj1exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCproj1 A) (synCvv))) :=
  by
  have p0000 := @gDfproj12 A
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
    @gImagekex
      (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      p0017
  have p0019 :=
    @gCnvkex
      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      p0018
  have p0020 :=
    @gImakexg
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
      A (synCvv) V
  have p0021 :=
    @gMpan
      (.classMem (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCvv))
      (.classMem A V)
      (.classMem (synCimak (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) A)
        (synCvv))
      p0019 p0020
  have p0022 :=
    @gSyl5eqel (.classMem A V) (synCproj1 A)
      (synCimak (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) A)
      (synCvv) p0000 p0021
  exact p0022

/-- Checked nominal proof certificate identified upstream as `g_proj2exg`. -/
@[expose]
noncomputable def gProj2exg (A : Class) (V : Class) :
    Nominal.NPrf (.imp (.classMem A V) (.classMem (synCproj2 A) (synCvv))) :=
  by
  have p0000 := @gDfproj22 A
  have p0001 := @gSsetkex
  have p0002 := @gIns2kex (synCssetk) p0001
  have p0003 := @gAddcexlem
  have p0004 := @gN1cex
  have p0005 := @gPw1ex (synC1c) p0004
  have p0006 := @gPw1ex (synCpw1 (synC1c)) p0005
  have p0007 :=
    @gImakex
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synC1c))) p0003 p0006
  have p0008 :=
    @gImagekex
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0007
  have p0009 := @gNncex
  have p0010 := @gVvex
  have p0011 := @gXpkex (synCnnc) (synCvv) p0009 p0010
  have p0012 :=
    @gInex
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCxpk (synCnnc) (synCvv)) p0008 p0011
  have p0013 := @gIdkex
  have p0015 := @gComplex (synCnnc) p0009
  have p0017 := @gXpkex (synCcompl (synCnnc)) (synCvv) p0015 p0010
  have p0018 :=
    @gInex (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)) p0013 p0017
  have p0019 :=
    @gUnex
      (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))) p0012 p0018
  have p0020 :=
    @gImagekex
      (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                      (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                    (synCun (synCins2k (synCins3k (synCssetk)))
                      (synCins3k (synCsik (synCsik (synCssetk))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
      p0019
  have p0021 :=
    @gCnvkex
      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      p0020
  have p0023 :=
    @gCokex
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
      (synCssetk) p0021 p0001
  have p0024 := @gSnex (synCsn (synC0c))
  have p0026 := @gXpkex (synCsn (synCsn (synC0c))) (synCvv) p0024 p0010
  have p0027 :=
    @gUnex
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
      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)) p0023 p0026
  have p0028 :=
    @gIns3kex
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
      p0027
  have p0029 :=
    @gSymdifex (synCins2k (synCssetk))
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
      p0002 p0028
  have p0030 :=
    @gImakex
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
      (synCpw1 (synCpw1 (synC1c))) p0029 p0006
  have p0031 :=
    @gComplex
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
      p0030
  have p0032 :=
    @gCnvkex
      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                              (synCdif (synCins3k (synCcompl (synCimak
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
      p0031
  have p0033 :=
    @gImakexg
      (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
      A (synCvv) V
  have p0034 :=
    @gMpan
      (.classMem (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c)))))) (synCvv))
      (.classMem A V)
      (.classMem (synCimak (synCcnvk (synCcompl (synCimak
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
                (synCpw1 (synCpw1 (synC1c)))))) A) (synCvv))
      p0032 p0033
  have p0035 :=
    @gSyl5eqel (.classMem A V) (synCproj2 A)
      (synCimak (synCcnvk (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
                              (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                        (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                    (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
              (synCpw1 (synCpw1 (synC1c)))))) A)
      (synCvv) p0000 p0034
  exact p0035

/-- Checked nominal proof certificate identified upstream as `g_proj1ex`. -/
@[expose]
noncomputable def gProj1ex (A : Class)
    (hyp_projex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCproj1 A) (synCvv)) :=
  by
  have p0000 := @gProj1exg A (synCvv)
  have p0001 := Nominal.mp hyp_projex_1 p0000
  exact p0001

/-- Checked nominal proof certificate identified upstream as `g_proj2ex`. -/
@[expose]
noncomputable def gProj2ex (A : Class)
    (hyp_projex_1 : Nominal.NPrf (.classMem A (synCvv))) :
    Nominal.NPrf (.classMem (synCproj2 A) (synCvv)) :=
  by
  have p0000 := @gProj2exg A (synCvv)
  have p0001 := Nominal.mp hyp_projex_1 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part033`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_phi11lem1`. -/
@[expose]
noncomputable def gPhi11lem1 (A : Class) (B : Class) :
    Nominal.NPrf (.imp (.classEq (synCphi A) (synCphi B)) (synWss A B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let z : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let x : Var := freshVar proofSupport 2
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_z_not_B : z ∉ B.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (Finset.mem_union_left _ (h))
  have fresh_y_not_B : y ∉ B.fv := by
    intro h
    exact fresh_y (Finset.mem_union_right _ (h))
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (Finset.mem_union_left _ (h))
  have fresh_x_not_B : x ∉ B.fv := by
    intro h
    exact fresh_x (Finset.mem_union_right _ (h))
  have fresh_z_ne_y : z ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_ne_x : z ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ∉ ((Class.cv z)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_y_ne_z, not_false_eq_true])
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
  have dv_cache_0003 :
    y ∉
      ((Wff.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0004 : y ∉ ((Wff.classEq (.cv x) (synCplc (.cv z) (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, compact_fv_not_mem_empty,
          or_false, not_false_eq_true])
  have dv_cache_0005 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0006 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0007 : x ∉ ((synCplc (.cv z) (synC1c))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_x_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((synWrex y A (.classEq (synCplc (.cv z) (synC1c))
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
              (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_z,
          fresh_x_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
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
  have dv_cache_0010 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0011 :
    x ∉
      ((synWrex y B (.classEq (synCplc (.cv z) (synC1c))
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
              (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_z,
          fresh_x_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0012 : y ∉ ((Wff.classMem (.cv z) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, fresh_y_not_B, or_false, not_false_eq_true])
  have dv_cache_0013 : y ∉ ((Wff.classMem (.cv z) (synCnnc))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0014 :
    y ∉
      ((Wff.classEq (.cv z) (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c))
            (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0015 : y ∉ ((Wff.objEq x z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_objEq, Finset.mem_insert,
          Finset.mem_singleton, fresh_y_ne_x, fresh_y_ne_z, or_false, not_false_eq_true])
  have dv_cache_0016 : x ∉ ((Class.cv z)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_z, not_false_eq_true])
  have dv_cache_0017 :
    x ∉
      ((synWrex y A (.classEq (.cv z)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
              (.cv y))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_z,
          fresh_x_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0018 :
    x ∉
      ((synWrex y B (.classEq (.cv z)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
              (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
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
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_B, fresh_x_ne_z,
          fresh_x_ne_y, compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have dv_cache_0019 : y ∉ ((Wff.neg (.classMem (.cv z) (synCnnc)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_neg,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_z, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have dv_cache_0020 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0021 : z ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_B, not_false_eq_true])
  have dv_cache_0022 : z ∉ ((Wff.classEq (synCphi A) (synCphi B))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cphi, Finset.mem_union,
          fresh_z_not_A, fresh_z_not_B, or_false, not_false_eq_true])
  have p0000 :=
    @gIftrue (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z)
  have p0001 :=
    @gEqcomd (.classMem (.cv z) (synCnnc))
      (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z))
      (synCplc (.cv z) (synC1c)) p0000
  have p0002 := @gEleq1 (.cv y) (.cv z) (synCnnc)
  have p0003 := @gAddceq1 (.cv y) (.cv z) (synC1c)
  have p0004 := @gId (.objEq y z)
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq y z)
        (synWb (.classMem (.cv y) (synCnnc)) (.classMem (.cv z) (synCnnc)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCnnc synCint synWa synC0c synCsn synC0 synCdif synCin
          synCcompl synCnin synWnan synCvv synWral synCplc synWrex synWex synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0002
  have p0005_e01_recanon :
    Nominal.NPrf
      (.imp (.objEq y z)
        (.classEq (synCplc (.cv y) (synC1c)) (synCplc (.cv z) (synC1c)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCplc synWrex synWex synWa synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0003
  have p0005_e02_recanon : Nominal.NPrf (.imp (.objEq y z) (.classEq (.cv y) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0004
  have p0005 :=
    @gIfbieq12d (.objEq y z) (.classMem (.cv y) (synCnnc))
      (.classMem (.cv z) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)
      (synCplc (.cv z) (synC1c)) (.cv z) p0005_e00_recanon p0005_e01_recanon
      p0005_e02_recanon
  have p0006 :=
    @gEqeq2d (.objEq y z)
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z))
      (synCplc (.cv z) (synC1c)) p0005
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv z)) (synWb (.classEq (synCplc (.cv z) (synC1c))
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
          (.classEq (synCplc (.cv z) (synC1c))
            (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCplc synWrex synWex synWa synC1c synCif synWo synCnnc
          synCint
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gRspcev
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z)))
      y (.cv z) A dv_cache_0001 dv_cache_0002 dv_cache_0003 p0007_e00_recanon
  have p0008 :=
    @gSylan2 (.classMem (.cv z) (synCnnc)) (.classMem (.cv z) A)
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z)))
      (synWrex y A (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      p0001 p0007
  have p0009 :=
    @gAncoms (.classMem (.cv z) A) (.classMem (.cv z) (synCnnc))
      (synWrex y A (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      p0008
  have p0010 := @gVex z
  have p0011 := @gN1cex
  have p0012 := @gAddcex (.cv z) (synC1c) p0010 p0011
  have p0013 :=
    @gEqeq1 (.cv x) (synCplc (.cv z) (synC1c))
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
  have p0014 :=
    @gRexbidv (.classEq (.cv x) (synCplc (.cv z) (synC1c)))
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      y A dv_cache_0004 p0013
  have p0015 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPhi y x A
      dv_cache_0002 dv_cache_0005 dv_cache_0006
  have p0016 :=
    @gElab2
      (synWrex y A (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synWrex y A (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      x (synCplc (.cv z) (synC1c)) (synCphi A) dv_cache_0007 dv_cache_0008 p0012 p0014
      p0015
  have p0017 :=
    @gSylibr (synWa (.classMem (.cv z) (synCnnc)) (.classMem (.cv z) A))
      (synWrex y A (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.classMem (synCplc (.cv z) (synC1c)) (synCphi A)) p0009 p0016
  have p0018 := @gEleq2 (synCphi A) (synCphi B) (synCplc (.cv z) (synC1c))
  have p0019 :=
    @gBiimpac (.classEq (synCphi A) (synCphi B))
      (.classMem (synCplc (.cv z) (synC1c)) (synCphi A))
      (.classMem (synCplc (.cv z) (synC1c)) (synCphi B)) p0018
  have p0020 :=
    @gRexbidv (.classEq (.cv x) (synCplc (.cv z) (synC1c)))
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      y B dv_cache_0004 p0013
  have p0021 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPhi y x B
      dv_cache_0009 dv_cache_0010 dv_cache_0006
  have p0022 :=
    @gElab2
      (synWrex y B (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synWrex y B (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      x (synCplc (.cv z) (synC1c)) (synCphi B) dv_cache_0007 dv_cache_0011 p0012 p0020
      p0021
  have p0023 :=
    @gIffalse (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)
  have p0024 :=
    @gEqeq2d (.neg (.classMem (.cv y) (synCnnc)))
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (.cv y) (synCplc (.cv z) (synC1c)) p0023
  have p0025 :=
    @gBiimpac (.neg (.classMem (.cv y) (synCnnc)))
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (synCplc (.cv z) (synC1c)) (.cv y)) p0024
  have p0026 := @gPeano2 (.cv z)
  have p0027 := @gEleq1 (synCplc (.cv z) (synC1c)) (.cv y) (synCnnc)
  have p0028 :=
    @gSyl5ibcom (.classMem (.cv z) (synCnnc))
      (.classMem (synCplc (.cv z) (synC1c)) (synCnnc))
      (.classEq (synCplc (.cv z) (synC1c)) (.cv y)) (.classMem (.cv y) (synCnnc)) p0026
      p0027
  have p0029 :=
    @gSyl5
      (synWa (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
        (.neg (.classMem (.cv y) (synCnnc))))
      (.classEq (synCplc (.cv z) (synC1c)) (.cv y)) (.classMem (.cv z) (synCnnc))
      (.classMem (.cv y) (synCnnc)) p0025 p0028
  have p0030 :=
    @gExpdimp (.classMem (.cv z) (synCnnc))
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.neg (.classMem (.cv y) (synCnnc))) (.classMem (.cv y) (synCnnc)) p0029
  have p0031 :=
    @gPm218d
      (synWa (.classMem (.cv z) (synCnnc)) (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.classMem (.cv y) (synCnnc)) p0030
  have p0032 :=
    @gSimpl (.classMem (.cv z) (synCnnc))
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
  have p0033 :=
    @gSimpr (.classMem (.cv z) (synCnnc))
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
  have p0034 :=
    @gIftrue (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)
  have p0035 :=
    @gSyl
      (synWa (.classMem (.cv z) (synCnnc)) (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.classMem (.cv y) (synCnnc))
      (.classEq (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
        (synCplc (.cv y) (synC1c)))
      p0031 p0034
  have p0036 :=
    @gEqtr2d
      (synWa (.classMem (.cv z) (synCnnc)) (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synCplc (.cv z) (synC1c))
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (synCplc (.cv y) (synC1c)) p0033 p0035
  have p0037 := @gPeano4 (.cv y) (.cv z)
  have p0038_e03_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem (.cv y) (synCnnc)) (.classMem (.cv z) (synCnnc))
          (.classEq (synCplc (.cv y) (synC1c)) (synCplc (.cv z) (synC1c)))) (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCnnc synCint synCplc synWrex synWex synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0037
  have p0038 :=
    @gSyl3anc
      (synWa (.classMem (.cv z) (synCnnc)) (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.classMem (.cv y) (synCnnc)) (.classMem (.cv z) (synCnnc))
      (.classEq (synCplc (.cv y) (synC1c)) (synCplc (.cv z) (synC1c))) (.objEq y z)
      p0031 p0032 p0036 p0038_e03_recanon
  have p0039 :=
    @gN3adant2 (.classMem (.cv z) (synCnnc))
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.objEq y z) (.classMem (.cv y) B) p0038
  have p0040 :=
    @gSimp2 (.classMem (.cv z) (synCnnc)) (.classMem (.cv y) B)
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
  have p0041_e00_recanon :
    Nominal.NPrf
      (.imp (synW3a (.classMem (.cv z) (synCnnc)) (.classMem (.cv y) B)
          (.classEq (synCplc (.cv z) (synC1c))
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
        (.classEq (.cv y) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synW3a synWa synCnnc synCint synCplc synWrex synWex synC1c synCif
          synWo
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0039
  have p0041 :=
    @gEqeltrrd
      (synW3a (.classMem (.cv z) (synCnnc)) (.classMem (.cv y) B)
        (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.cv y) (.cv z) B p0041_e00_recanon p0040
  have p0042 :=
    @gN3expia (.classMem (.cv z) (synCnnc)) (.classMem (.cv y) B)
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classMem (.cv z) B) p0041
  have p0043 :=
    @gRexlimdva (.classMem (.cv z) (synCnnc))
      (.classEq (synCplc (.cv z) (synC1c))
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classMem (.cv z) B) y B dv_cache_0012 dv_cache_0013 p0042
  have p0044 :=
    @gSyl5bi (.classMem (synCplc (.cv z) (synC1c)) (synCphi B))
      (synWrex y B (.classEq (synCplc (.cv z) (synC1c))
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.classMem (.cv z) (synCnnc)) (.classMem (.cv z) B) p0022 p0043
  have p0045 :=
    @gSyl5
      (synWa (.classMem (synCplc (.cv z) (synC1c)) (synCphi A))
        (.classEq (synCphi A) (synCphi B)))
      (.classMem (synCplc (.cv z) (synC1c)) (synCphi B)) (.classMem (.cv z) (synCnnc))
      (.classMem (.cv z) B) p0019 p0044
  have p0046 :=
    @gExp3a (.classMem (.cv z) (synCnnc))
      (.classMem (synCplc (.cv z) (synC1c)) (synCphi A))
      (.classEq (synCphi A) (synCphi B)) (.classMem (.cv z) B) p0045
  have p0047 :=
    @gAdantr (.classMem (.cv z) (synCnnc))
      (.imp (.classMem (synCplc (.cv z) (synC1c)) (synCphi A))
        (.imp (.classEq (synCphi A) (synCphi B)) (.classMem (.cv z) B)))
      (.classMem (.cv z) A) p0046
  have p0048 :=
    @gMpd (synWa (.classMem (.cv z) (synCnnc)) (.classMem (.cv z) A))
      (.classMem (synCplc (.cv z) (synC1c)) (synCphi A))
      (.imp (.classEq (synCphi A) (synCphi B)) (.classMem (.cv z) B)) p0017 p0047
  have p0049 :=
    @gIffalse (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z)
  have p0050 :=
    @gEqcomd (.neg (.classMem (.cv z) (synCnnc)))
      (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z))
      (.cv z) p0049
  have p0051 :=
    @gEqeq2d (.objEq y z)
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z))
      (.cv z) p0005
  have p0052_e00_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv y) (.cv z)) (synWb (.classEq (.cv z)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
          (.classEq (.cv z) (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c))
              (.cv z))))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCif synWo synWa synCnnc synCint synCplc synWrex synWex
          synC1c
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0051
  have p0052 :=
    @gRspcev
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (.cv z)
        (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z)))
      y (.cv z) A dv_cache_0001 dv_cache_0002 dv_cache_0014 p0052_e00_recanon
  have p0053 :=
    @gSylan2 (.neg (.classMem (.cv z) (synCnnc))) (.classMem (.cv z) A)
      (.classEq (.cv z)
        (synCif (.classMem (.cv z) (synCnnc)) (synCplc (.cv z) (synC1c)) (.cv z)))
      (synWrex y A (.classEq (.cv z)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      p0050 p0052
  have p0054 :=
    @gAncoms (.classMem (.cv z) A) (.neg (.classMem (.cv z) (synCnnc)))
      (synWrex y A (.classEq (.cv z)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      p0053
  have p0055 :=
    @gEqeq1 (.cv x) (.cv z)
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
  have p0056_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (synWb (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
          (.classEq (.cv z) (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
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
      p0055
  have p0056 :=
    @gRexbidv (.objEq x z)
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      y A dv_cache_0015 p0056_e00_recanon
  have p0057_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (synWb (synWrex y A (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
          (synWrex y A (.classEq (.cv z)
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
      p0056
  have p0057 :=
    @gElab2
      (synWrex y A (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synWrex y A (.classEq (.cv z)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      x (.cv z) (synCphi A) dv_cache_0016 dv_cache_0017 p0010 p0057_e01_recanon p0015
  have p0058 :=
    @gSylibr (synWa (.neg (.classMem (.cv z) (synCnnc))) (.classMem (.cv z) A))
      (synWrex y A (.classEq (.cv z)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.classMem (.cv z) (synCphi A)) p0054 p0057
  have p0059 := @gEleq2 (synCphi A) (synCphi B) (.cv z)
  have p0060 :=
    @gBiimpac (.classEq (synCphi A) (synCphi B)) (.classMem (.cv z) (synCphi A))
      (.classMem (.cv z) (synCphi B)) p0059
  have p0061_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq x z) (synWb (.classEq (.cv x)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
          (.classEq (.cv z) (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
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
      p0055
  have p0061 :=
    @gRexbidv (.objEq x z)
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      y B dv_cache_0015 p0061_e00_recanon
  have p0062_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv x) (.cv z)) (synWb (synWrex y B (.classEq (.cv x)
              (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
          (synWrex y B (.classEq (.cv z)
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
      p0061
  have p0062 :=
    @gElab2
      (synWrex y B (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synWrex y B (.classEq (.cv z)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      x (.cv z) (synCphi B) dv_cache_0016 dv_cache_0018 p0010 p0062_e01_recanon p0021
  have p0063 :=
    @gSimpr (.neg (.classMem (.cv z) (synCnnc)))
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
  have p0064 :=
    @gEqeq2d (.classMem (.cv y) (synCnnc))
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (synCplc (.cv y) (synC1c)) (.cv z) p0034
  have p0065 := @gPeano2 (.cv y)
  have p0066 := @gEleq1a (synCplc (.cv y) (synC1c)) (synCnnc) (.cv z)
  have p0067 :=
    @gSyl (.classMem (.cv y) (synCnnc))
      (.classMem (synCplc (.cv y) (synC1c)) (synCnnc))
      (.imp (.classEq (.cv z) (synCplc (.cv y) (synC1c))) (.classMem (.cv z) (synCnnc)))
      p0065 p0066
  have p0068 :=
    @gSylbid (.classMem (.cv y) (synCnnc))
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (.cv z) (synCplc (.cv y) (synC1c))) (.classMem (.cv z) (synCnnc)) p0064
      p0067
  have p0069 :=
    @gCom12 (.classMem (.cv y) (synCnnc))
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classMem (.cv z) (synCnnc)) p0068
  have p0070 :=
    @gCon3d
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classMem (.cv y) (synCnnc)) (.classMem (.cv z) (synCnnc)) p0069
  have p0071 :=
    @gImpcom
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.neg (.classMem (.cv z) (synCnnc))) (.neg (.classMem (.cv y) (synCnnc))) p0070
  have p0072 :=
    @gSyl
      (synWa (.neg (.classMem (.cv z) (synCnnc))) (.classEq (.cv z)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.neg (.classMem (.cv y) (synCnnc)))
      (.classEq (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
        (.cv y))
      p0071 p0023
  have p0073 :=
    @gEqtr2d
      (synWa (.neg (.classMem (.cv z) (synCnnc))) (.classEq (.cv z)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.cv z)
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (.cv y) p0063 p0072
  have p0074_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (.neg (.classMem (.cv z) (synCnnc))) (.classEq (.cv z)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
        (.objEq y z)) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCnnc synCint synCif synWo synCplc synWrex synWex synC1c
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _)
      p0073
  have p0074 :=
    @gAdantlr (.neg (.classMem (.cv z) (synCnnc)))
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.objEq y z) (.classMem (.cv y) B) p0074_e00_recanon
  have p0075 :=
    @gSimplr (.neg (.classMem (.cv z) (synCnnc))) (.classMem (.cv y) B)
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
  have p0076_e00_recanon :
    Nominal.NPrf
      (.imp (synWa (synWa (.neg (.classMem (.cv z) (synCnnc))) (.classMem (.cv y) B))
          (.classEq (.cv z) (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
              (.cv y)))) (.classEq (.cv y) (.cv z))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWa synCif synWo synCnnc synCint synCplc synWrex synWex synC1c
        simp (config :=
          {
            failIfUnchanged :=
              false }) only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _)
      p0074
  have p0076 :=
    @gEqeltrrd
      (synWa (synWa (.neg (.classMem (.cv z) (synCnnc))) (.classMem (.cv y) B))
        (.classEq (.cv z)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.cv y) (.cv z) B p0076_e00_recanon p0075
  have p0077 :=
    @gEx (synWa (.neg (.classMem (.cv z) (synCnnc))) (.classMem (.cv y) B))
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classMem (.cv z) B) p0076
  have p0078 :=
    @gRexlimdva (.neg (.classMem (.cv z) (synCnnc)))
      (.classEq (.cv z)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classMem (.cv z) B) y B dv_cache_0012 dv_cache_0019 p0077
  have p0079 :=
    @gSyl5bi (.classMem (.cv z) (synCphi B))
      (synWrex y B (.classEq (.cv z)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.neg (.classMem (.cv z) (synCnnc))) (.classMem (.cv z) B) p0062 p0078
  have p0080 :=
    @gSyl5 (synWa (.classMem (.cv z) (synCphi A)) (.classEq (synCphi A) (synCphi B)))
      (.classMem (.cv z) (synCphi B)) (.neg (.classMem (.cv z) (synCnnc)))
      (.classMem (.cv z) B) p0060 p0079
  have p0081 :=
    @gExp3a (.neg (.classMem (.cv z) (synCnnc))) (.classMem (.cv z) (synCphi A))
      (.classEq (synCphi A) (synCphi B)) (.classMem (.cv z) B) p0080
  have p0082 :=
    @gAdantr (.neg (.classMem (.cv z) (synCnnc)))
      (.imp (.classMem (.cv z) (synCphi A))
        (.imp (.classEq (synCphi A) (synCphi B)) (.classMem (.cv z) B)))
      (.classMem (.cv z) A) p0081
  have p0083 :=
    @gMpd (synWa (.neg (.classMem (.cv z) (synCnnc))) (.classMem (.cv z) A))
      (.classMem (.cv z) (synCphi A))
      (.imp (.classEq (synCphi A) (synCphi B)) (.classMem (.cv z) B)) p0058 p0082
  have p0084 :=
    @gPm261ian (.classMem (.cv z) (synCnnc)) (.classMem (.cv z) A)
      (.imp (.classEq (synCphi A) (synCphi B)) (.classMem (.cv z) B)) p0048 p0083
  have p0085 :=
    @gCom12 (.classMem (.cv z) A) (.classEq (synCphi A) (synCphi B))
      (.classMem (.cv z) B) p0084
  have p0086 :=
    @gSsrdv (.classEq (synCphi A) (synCphi B)) z A B dv_cache_0020 dv_cache_0021
      dv_cache_0022 p0085
  exact p0086

/-- Checked nominal proof certificate identified upstream as `g_phi11`. -/
@[expose]
noncomputable def gPhi11 (A : Class) (B : Class) :
    Nominal.NPrf (synWb (.classEq A B) (.classEq (synCphi A) (synCphi B))) :=
  by
  have p0000 := @gPhieq A B
  have p0001 := @gPhi11lem1 A B
  have p0002 := @gPhi11lem1 B A
  have p0003 := @gEqcoms (synWss B A) (synCphi B) (synCphi A) p0002
  have p0004 := @gEqssd (.classEq (synCphi A) (synCphi B)) A B p0001 p0003
  have p0005 := @gImpbii (.classEq A B) (.classEq (synCphi A) (synCphi B)) p0000 p0004
  exact p0005

/-- Checked nominal proof certificate identified upstream as `g_n_0cnelphi`. -/
@[expose]
noncomputable def gN0cnelphi (A : Class) :
    Nominal.NPrf (.neg (.classMem (synC0c) (synCphi A))) :=
  by
  let proofSupport : Finset Var := A.fv
  let y : Var := freshVar proofSupport 0
  let x : Var := freshVar proofSupport 1
  have fresh_y : y ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_y_not_A : y ∉ A.fv := by
    intro h
    exact fresh_y (h)
  have fresh_x : x ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_x_not_A : x ∉ A.fv := by
    intro h
    exact fresh_x (h)
  have fresh_y_ne_x : y ≠ x :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_y : x ≠ y := Ne.symm fresh_y_ne_x
  have dv_cache_0001 : y ∉ ((Wff.classEq (.cv x) (synC0c))).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_y_ne_x, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
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
  have dv_cache_0003 : x ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0004 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0005 : x ∉ ((synC0c)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0006 :
    x ∉
      ((synWrex y A (.classEq (synC0c)
            (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c))
              (.cv y))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_wrex,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cif,
          NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cplc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, Finset.mem_union,
          Finset.mem_erase, Finset.mem_singleton, fresh_x_not_A, fresh_x_ne_y,
          compact_fv_not_mem_empty, or_false, and_false, not_false_eq_true])
  have p0000 := @gN0cnsuc (.cv y)
  have p0001 := (Nominal.biimpRefl (synWne (synCplc (.cv y) (synC1c)) (synC0c)))
  have p0002 :=
    @gMpbi (synWne (synCplc (.cv y) (synC1c)) (synC0c))
      (.neg (.classEq (synCplc (.cv y) (synC1c)) (synC0c))) p0000 p0001
  have p0003 :=
    @gIffalse (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)
  have p0004 :=
    @gEqeq2d (.neg (.classMem (.cv y) (synCnnc)))
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (.cv y) (synC0c) p0003
  have p0005 :=
    @gBiimpac (.neg (.classMem (.cv y) (synCnnc)))
      (.classEq (synC0c)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (synC0c) (.cv y)) p0004
  have p0006 := @gPeano1
  have p0007 :=
    @gSyl6eqelr
      (synWa (.classEq (synC0c)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
        (.neg (.classMem (.cv y) (synCnnc))))
      (.cv y) (synC0c) (synCnnc) p0005 p0006
  have p0008 :=
    @gEx
      (.classEq (synC0c)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.neg (.classMem (.cv y) (synCnnc))) (.classMem (.cv y) (synCnnc)) p0007
  have p0009 :=
    @gPm218d
      (.classEq (synC0c)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classMem (.cv y) (synCnnc)) p0008
  have p0010 :=
    @gIftrue (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)
  have p0011 :=
    @gEqeq2d (.classMem (.cv y) (synCnnc))
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
      (synCplc (.cv y) (synC1c)) (synC0c) p0010
  have p0012 := @gEqcom (synC0c) (synCplc (.cv y) (synC1c))
  have p0013 :=
    @gSyl6bb (.classMem (.cv y) (synCnnc))
      (.classEq (synC0c)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (synC0c) (synCplc (.cv y) (synC1c)))
      (.classEq (synCplc (.cv y) (synC1c)) (synC0c)) p0011 p0012
  have p0014 :=
    @gBiimpd (.classMem (.cv y) (synCnnc))
      (.classEq (synC0c)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (synCplc (.cv y) (synC1c)) (synC0c)) p0013
  have p0015 :=
    @gMpcom (.classMem (.cv y) (synCnnc))
      (.classEq (synC0c)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (synCplc (.cv y) (synC1c)) (synC0c)) p0009 p0014
  have p0016 :=
    @gMto
      (.classEq (synC0c)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (synCplc (.cv y) (synC1c)) (synC0c)) p0002 p0015
  have p0017 :=
    @gA1i
      (.neg (.classEq (synC0c)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (.classMem (.cv y) A) p0016
  have p0018 :=
    @gNrex
      (.classEq (synC0c)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      y A p0017
  have p0019 := @gN0cex
  have p0020 :=
    @gEqeq1 (.cv x) (synC0c)
      (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))
  have p0021 :=
    @gRexbidv (.classEq (.cv x) (synC0c))
      (.classEq (.cv x)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      (.classEq (synC0c)
        (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y)))
      y A dv_cache_0001 p0020
  have p0022 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfPhi y x A
      dv_cache_0002 dv_cache_0003 dv_cache_0004
  have p0023 :=
    @gElab2
      (synWrex y A (.classEq (.cv x)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      (synWrex y A (.classEq (synC0c)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      x (synC0c) (synCphi A) dv_cache_0005 dv_cache_0006 p0019 p0021 p0022
  have p0024 :=
    @gMtbir (.classMem (synC0c) (synCphi A))
      (synWrex y A (.classEq (synC0c)
          (synCif (.classMem (.cv y) (synCnnc)) (synCplc (.cv y) (synC1c)) (.cv y))))
      p0018 p0023
  exact p0024


end NFChoice.DirectNominalPrf.WPPReplay

end
