/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk010Compact001Part047

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part048`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_df1st2`. -/
@[expose]
noncomputable def gDf1st2 :
    Nominal.NPrf
      (.classEq (synC1st) (synCuni1 (synCuni1 (synCimak
              (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv)) (synCcnvk
                  (synCcompl (synCimak
                      (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k
                          (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
                                    (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv))))))))) (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                    (synCsik (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
        (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1
        (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk
        (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCimak
                (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk)))
                      (synCun (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik
                                (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                        (synCins3k (synCsik (synCsik (synCimak
                                (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                      (synCcompl (synCimak
        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk (synCcnvk
        (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1
        (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk
        (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synC1c))))))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have dv_cache_0001 :
    t ∉
      ((synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun
                (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk
                          (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                      (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
    by
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
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
  have dv_cache_0002 : t ∉ ((synCpw1 (synC1c))).fv :=
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
  have dv_cache_0003 : t ∉ ((synCopk (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, or_false, not_false_eq_true])
  have dv_cache_0004 : z ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_t, not_false_eq_true])
  have dv_cache_0005 :
    z ∉
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_x, fresh_z_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0006 : t ∉ ((synCsn (synCsn (.cv z)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_z,
          not_false_eq_true])
  have dv_cache_0007 :
    t ∉
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv x) (.cv y)))
          (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun
                  (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk
                            (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                        (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_x, fresh_t_ne_y,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    x ∉
      ((synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk)))
                (synCun (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk
                            (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                        (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synC1c)))).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
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
  have dv_cache_0009 :
    y ∉
      ((synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk)))
                (synCun (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk
                            (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                        (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synC1c)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
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
  have dv_cache_0010 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have dv_cache_0011 : x ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show x ≠ z from (by exact fresh_x_ne_z))
  have dv_cache_0012 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have p0000 := @gOpkex (.cv x) (.cv y)
  have p0001 :=
    @gElimak t
      (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun
              (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                          (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                      (synCcompl (synCimak (synCin (synCins3k (synCssetk))
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
      (synCpw1 (synC1c)) (synCopk (.cv x) (.cv y)) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0000
  have p0002 :=
    (Nominal.biimpRefl (synWrex t (synCpw1 (synC1c))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
  have p0003 := @gElpw11c z (.cv t) dv_cache_0004
  have p0004 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex z (.classEq (.cv t) (synCsn (synCsn (.cv z)))))
      (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
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
      p0003
  have p0005 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv z))))
      (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
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
      z dv_cache_0005
  have p0006 :=
    @gBitr4i
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWa (synWex z (.classEq (.cv t) (synCsn (synCsn (.cv z)))))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                      (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                    (synCins3k (synCsik (synCsik (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1
        (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
        (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1
        (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c)))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      p0004 p0005
  have p0007 :=
    @gExbii
      (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                      (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                    (synCins3k (synCsik (synCsik (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1
        (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
        (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1
        (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c)))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      t p0006
  have p0008 :=
    @gExcom
      (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
        (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      z t
  have p0009 :=
    @gBitr4i
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                      (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                    (synCins3k (synCsik (synCsik (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1
        (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
        (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1
        (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c)))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex t (synWex z (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
            (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                        (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                  (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                      (synCins3k (synCsik (synCsik (synCimak
                              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c)))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
            (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                        (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                  (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                      (synCins3k (synCsik (synCsik (synCimak
                              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c)))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0007 p0008
  have p0010 :=
    @gBitri
      (synWrex t (synCpw1 (synC1c)) (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
          (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun
                  (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk
                            (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                        (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex t (synWa (.classMem (.cv t) (synCpw1 (synC1c)))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                      (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                    (synCins3k (synCsik (synCsik (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1
        (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
        (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1
        (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c)))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
            (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                        (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                  (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                      (synCins3k (synCsik (synCsik (synCimak
                              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c)))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0002 p0009
  have p0011 :=
    @gBitri
      (.classMem (synCopk (.cv x) (.cv y)) (synCimak (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c))))
      (synWrex t (synCpw1 (synC1c)) (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
          (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun
                  (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk
                            (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                        (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
            (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                        (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                  (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                      (synCins3k (synCsik (synCsik (synCimak
                              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c)))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      p0001 p0010
  have p0012 := @gSnex (synCsn (.cv z))
  have p0013 := @gOpkeq1 (.cv t) (synCsn (synCsn (.cv z))) (synCopk (.cv x) (.cv y))
  have p0014 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv z))))
      (synCopk (.cv t) (synCopk (.cv x) (.cv y)))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv x) (.cv y)))
      (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun
              (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                          (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                      (synCcompl (synCimak (synCin (synCins3k (synCssetk))
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
      p0013
  have p0015 :=
    @gCeqsexv
      (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
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
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv x) (.cv y))) (synCcompl
          (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                  (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
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
      t (synCsn (synCsn (.cv z))) dv_cache_0006 dv_cache_0007 p0012 p0014
  have p0016 := @gVex x
  have p0017 := @gVex y
  have p0018 := @gVex z
  have p0019 := @gSetconslem7 (.cv x) (.cv y) (.cv z) p0016 p0017 p0018
  have p0020 :=
    @gBitri
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                      (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                    (synCins3k (synCsik (synCsik (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1
        (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
        (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1
        (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c)))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv x) (.cv y))) (synCcompl
          (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                  (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
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
      (.classEq (.cv x) (synCop (.cv y) (.cv z))) p0015 p0019
  have p0021 :=
    @gExbii
      (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
          (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                      (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                    (synCins3k (synCsik (synCsik (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1
        (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
        (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1
        (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c)))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (.classEq (.cv x) (synCop (.cv y) (.cv z))) z p0020
  have p0022 :=
    @gBitri
      (.classMem (synCopk (.cv x) (.cv y)) (synCimak (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c))))
      (synWex z (synWex t (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z))))
            (.classMem (synCopk (.cv t) (synCopk (.cv x) (.cv y))) (synCcompl (synCimak
                  (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                        (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                  (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                      (synCins3k (synCsik (synCsik (synCimak
                              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c)))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))
      (synWex z (.classEq (.cv x) (synCop (.cv y) (.cv z)))) p0011 p0021
  have p0023 :=
    @gOpabbii
      (.classMem (synCopk (.cv x) (.cv y)) (synCimak (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c))))
      (synWex z (.classEq (.cv x) (synCop (.cv y) (.cv z)))) x y p0022
  have p0024 :=
    @gSetconslem4 x y
      (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk)))
              (synCun (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk
                          (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                      (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))
      dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0025 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDf1st x y z
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0026 :=
    @gN3eqtr4ri
      (synCopab x y (.classMem (synCopk (.cv x) (.cv y)) (synCimak (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
                      (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                    (synCins3k (synCsik (synCsik (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1
        (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
        (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1
        (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c)))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))))
      (synCopab x y (synWex z (.classEq (.cv x) (synCop (.cv y) (.cv z)))))
      (synCuni1 (synCuni1 (synCimak
            (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv)) (synCcnvk (synCcompl
                  (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
                      (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik
                                (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCimak
              (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk)))
                    (synCun (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik
                              (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                      (synCins3k (synCsik (synCsik (synCimak
                              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c)))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synC1c))))))
      (synC1st) p0023 p0024 p0025
  exact p0026


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part049`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_n_1stex`. -/
@[expose]
noncomputable def gN1stex : Nominal.NPrf (.classMem (synC1st) (synCvv)) :=
  by
  have p0000 := @gDf1st2
  have p0001 := @gVvex
  have p0003 := @gXpkex (synCvv) (synCvv) p0001 p0001
  have p0005 := @gXpkex (synCxpk (synCvv) (synCvv)) (synCvv) p0003 p0001
  have p0006 := @gSetconslem5
  have p0007 :=
    @gCnvkex
      (synCcompl (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
            (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
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
                              (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                  (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                          (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      p0006
  have p0008 :=
    @gInex (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv))
      (synCcnvk (synCcompl (synCimak
            (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k (synCun
                  (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                              (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv))))))))) (synCins2k
                    (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                            (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                                  (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik
        (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
                                      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c))))))))
                      (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0005 p0007
  have p0009 := @gSsetkex
  have p0010 := @gIns3kex (synCssetk) p0009
  have p0011 := @gIns2kex (synCins3k (synCssetk)) p0010
  have p0013 := @gAddcexlem
  have p0014 := @gN1cex
  have p0015 := @gPw1ex (synC1c) p0014
  have p0016 := @gPw1ex (synCpw1 (synC1c)) p0015
  have p0017 :=
    @gImakex
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synC1c))) p0013 p0016
  have p0018 :=
    @gImagekex
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0017
  have p0019 := @gNncex
  have p0021 := @gXpkex (synCnnc) (synCvv) p0019 p0001
  have p0022 :=
    @gInex
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCxpk (synCnnc) (synCvv)) p0018 p0021
  have p0023 := @gIdkex
  have p0025 := @gComplex (synCnnc) p0019
  have p0027 := @gXpkex (synCcompl (synCnnc)) (synCvv) p0025 p0001
  have p0028 :=
    @gInex (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)) p0023 p0027
  have p0029 :=
    @gUnex
      (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))) p0022 p0028
  have p0030 :=
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
      p0029
  have p0031 :=
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
      p0030
  have p0032 :=
    @gSikex
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
      p0031
  have p0033 :=
    @gCokex (synCssetk)
      (synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      p0009 p0032
  have p0034 :=
    @gIns2kex
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
      p0033
  have p0035 :=
    @gIns2kex
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
      p0034
  have p0037 := @gIns2kex (synCssetk) p0009
  have p0039 :=
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
      (synCssetk) p0031 p0009
  have p0040 := @gSnex (synCsn (synC0c))
  have p0042 := @gXpkex (synCsn (synCsn (synC0c))) (synCvv) p0040 p0001
  have p0043 :=
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
      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)) p0039 p0042
  have p0044 :=
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
      p0043
  have p0045 :=
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
      p0037 p0044
  have p0046 :=
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
      (synCpw1 (synCpw1 (synC1c))) p0045 p0016
  have p0047 :=
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
      p0046
  have p0048 :=
    @gSikex
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
      p0047
  have p0049 :=
    @gIns3kex
      (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
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
      p0048
  have p0050 :=
    @gInex (synCins2k (synCssetk))
      (synCins3k (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
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
              (synCpw1 (synCpw1 (synC1c)))))))
      p0037 p0049
  have p0051 :=
    @gImakex
      (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl (synCimak
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
      (synCpw1 (synCpw1 (synC1c))) p0050 p0016
  have p0052 :=
    @gSikex
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
      p0051
  have p0053 :=
    @gSikex
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
      p0052
  have p0054 :=
    @gIns3kex
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
      p0053
  have p0055 :=
    @gUnex
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
      p0035 p0054
  have p0056 :=
    @gSymdifex (synCins2k (synCins3k (synCssetk)))
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
      p0011 p0055
  have p0057 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0016
  have p0058 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0057
  have p0059 :=
    @gImakex
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
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0056 p0058
  have p0060 :=
    @gComplex
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
      p0059
  have p0061 :=
    @gImakex
      (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun
              (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                          (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                      (synCcompl (synCimak (synCin (synCins3k (synCssetk))
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
      (synCpw1 (synC1c)) p0060 p0015
  have p0062 :=
    @gImakex
      (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv)) (synCcnvk (synCcompl
            (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k
                  (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                              (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                    (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
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
                        (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk)))
              (synCun (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk
                          (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                      (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))
      p0008 p0061
  have p0063 :=
    @gUni1ex
      (synCimak (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv)) (synCcnvk
            (synCcompl (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
                  (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
                              (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                      (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                              (synCsik (synCcompl (synCimak
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
                          (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCimak (synCcompl
            (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun (synCins2k
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c))))
      p0062
  have p0064 :=
    @gUni1ex
      (synCuni1 (synCimak (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv))
            (synCcnvk (synCcompl (synCimak
                  (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k
                      (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
                                (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                        (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                (synCsik (synCcompl (synCimak
                                      (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCimak
            (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk))) (synCun
                    (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik (synCcnvk
                              (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                    (synCins3k (synCsik (synCsik (synCimak
                            (synCin (synCins2k (synCssetk)) (synCins3k (synCsik (synCcompl
                                    (synCimak (synCsymdif (synCins2k (synCssetk))
                                        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1
        (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
        (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1
        (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c))))))))
                            (synCpw1 (synCpw1 (synC1c)))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))))
      p0063
  have p0065 :=
    @gEqeltri (synC1st)
      (synCuni1 (synCuni1 (synCimak
            (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv)) (synCcnvk (synCcompl
                  (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
                      (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik
                                (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
                          (synCins2k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
                                  (synCsik (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCimak
              (synCcompl (synCimak (synCsymdif (synCins2k (synCins3k (synCssetk)))
                    (synCun (synCins2k (synCins2k (synCcomk (synCssetk) (synCsik
                              (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
                      (synCins3k (synCsik (synCsik (synCimak
                              (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                                    (synCcompl (synCimak
                                        (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c))))))))
                              (synCpw1 (synCpw1 (synC1c)))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
              (synCpw1 (synC1c))))))
      (synCvv) p0000 p0064
  exact p0065

/-- Checked nominal proof certificate identified upstream as `g_elswap`. -/
@[expose]
noncomputable def gElswap (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (synWb (.classMem A (synCswap)) (synWex x (synWex y (.classEq A
              (synCop (synCop (.cv x) (.cv y)) (synCop (.cv y) (.cv x))))))) :=
  by
  let proofSupport : Finset Var := ({ x } : Finset Var) ∪ ({ y } : Finset Var) ∪ A.fv
  let z : Var := freshVar proofSupport 0
  let w : Var := freshVar proofSupport 1
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 0 ∉ proofSupport
    exact freshVar_not_mem proofSupport 0
  have fresh_z_ne_x : z ≠ x := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_z : x ≠ z := Ne.symm fresh_z_ne_x
  have fresh_z_ne_y : z ≠ y := by
    intro h
    exact
      fresh_z
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_z : y ≠ z := Ne.symm fresh_z_ne_y
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_right _ (h))
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 1 ∉ proofSupport
    exact freshVar_not_mem proofSupport 1
  have fresh_w_ne_x : w ≠ x := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_singleton.mpr h)))
  have fresh_x_ne_w : x ≠ w := Ne.symm fresh_w_ne_x
  have fresh_w_ne_y : w ≠ y := by
    intro h
    exact
      fresh_w
        (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton.mpr h)))
  have fresh_y_ne_w : y ≠ w := Ne.symm fresh_w_ne_y
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_right _ (h))
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : y ≠ z := by exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0002 : y ≠ w := by
    clear dv_cache_0001
    exact (show y ≠ w from (by exact fresh_y_ne_w))
  have dv_cache_0003 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show y ≠ x from (by exact Ne.symm dv_x_y))
  have dv_cache_0004 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0005 : z ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show z ≠ x from (by exact fresh_z_ne_x))
  have dv_cache_0006 : w ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact (show w ≠ x from (by exact fresh_w_ne_x))
  have dv_cache_0007 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0008 : w ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_w_not_A, not_false_eq_true])
  have dv_cache_0009 : x ∉ ((Wff.classEq A (synCop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_x, fresh_x_ne_z, fresh_x_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0010 : y ∉ ((Wff.classEq A (synCop (.cv z) (.cv w)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, dv_A_y, fresh_y_ne_z, fresh_y_ne_w, or_false,
          not_false_eq_true])
  have dv_cache_0011 : z ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_x, fresh_z_ne_y, or_false, not_false_eq_true])
  have dv_cache_0012 : w ∉ ((synCop (.cv x) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_y, or_false, not_false_eq_true])
  have dv_cache_0013 : z ∉ ((synCop (.cv y) (.cv x))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_y, fresh_z_ne_x, or_false, not_false_eq_true])
  have dv_cache_0014 : w ∉ ((synCop (.cv y) (.cv x))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_x, or_false, not_false_eq_true])
  have dv_cache_0015 :
    w ∉
      ((Wff.classEq A (synCop (synCop (.cv x) (.cv y)) (synCop (.cv y) (.cv x))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_not_A, fresh_w_ne_x, fresh_w_ne_y, or_false,
          not_false_eq_true])
  have dv_cache_0016 :
    z ∉ ((Wff.classEq A (synCop (synCop (.cv x) (.cv y)) (.cv w)))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classEq,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_not_A, fresh_z_ne_x, fresh_z_ne_y, fresh_z_ne_w,
          or_false, not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSwap z w x y
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @gEleq2i (synCswap)
      (synCopab z w (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
              (.classEq (.cv w) (synCop (.cv y) (.cv x)))))))
      A p0000
  have p0002 :=
    @gElopab
      (synWex x (synWex y (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
            (.classEq (.cv w) (synCop (.cv y) (.cv x))))))
      z w A dv_cache_0007 dv_cache_0008
  have p0003 :=
    @gBitri (.classMem A (synCswap))
      (.classMem A (synCopab z w (synWex x (synWex y
              (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
                (.classEq (.cv w) (synCop (.cv y) (.cv x))))))))
      (synWex z (synWex w (synWa (.classEq A (synCop (.cv z) (.cv w))) (synWex x (synWex y
                (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
                  (.classEq (.cv w) (synCop (.cv y) (.cv x)))))))))
      p0001 p0002
  have p0004 :=
    @gExrot4
      (synWa (.classEq A (synCop (.cv z) (.cv w)))
        (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
          (.classEq (.cv w) (synCop (.cv y) (.cv x)))))
      z w x y
  have p0005 :=
    @gN1942vv (.classEq A (synCop (.cv z) (.cv w)))
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (.classEq (.cv w) (synCop (.cv y) (.cv x))))
      x y dv_cache_0009 dv_cache_0010
  have p0006 :=
    @gN2exbii
      (synWex x (synWex y (synWa (.classEq A (synCop (.cv z) (.cv w)))
            (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
              (.classEq (.cv w) (synCop (.cv y) (.cv x)))))))
      (synWa (.classEq A (synCop (.cv z) (.cv w))) (synWex x (synWex y
            (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
              (.classEq (.cv w) (synCop (.cv y) (.cv x)))))))
      z w p0005
  have p0007 :=
    (Nominal.biimpRefl (synW3a (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (.classEq (.cv w) (synCop (.cv y) (.cv x))) (.classEq A (synCop (.cv z) (.cv w)))))
  have p0008 :=
    @gAncom
      (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (.classEq (.cv w) (synCop (.cv y) (.cv x))))
      (.classEq A (synCop (.cv z) (.cv w)))
  have p0009 :=
    @gBitr2i
      (synW3a (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (.classEq (.cv w) (synCop (.cv y) (.cv x))) (.classEq A (synCop (.cv z) (.cv w))))
      (synWa (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
          (.classEq (.cv w) (synCop (.cv y) (.cv x)))) (.classEq A (synCop (.cv z) (.cv w))))
      (synWa (.classEq A (synCop (.cv z) (.cv w)))
        (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
          (.classEq (.cv w) (synCop (.cv y) (.cv x)))))
      p0007 p0008
  have p0010 :=
    @gN2exbii
      (synWa (.classEq A (synCop (.cv z) (.cv w)))
        (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
          (.classEq (.cv w) (synCop (.cv y) (.cv x)))))
      (synW3a (.classEq (.cv z) (synCop (.cv x) (.cv y)))
        (.classEq (.cv w) (synCop (.cv y) (.cv x))) (.classEq A (synCop (.cv z) (.cv w))))
      z w p0009
  have p0011 := @gVex x
  have p0012 := @gVex y
  have p0013 := @gOpex (.cv x) (.cv y) p0011 p0012
  have p0014 := @gOpex (.cv y) (.cv x) p0012 p0011
  have p0015 := @gOpeq1 (.cv z) (synCop (.cv x) (.cv y)) (.cv w)
  have p0016 :=
    @gEqeq2d (.classEq (.cv z) (synCop (.cv x) (.cv y))) (synCop (.cv z) (.cv w))
      (synCop (synCop (.cv x) (.cv y)) (.cv w)) A p0015
  have p0017 := @gOpeq2 (.cv w) (synCop (.cv y) (.cv x)) (synCop (.cv x) (.cv y))
  have p0018 :=
    @gEqeq2d (.classEq (.cv w) (synCop (.cv y) (.cv x)))
      (synCop (synCop (.cv x) (.cv y)) (.cv w))
      (synCop (synCop (.cv x) (.cv y)) (synCop (.cv y) (.cv x))) A p0017
  have p0019 :=
    @gCeqsex2v (.classEq A (synCop (.cv z) (.cv w)))
      (.classEq A (synCop (synCop (.cv x) (.cv y)) (.cv w)))
      (.classEq A (synCop (synCop (.cv x) (.cv y)) (synCop (.cv y) (.cv x)))) z w
      (synCop (.cv x) (.cv y)) (synCop (.cv y) (.cv x)) dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0004 p0013 p0014
      p0016 p0018
  have p0020 :=
    @gBitri
      (synWex z (synWex w (synWa (.classEq A (synCop (.cv z) (.cv w)))
            (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
              (.classEq (.cv w) (synCop (.cv y) (.cv x)))))))
      (synWex z (synWex w (synW3a (.classEq (.cv z) (synCop (.cv x) (.cv y)))
            (.classEq (.cv w) (synCop (.cv y) (.cv x)))
            (.classEq A (synCop (.cv z) (.cv w))))))
      (.classEq A (synCop (synCop (.cv x) (.cv y)) (synCop (.cv y) (.cv x)))) p0010
      p0019
  have p0021 :=
    @gN2exbii
      (synWex z (synWex w (synWa (.classEq A (synCop (.cv z) (.cv w)))
            (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
              (.classEq (.cv w) (synCop (.cv y) (.cv x)))))))
      (.classEq A (synCop (synCop (.cv x) (.cv y)) (synCop (.cv y) (.cv x)))) x y p0020
  have p0022 :=
    @gN3bitr3i
      (synWex z (synWex w (synWex x (synWex y (synWa (.classEq A (synCop (.cv z) (.cv w)))
                (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
                  (.classEq (.cv w) (synCop (.cv y) (.cv x)))))))))
      (synWex x (synWex y (synWex z (synWex w (synWa (.classEq A (synCop (.cv z) (.cv w)))
                (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
                  (.classEq (.cv w) (synCop (.cv y) (.cv x)))))))))
      (synWex z (synWex w (synWa (.classEq A (synCop (.cv z) (.cv w))) (synWex x (synWex y
                (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
                  (.classEq (.cv w) (synCop (.cv y) (.cv x)))))))))
      (synWex x (synWex y
          (.classEq A (synCop (synCop (.cv x) (.cv y)) (synCop (.cv y) (.cv x))))))
      p0004 p0006 p0021
  have p0023 :=
    @gBitri (.classMem A (synCswap))
      (synWex z (synWex w (synWa (.classEq A (synCop (.cv z) (.cv w))) (synWex x (synWex y
                (synWa (.classEq (.cv z) (synCop (.cv x) (.cv y)))
                  (.classEq (.cv w) (synCop (.cv y) (.cv x)))))))))
      (synWex x (synWex y
          (.classEq A (synCop (synCop (.cv x) (.cv y)) (synCop (.cv y) (.cv x))))))
      p0003 p0022
  exact p0023


end NFChoice.DirectNominalPrf.WPPReplay

end
