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

@[expose]
noncomputable def g_df1st2 :
    Nominal.NPrf
      (.classEq (syn_c1st) (syn_cuni1 (syn_cuni1 (syn_cimak
              (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk
                  (syn_ccompl (syn_cimak
                      (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k
                          (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                                    (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv))))))))) (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                    (syn_csik (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
        (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1
        (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk
        (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cimak
                (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik
                                (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                        (syn_cins3k (syn_csik (syn_csik (syn_cimak
                                (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                      (syn_ccompl (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk
        (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik
        (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1
        (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk
        (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_c1c))))))) :=
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
      ((syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun
                (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                          (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                      (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                  (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
  have dv_cache_0002 : t ∉ ((syn_cpw1 (syn_c1c))).fv :=
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
  have dv_cache_0003 : t ∉ ((syn_copk (.cv x) (.cv y))).fv :=
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                    (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
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
  have dv_cache_0006 : t ∉ ((syn_csn (syn_csn (.cv z)))).fv :=
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv x) (.cv y)))
          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun
                  (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                            (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                        (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))).fv :=
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
      ((syn_cimak (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                            (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                        (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_c1c)))).fv :=
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
      ((syn_cimak (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                            (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                        (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_c1c)))).fv :=
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
  have p0000 := @g_opkex (.cv x) (.cv y)
  have p0001 :=
    @g_elimak t
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun
              (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                          (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                      (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_c1c)) (syn_copk (.cv x) (.cv y)) dv_cache_0001 dv_cache_0002
      dv_cache_0003 p0000
  have p0002 :=
    (Nominal.biimpRefl (syn_wrex t (syn_cpw1 (syn_c1c))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                    (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
  have p0003 := @g_elpw11c z (.cv t) dv_cache_0004
  have p0004 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (.cv z)))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins2k
                    (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                  (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      p0003
  have p0005 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
      (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins2k
                    (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                  (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      z dv_cache_0005
  have p0006 :=
    @g_bitr4i
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                    (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wa (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (.cv z)))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                    (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                      (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                    (syn_cins3k (syn_csik (syn_csik (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1
        (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun
        (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1
        (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      p0004 p0005
  have p0007 :=
    @g_exbii
      (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                    (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                      (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                    (syn_cins3k (syn_csik (syn_csik (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1
        (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun
        (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1
        (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      t p0006
  have p0008 :=
    @g_excom
      (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
        (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                    (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      z t
  have p0009 :=
    @g_bitr4i
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                      (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                    (syn_cins3k (syn_csik (syn_csik (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1
        (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun
        (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1
        (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex t (syn_wex z (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                        (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                  (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                      (syn_cins3k (syn_csik (syn_csik (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                        (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                  (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                      (syn_cins3k (syn_csik (syn_csik (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0007 p0008
  have p0010 :=
    @g_bitri
      (syn_wrex t (syn_cpw1 (syn_c1c)) (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun
                  (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                            (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                        (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wex t (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                      (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                    (syn_cins3k (syn_csik (syn_csik (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1
        (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun
        (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1
        (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                        (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                  (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                      (syn_cins3k (syn_csik (syn_csik (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0002 p0009
  have p0011 :=
    @g_bitri
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cimak (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                    (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c))))
      (syn_wrex t (syn_cpw1 (syn_c1c)) (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun
                  (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                            (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                        (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                        (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                  (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                      (syn_cins3k (syn_csik (syn_csik (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      p0001 p0010
  have p0012 := @g_snex (syn_csn (.cv z))
  have p0013 := @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv z))) (syn_copk (.cv x) (.cv y))
  have p0014 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
      (syn_copk (.cv t) (syn_copk (.cv x) (.cv y)))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv x) (.cv y)))
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun
              (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                          (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                      (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      p0013
  have p0015 :=
    @g_ceqsexv
      (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins2k
                    (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                                (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                  (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv x) (.cv y))) (syn_ccompl
          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                  (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                  (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      t (syn_csn (syn_csn (.cv z))) dv_cache_0006 dv_cache_0007 p0012 p0014
  have p0016 := @g_vex x
  have p0017 := @g_vex y
  have p0018 := @g_vex z
  have p0019 := @g_setconslem7 (.cv x) (.cv y) (.cv z) p0016 p0017 p0018
  have p0020 :=
    @g_bitri
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                      (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                    (syn_cins3k (syn_csik (syn_csik (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1
        (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun
        (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1
        (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv x) (.cv y))) (syn_ccompl
          (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                  (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                              (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                  (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
      (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) p0015 p0019
  have p0021 :=
    @g_exbii
      (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
          (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                      (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                    (syn_cins3k (syn_csik (syn_csik (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1
        (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun
        (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1
        (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
      (.classEq (.cv x) (syn_cop (.cv y) (.cv z))) z p0020
  have p0022 :=
    @g_bitri
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cimak (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                    (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c))))
      (syn_wex z (syn_wex t (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
            (.classMem (syn_copk (.cv t) (syn_copk (.cv x) (.cv y))) (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                        (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                  (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                      (syn_cins3k (syn_csik (syn_csik (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))
      (syn_wex z (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))) p0011 p0021
  have p0023 :=
    @g_opabbii
      (.classMem (syn_copk (.cv x) (.cv y)) (syn_cimak (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                    (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c))))
      (syn_wex z (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))) x y p0022
  have p0024 :=
    @g_setconslem4 x y
      (syn_cimak (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                          (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                      (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                  (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c)))
      dv_cache_0008 dv_cache_0009 dv_cache_0010
  have p0025 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_1st x y z
      dv_cache_0010 dv_cache_0011 dv_cache_0012
  have p0026 :=
    @g_n_3eqtr4ri
      (syn_copab x y (.classMem (syn_copk (.cv x) (.cv y)) (syn_cimak (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                      (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                    (syn_cins3k (syn_csik (syn_csik (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1
        (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun
        (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1
        (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c)))))
      (syn_copab x y (syn_wex z (.classEq (.cv x) (syn_cop (.cv y) (.cv z)))))
      (syn_cuni1 (syn_cuni1 (syn_cimak
            (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl
                  (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
                      (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik
                                (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cimak
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik
                              (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                      (syn_cins3k (syn_csik (syn_csik (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_c1c))))))
      (syn_c1st) p0023 p0024 p0025
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

@[expose]
noncomputable def g_n_1stex : Nominal.NPrf (.classMem (syn_c1st) (syn_cvv)) :=
  by
  have p0000 := @g_df1st2
  have p0001 := @g_vvex
  have p0003 := @g_xpkex (syn_cvv) (syn_cvv) p0001 p0001
  have p0005 := @g_xpkex (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv) p0003 p0001
  have p0006 := @g_setconslem5
  have p0007 :=
    @g_cnvkex
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
            (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
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
      p0006
  have p0008 :=
    @g_inex (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv))
      (syn_ccnvk (syn_ccompl (syn_cimak
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
      p0005 p0007
  have p0009 := @g_ssetkex
  have p0010 := @g_ins3kex (syn_cssetk) p0009
  have p0011 := @g_ins2kex (syn_cins3k (syn_cssetk)) p0010
  have p0013 := @g_addcexlem
  have p0014 := @g_n_1cex
  have p0015 := @g_pw1ex (syn_c1c) p0014
  have p0016 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0015
  have p0017 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0013 p0016
  have p0018 :=
    @g_imagekex
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0017
  have p0019 := @g_nncex
  have p0021 := @g_xpkex (syn_cnnc) (syn_cvv) p0019 p0001
  have p0022 :=
    @g_inex
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cxpk (syn_cnnc) (syn_cvv)) p0018 p0021
  have p0023 := @g_idkex
  have p0025 := @g_complex (syn_cnnc) p0019
  have p0027 := @g_xpkex (syn_ccompl (syn_cnnc)) (syn_cvv) p0025 p0001
  have p0028 :=
    @g_inex (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)) p0023 p0027
  have p0029 :=
    @g_unex
      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))) p0022 p0028
  have p0030 :=
    @g_imagekex
      (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                      (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                  (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                      (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
      p0029
  have p0031 :=
    @g_cnvkex
      (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
          (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))
      p0030
  have p0032 :=
    @g_sikex
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
      p0031
  have p0033 :=
    @g_cokex (syn_cssetk)
      (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                      (syn_cins3k (syn_ccompl (syn_cimak
                            (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                          (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                            (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
              (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))
      p0009 p0032
  have p0034 :=
    @g_ins2kex
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
      p0033
  have p0035 :=
    @g_ins2kex
      (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                  (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
      p0034
  have p0037 := @g_ins2kex (syn_cssetk) p0009
  have p0039 :=
    @g_cokex
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
      (syn_cssetk) p0031 p0009
  have p0040 := @g_snex (syn_csn (syn_c0c))
  have p0042 := @g_xpkex (syn_csn (syn_csn (syn_c0c))) (syn_cvv) p0040 p0001
  have p0043 :=
    @g_unex
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
      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)) p0039 p0042
  have p0044 :=
    @g_ins3kex
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
      p0043
  have p0045 :=
    @g_symdifex (syn_cins2k (syn_cssetk))
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
      p0037 p0044
  have p0046 :=
    @g_imakex
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
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0045 p0016
  have p0047 :=
    @g_complex
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
      p0046
  have p0048 :=
    @g_sikex
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
      p0047
  have p0049 :=
    @g_ins3kex
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
      p0048
  have p0050 :=
    @g_inex (syn_cins2k (syn_cssetk))
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
      p0037 p0049
  have p0051 :=
    @g_imakex
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
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0050 p0016
  have p0052 :=
    @g_sikex
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
      p0051
  have p0053 :=
    @g_sikex
      (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
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
                            (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      p0052
  have p0054 :=
    @g_ins3kex
      (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
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
      p0053
  have p0055 :=
    @g_unex
      (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
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
      (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                  (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                          (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
                                      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
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
      p0035 p0054
  have p0056 :=
    @g_symdifex (syn_cins2k (syn_cins3k (syn_cssetk)))
      (syn_cun (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                    (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
                                      (syn_cins2k (syn_cssetk)))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
                      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
        (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                  (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                          (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun (syn_ccomk
                                  (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
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
      p0011 p0055
  have p0057 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0016
  have p0058 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0057
  have p0059 :=
    @g_imakex
      (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins2k
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
                        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
          (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                    (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                            (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
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
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0056 p0058
  have p0060 :=
    @g_complex
      (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
              (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                          (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                                      (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
              (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                        (syn_csik (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun
        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      p0059
  have p0061 :=
    @g_imakex
      (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun
              (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                          (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
                                      (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_c1c)) p0060 p0015
  have p0062 :=
    @g_imakex
      (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl
            (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k
                  (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
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
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
      (syn_cimak (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                          (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
                                      (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))) (syn_cins3k
                  (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c)))
      p0008 p0061
  have p0063 :=
    @g_uni1ex
      (syn_cimak (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
                  (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                              (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                      (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                              (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cimak (syn_ccompl
            (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun (syn_cins2k
                    (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                              (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                  (syn_cins3k (syn_csik (syn_csik (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                            (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c))))
      p0062
  have p0064 :=
    @g_uni1ex
      (syn_cuni1 (syn_cimak (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv))
            (syn_ccnvk (syn_ccompl (syn_cimak
                  (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))) (syn_cins2k
                      (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                                (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                        (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                (syn_csik (syn_ccompl (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cimak
            (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cun
                    (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk
                              (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                    (syn_cins3k (syn_csik (syn_csik (syn_cimak
                            (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik (syn_ccompl
                                    (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
                                        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1
        (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun
        (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1
        (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c)))))
      p0063
  have p0065 :=
    @g_eqeltri (syn_c1st)
      (syn_cuni1 (syn_cuni1 (syn_cimak
            (syn_cin (syn_cxpk (syn_cxpk (syn_cvv) (syn_cvv)) (syn_cvv)) (syn_ccnvk (syn_ccompl
                  (syn_cimak (syn_csymdif (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
                      (syn_cins2k (syn_cun (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik
                                (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))
                          (syn_cins2k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
                                  (syn_csik (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cimak
              (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cun (syn_cins2k (syn_cins2k (syn_ccomk (syn_cssetk) (syn_csik
                              (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))
                      (syn_cins3k (syn_csik (syn_csik (syn_cimak
                              (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
                                    (syn_ccompl (syn_cimak
                                        (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
              (syn_cpw1 (syn_c1c))))))
      (syn_cvv) p0000 p0064
  exact p0065

@[expose]
noncomputable def g_elswap (x : Var) (y : Var) (A : Class) (dv_A_x : x ∉ A.fv)
    (dv_A_y : y ∉ A.fv) (dv_x_y : x ≠ y) :
    Nominal.NPrf
      (syn_wb (.classMem A (syn_cswap)) (syn_wex x (syn_wex y (.classEq A
              (syn_cop (syn_cop (.cv x) (.cv y)) (syn_cop (.cv y) (.cv x))))))) :=
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
  have dv_cache_0009 : x ∉ ((Wff.classEq A (syn_cop (.cv z) (.cv w)))).fv :=
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
  have dv_cache_0010 : y ∉ ((Wff.classEq A (syn_cop (.cv z) (.cv w)))).fv :=
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
  have dv_cache_0011 : z ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
  have dv_cache_0012 : w ∉ ((syn_cop (.cv x) (.cv y))).fv :=
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
  have dv_cache_0013 : z ∉ ((syn_cop (.cv y) (.cv x))).fv :=
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
  have dv_cache_0014 : w ∉ ((syn_cop (.cv y) (.cv x))).fv :=
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
      ((Wff.classEq A (syn_cop (syn_cop (.cv x) (.cv y)) (syn_cop (.cv y) (.cv x))))).fv :=
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
    z ∉ ((Wff.classEq A (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))).fv :=
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
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_swap z w x y
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005 dv_cache_0006
  have p0001 :=
    @g_eleq2i (syn_cswap)
      (syn_copab z w (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
              (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))))
      A p0000
  have p0002 :=
    @g_elopab
      (syn_wex x (syn_wex y (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
            (.classEq (.cv w) (syn_cop (.cv y) (.cv x))))))
      z w A dv_cache_0007 dv_cache_0008
  have p0003 :=
    @g_bitri (.classMem A (syn_cswap))
      (.classMem A (syn_copab z w (syn_wex x (syn_wex y
              (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
                (.classEq (.cv w) (syn_cop (.cv y) (.cv x))))))))
      (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w))) (syn_wex x (syn_wex y
                (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
                  (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))))))
      p0001 p0002
  have p0004 :=
    @g_exrot4
      (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
        (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
          (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))
      z w x y
  have p0005 :=
    @g_n_19_42vv (.classEq A (syn_cop (.cv z) (.cv w)))
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (.classEq (.cv w) (syn_cop (.cv y) (.cv x))))
      x y dv_cache_0009 dv_cache_0010
  have p0006 :=
    @g_n_2exbii
      (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
            (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
              (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))))
      (syn_wa (.classEq A (syn_cop (.cv z) (.cv w))) (syn_wex x (syn_wex y
            (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
              (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))))
      z w p0005
  have p0007 :=
    (Nominal.biimpRefl (syn_w3a (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (.classEq A (syn_cop (.cv z) (.cv w)))))
  have p0008 :=
    @g_ancom
      (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (.classEq (.cv w) (syn_cop (.cv y) (.cv x))))
      (.classEq A (syn_cop (.cv z) (.cv w)))
  have p0009 :=
    @g_bitr2i
      (syn_w3a (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (.classEq A (syn_cop (.cv z) (.cv w))))
      (syn_wa (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
          (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))) (.classEq A (syn_cop (.cv z) (.cv w))))
      (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
        (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
          (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))
      p0007 p0008
  have p0010 :=
    @g_n_2exbii
      (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
        (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
          (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))
      (syn_w3a (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
        (.classEq (.cv w) (syn_cop (.cv y) (.cv x))) (.classEq A (syn_cop (.cv z) (.cv w))))
      z w p0009
  have p0011 := @g_vex x
  have p0012 := @g_vex y
  have p0013 := @g_opex (.cv x) (.cv y) p0011 p0012
  have p0014 := @g_opex (.cv y) (.cv x) p0012 p0011
  have p0015 := @g_opeq1 (.cv z) (syn_cop (.cv x) (.cv y)) (.cv w)
  have p0016 :=
    @g_eqeq2d (.classEq (.cv z) (syn_cop (.cv x) (.cv y))) (syn_cop (.cv z) (.cv w))
      (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)) A p0015
  have p0017 := @g_opeq2 (.cv w) (syn_cop (.cv y) (.cv x)) (syn_cop (.cv x) (.cv y))
  have p0018 :=
    @g_eqeq2d (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))
      (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w))
      (syn_cop (syn_cop (.cv x) (.cv y)) (syn_cop (.cv y) (.cv x))) A p0017
  have p0019 :=
    @g_ceqsex2v (.classEq A (syn_cop (.cv z) (.cv w)))
      (.classEq A (syn_cop (syn_cop (.cv x) (.cv y)) (.cv w)))
      (.classEq A (syn_cop (syn_cop (.cv x) (.cv y)) (syn_cop (.cv y) (.cv x)))) z w
      (syn_cop (.cv x) (.cv y)) (syn_cop (.cv y) (.cv x)) dv_cache_0011 dv_cache_0012
      dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0004 p0013 p0014
      p0016 p0018
  have p0020 :=
    @g_bitri
      (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
            (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
              (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))))
      (syn_wex z (syn_wex w (syn_w3a (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
            (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))
            (.classEq A (syn_cop (.cv z) (.cv w))))))
      (.classEq A (syn_cop (syn_cop (.cv x) (.cv y)) (syn_cop (.cv y) (.cv x)))) p0010
      p0019
  have p0021 :=
    @g_n_2exbii
      (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
            (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
              (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))))
      (.classEq A (syn_cop (syn_cop (.cv x) (.cv y)) (syn_cop (.cv y) (.cv x)))) x y p0020
  have p0022 :=
    @g_n_3bitr3i
      (syn_wex z (syn_wex w (syn_wex x (syn_wex y (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
                (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
                  (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))))))
      (syn_wex x (syn_wex y (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w)))
                (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
                  (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))))))
      (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w))) (syn_wex x (syn_wex y
                (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
                  (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))))))
      (syn_wex x (syn_wex y
          (.classEq A (syn_cop (syn_cop (.cv x) (.cv y)) (syn_cop (.cv y) (.cv x))))))
      p0004 p0006 p0021
  have p0023 :=
    @g_bitri (.classMem A (syn_cswap))
      (syn_wex z (syn_wex w (syn_wa (.classEq A (syn_cop (.cv z) (.cv w))) (syn_wex x (syn_wex y
                (syn_wa (.classEq (.cv z) (syn_cop (.cv x) (.cv y)))
                  (.classEq (.cv w) (syn_cop (.cv y) (.cv x)))))))))
      (syn_wex x (syn_wex y
          (.classEq A (syn_cop (syn_cop (.cv x) (.cv y)) (syn_cop (.cv y) (.cv x))))))
      p0003 p0022
  exact p0023


end NFChoice.DirectNominalPrf.WPPReplay

end
