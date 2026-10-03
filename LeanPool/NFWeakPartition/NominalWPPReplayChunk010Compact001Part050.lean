/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block014

/-! NF weak partition development: NominalWPPReplayChunk010Compact001Part050. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_dfswap2 :
    Nominal.NPrf
      (.classEq (syn_cswap) (syn_cimak (syn_cimak (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cimak (syn_cin
                        (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k (syn_ccomk (syn_cssetk)
                                  (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))))))) (syn_cins3k (syn_csik (syn_csik (syn_cimak
                                    (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
        (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k
                          (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cimagek
                                      (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))))))))) (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik
                                  (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik
        (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))) (syn_cins2k (syn_cins3k (syn_cimak
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
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k
                          (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k
        (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k
        (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c)))
          (syn_cvv))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let z : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let w : Var := freshVar proofSupport 4
  let v : Var := freshVar proofSupport 5
  let u : Var := freshVar proofSupport 6
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
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
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_v : x ≠ v :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 0) (j := 5) (by decide)
  have fresh_v_ne_x : v ≠ x := Ne.symm fresh_x_ne_v
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
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_v : y ≠ v :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 1) (j := 5) (by decide)
  have fresh_v_ne_y : v ≠ y := Ne.symm fresh_y_ne_v
  have fresh_y_ne_u : y ≠ u :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 1) (j := 6) (by decide)
  have fresh_u_ne_y : u ≠ y := Ne.symm fresh_y_ne_u
  have fresh_z_ne_t : z ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_t_ne_z : t ≠ z := Ne.symm fresh_z_ne_t
  have fresh_z_ne_w : z ≠ w :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_w_ne_z : w ≠ z := Ne.symm fresh_z_ne_w
  have fresh_z_ne_v : z ≠ v :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 2) (j := 5) (by decide)
  have fresh_v_ne_z : v ≠ z := Ne.symm fresh_z_ne_v
  have fresh_z_ne_u : z ≠ u :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 2) (j := 6) (by decide)
  have fresh_u_ne_z : u ≠ z := Ne.symm fresh_z_ne_u
  have fresh_t_ne_w : t ≠ w :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_w_ne_t : w ≠ t := Ne.symm fresh_t_ne_w
  have fresh_t_ne_v : t ≠ v :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 3) (j := 5) (by decide)
  have fresh_v_ne_t : v ≠ t := Ne.symm fresh_t_ne_v
  have fresh_w_ne_v : w ≠ v :=
    by
    change freshVar proofSupport 4 ≠ freshVar proofSupport 5
    exact freshVar_injective proofSupport (i := 4) (j := 5) (by decide)
  have fresh_v_ne_w : v ≠ w := Ne.symm fresh_w_ne_v
  have fresh_v_ne_u : v ≠ u :=
    by
    change freshVar proofSupport 5 ≠ freshVar proofSupport 6
    exact freshVar_injective proofSupport (i := 5) (j := 6) (by decide)
  have fresh_u_ne_v : u ≠ v := Ne.symm fresh_v_ne_u
  have dv_cache_0001 :
    t ∉
      ((syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun
                (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k
                            (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                                      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
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
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k
                      (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cimagek (syn_cun
                                    (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))))
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik
                              (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                                        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv))))))))))) (syn_cins2k (syn_cins3k (syn_cimak
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
                              (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_csik
                        (syn_csik (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
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
  have dv_cache_0003 : t ∉ ((syn_copk (.cv y) (.cv x))).fv :=
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
          Finset.mem_singleton, fresh_t_ne_y, fresh_t_ne_x, or_false, not_false_eq_true])
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
      ((Wff.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) (syn_ccompl (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cimak (syn_cin
                      (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k (syn_ccomk (syn_cssetk)
                                (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))))))) (syn_cins3k (syn_csik (syn_csik (syn_cimak
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
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k
                        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cimagek (syn_cun
                                      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik
                                (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv))))))))))) (syn_cins2k (syn_cins3k (syn_cimak
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
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k
                        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
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
          Finset.mem_singleton, fresh_z_ne_t, fresh_z_ne_y, fresh_z_ne_x,
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
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
          (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun
                  (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k
                              (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                                        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))))))) (syn_cins3k (syn_csik (syn_csik (syn_cimak
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
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k
                        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cimagek (syn_cun
                                      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik
                                (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv))))))))))) (syn_cins2k (syn_cins3k (syn_cimak
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
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k
                        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
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
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_y, fresh_t_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0008 :
    t ∉
      ((syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cimak (syn_cin
                (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik
                            (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
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
                            (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k (syn_csik
                    (syn_csik (syn_csik (syn_csik (syn_csik (syn_cimagek (syn_cun (syn_cin
                                  (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
            (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik
                          (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                                    (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                      (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                      (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))))
                    (syn_cins2k (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
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
                          (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_csik (syn_csik
                      (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                      (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_cpw1 (syn_cpw1
                  (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
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
  have dv_cache_0009 : t ∉ ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0010 :
    t ∉ ((syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_z, fresh_t_ne_y, fresh_t_ne_x, or_false,
          not_false_eq_true])
  have dv_cache_0011 : w ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_t, not_false_eq_true])
  have dv_cache_0012 :
    w ∉
      ((Wff.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cimak (syn_cin
                  (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik
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
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k (syn_csik
                      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cimagek (syn_cun (syn_cin
                                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik
                            (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                                      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))))
                      (syn_cins2k (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
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
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_csik (syn_csik
                        (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_cpw1 (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_t, fresh_w_ne_z, fresh_w_ne_y, fresh_w_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0013 :
    t ∉ ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_w,
          not_false_eq_true])
  have dv_cache_0014 :
    t ∉
      ((Wff.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
            (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cimak (syn_cin
                  (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik
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
                              (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k (syn_csik
                      (syn_csik (syn_csik (syn_csik (syn_csik (syn_cimagek (syn_cun (syn_cin
                                    (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
        (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                    (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                    (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
              (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik
                            (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                                      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))))
                      (syn_cins2k (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                              (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
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
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_csik (syn_csik
                        (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                  (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
                                        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin
        (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))
        (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k
        (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_cpw1 (syn_cpw1
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_z, fresh_t_ne_y, fresh_t_ne_x,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    t ∉
      ((syn_cin (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik
                      (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                  (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
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
                      (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k (syn_csik (syn_csik
                (syn_csik (syn_csik (syn_csik (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                              (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
                                        (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                      (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                                        (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                            (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                            (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 :
    t ∉
      ((syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c, compact_fv_not_mem_empty,
          not_false_eq_true])
  have dv_cache_0017 :
    t ∉
      ((syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
          (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_w, fresh_t_ne_z, fresh_t_ne_y, fresh_t_ne_x,
          or_false, not_false_eq_true])
  have dv_cache_0018 : v ∉ ((Class.cv t)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_t, not_false_eq_true])
  have dv_cache_0019 :
    v ∉
      ((Wff.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))) (syn_cin
            (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik
                        (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k (syn_csik (syn_csik
                  (syn_csik (syn_csik (syn_csik (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_t, fresh_v_ne_w, fresh_v_ne_z, fresh_v_ne_y,
          fresh_v_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0020 :
    t ∉
      ((syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton, fresh_t_ne_v,
          not_false_eq_true])
  have dv_cache_0021 :
    t ∉
      ((Wff.classMem (syn_copk
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))))
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))) (syn_cin
            (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k (syn_ccomk (syn_cssetk) (syn_csik
                        (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
                                    (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
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
                        (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k (syn_csik (syn_csik
                  (syn_csik (syn_csik (syn_csik (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                                (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                                        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
                                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
                                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                              (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                              (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_v, fresh_t_ne_w, fresh_t_ne_z, fresh_t_ne_y,
          fresh_t_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0022 : u ∉ ((Class.cv v)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_v, not_false_eq_true])
  have dv_cache_0023 : u ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_y, not_false_eq_true])
  have dv_cache_0024 : u ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : u ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_u_ne_z, not_false_eq_true])
  have dv_cache_0025 : v ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_y, not_false_eq_true])
  have dv_cache_0026 : v ∉ ((Class.cv z)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_v_ne_z, not_false_eq_true])
  have dv_cache_0027 : v ≠ u :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact (show v ≠ u from (by exact fresh_v_ne_u))
  have dv_cache_0028 :
    t ∉
      ((Wff.classMem (syn_copk
            (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))))
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))) (syn_cin
            (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik (syn_ccomk (syn_cssetk)
                        (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                                    (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))))
                (syn_cins2k (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
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
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_csik (syn_csik
                  (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
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
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_v, fresh_t_ne_w, fresh_t_ne_z, fresh_t_ne_y,
          fresh_t_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0029 : v ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028
    exact (show v ≠ w from (by exact fresh_v_ne_w))
  have dv_cache_0030 :
    t ∉
      ((syn_cin (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik (syn_ccomk (syn_cssetk)
                      (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                                  (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))))
              (syn_cins2k (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k
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
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_csik (syn_csik
                (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
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
                          (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0031 :
    v ∉
      ((Wff.classMem (syn_copk (.cv t)
            (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
              (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))) (syn_cin
            (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik (syn_ccomk (syn_cssetk)
                        (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
                                    (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                  (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                  (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))))))))
                (syn_cins2k (syn_cins3k (syn_cimak (syn_cin (syn_cins2k (syn_cssetk))
                        (syn_cins3k (syn_csik (syn_ccompl (syn_cimak
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
                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k (syn_csik (syn_csik
                  (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
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
                            (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_copk,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_t, fresh_v_ne_w, fresh_v_ne_z, fresh_v_ne_y,
          fresh_v_ne_x, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0032 : w ∉ ((syn_cop (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true])
  have dv_cache_0033 : v ∉ ((syn_cop (.cv y) (.cv z))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_y, fresh_v_ne_z, or_false, not_false_eq_true])
  have dv_cache_0034 : w ∉ ((syn_cop (.cv z) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_z, fresh_w_ne_y, or_false, not_false_eq_true])
  have dv_cache_0035 : v ∉ ((syn_cop (.cv z) (.cv y))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034
    exact
      (by
        have compact_fv_not_mem_empty : v ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_v_ne_z, fresh_v_ne_y, or_false, not_false_eq_true])
  have dv_cache_0036 : w ≠ v :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
    exact (show w ≠ v from (by exact fresh_w_ne_v))
  have dv_cache_0037 : w ∉ ((Class.cv x)).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0038 :
    w ∉ ((syn_cop (syn_cop (.cv y) (.cv z)) (syn_cop (.cv z) (.cv y)))).fv :=
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
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_y, fresh_w_ne_z, or_false, not_false_eq_true])
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
  have dv_cache_0040 : z ∉ ((Class.cv x)).fv :=
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
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0041 : y ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0027 dv_cache_0028 dv_cache_0029
      dv_cache_0030 dv_cache_0031 dv_cache_0032 dv_cache_0033 dv_cache_0034 dv_cache_0035
      dv_cache_0036 dv_cache_0037 dv_cache_0038 dv_cache_0039 dv_cache_0040
    exact (show y ≠ z from (by exact fresh_y_ne_z))
  have dv_cache_0042 :
    y ∉
      ((syn_cimak (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k
                              (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek (syn_cun
                                        (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))))))) (syn_cins3k (syn_csik (syn_csik (syn_cimak
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
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k
                        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cimagek (syn_cun
                                      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k
        (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
                                        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
                                        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))))
                    (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                  (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik
                                (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
                                        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv))))))))))) (syn_cins2k (syn_cins3k (syn_cimak
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
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k
                        (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_ccompl (syn_cimak
                                      (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k
        (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak
        (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                      (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_cpw1
                      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_c1c)))).fv :=
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
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
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
  have dv_cache_0043 : x ∉ ((syn_cswap)).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cswap,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0044 :
    x ∉
      ((syn_cimak (syn_cimak (syn_ccompl (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cimak (syn_cin
                        (syn_cins2k (syn_cun (syn_cins2k (syn_cins3k (syn_ccomk (syn_cssetk)
                                  (syn_csik (syn_ccnvk (syn_cimagek (syn_cun (syn_cin
        (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))))))) (syn_cins3k (syn_csik (syn_csik (syn_cimak
                                    (syn_cin (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_csik
        (syn_ccompl (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk)) (syn_cins3k (syn_cun
        (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k
        (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k
        (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k
        (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1
        (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
        (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)))))) (syn_cssetk))
        (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c))))))))) (syn_cins3k
                          (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_cimagek
                                      (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif
        (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k (syn_cssetk))
        (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif
        (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
        (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))))))))) (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
                    (syn_cimak (syn_cin (syn_cins2k (syn_cun (syn_cins3k (syn_csik (syn_csik
                                  (syn_ccomk (syn_cssetk) (syn_csik (syn_ccnvk (syn_cimagek
        (syn_cun (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak
        (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1
        (syn_cpw1 (syn_c1c)))))) (syn_cimak (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
        (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk))) (syn_cins3k (syn_csik
        (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk)
        (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))))))))) (syn_cins2k (syn_cins3k (syn_cimak
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
        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))))) (syn_cins3k
                          (syn_csik (syn_csik (syn_csik (syn_csik (syn_csik (syn_ccompl
                                      (syn_cimak (syn_csymdif (syn_cins2k (syn_cssetk))
        (syn_cins3k (syn_cun (syn_ccomk (syn_ccnvk (syn_cimagek (syn_cun (syn_cin (syn_cimagek
        (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl (syn_cimak (syn_cin (syn_cins3k
        (syn_cssetk)) (syn_cins2k (syn_cssetk))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
        (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) (syn_cun (syn_cins2k (syn_cins3k
        (syn_cssetk))) (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))) (syn_cpw1 (syn_cpw1
        (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_cpw1 (syn_c1c)))))
        (syn_cxpk (syn_cnnc) (syn_cvv))) (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc))
        (syn_cvv)))))) (syn_cssetk)) (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))))
                                        (syn_cpw1 (syn_cpw1 (syn_c1c)))))))))))) (syn_cpw1
                        (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cpw1 (syn_c1c)))
          (syn_cvv))).fv :=
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
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
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
  let syntaxClass0000 : Class :=
    (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
      (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0001 : Class := (syn_ccompl syntaxClass0000)
  let syntaxClass0002 : Class := (syn_cins3k syntaxClass0001)
  let syntaxClass0003 : Class :=
    (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
      (syn_cins3k (syn_csik (syn_csik (syn_cssetk)))))
  let syntaxClass0004 : Class :=
    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0003)
  let syntaxClass0005 : Class :=
    (syn_cimak syntaxClass0004 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  let syntaxClass0006 : Class := (syn_cdif syntaxClass0002 syntaxClass0005)
  let syntaxClass0007 : Class :=
    (syn_cimak syntaxClass0006 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0008 : Class := (syn_cimagek syntaxClass0007)
  let syntaxClass0009 : Class := (syn_cin syntaxClass0008 (syn_cxpk (syn_cnnc) (syn_cvv)))
  let syntaxClass0010 : Class :=
    (syn_cun syntaxClass0009 (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))))
  let syntaxClass0011 : Class := (syn_cimagek syntaxClass0010)
  let syntaxClass0012 : Class := (syn_ccnvk syntaxClass0011)
  let syntaxClass0013 : Class := (syn_csik syntaxClass0012)
  let syntaxClass0014 : Class := (syn_ccomk (syn_cssetk) syntaxClass0013)
  let syntaxClass0015 : Class := (syn_cins3k syntaxClass0014)
  let syntaxClass0016 : Class := (syn_cins2k syntaxClass0015)
  let syntaxClass0017 : Class := (syn_ccomk syntaxClass0012 (syn_cssetk))
  let syntaxClass0018 : Class :=
    (syn_cun syntaxClass0017 (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)))
  let syntaxClass0019 : Class := (syn_cins3k syntaxClass0018)
  let syntaxClass0020 : Class := (syn_csymdif (syn_cins2k (syn_cssetk)) syntaxClass0019)
  let syntaxClass0021 : Class :=
    (syn_cimak syntaxClass0020 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0022 : Class := (syn_ccompl syntaxClass0021)
  let syntaxClass0023 : Class := (syn_csik syntaxClass0022)
  let syntaxClass0024 : Class := (syn_cins3k syntaxClass0023)
  let syntaxClass0025 : Class := (syn_cin (syn_cins2k (syn_cssetk)) syntaxClass0024)
  let syntaxClass0026 : Class :=
    (syn_cimak syntaxClass0025 (syn_cpw1 (syn_cpw1 (syn_c1c))))
  let syntaxClass0027 : Class := (syn_csik syntaxClass0026)
  let syntaxClass0028 : Class := (syn_csik syntaxClass0027)
  let syntaxClass0029 : Class := (syn_cins3k syntaxClass0028)
  let syntaxClass0030 : Class := (syn_cun syntaxClass0016 syntaxClass0029)
  let syntaxClass0031 : Class := (syn_cins2k syntaxClass0030)
  let syntaxClass0032 : Class := (syn_csik syntaxClass0011)
  let syntaxClass0033 : Class := (syn_csik syntaxClass0032)
  let syntaxClass0034 : Class := (syn_csik syntaxClass0033)
  let syntaxClass0035 : Class := (syn_csik syntaxClass0034)
  let syntaxClass0036 : Class := (syn_csik syntaxClass0035)
  let syntaxClass0037 : Class := (syn_cins3k syntaxClass0036)
  let syntaxClass0038 : Class := (syn_cin syntaxClass0031 syntaxClass0037)
  let syntaxClass0039 : Class :=
    (syn_cimak syntaxClass0038
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  let syntaxClass0040 : Class := (syn_csik syntaxClass0014)
  let syntaxClass0041 : Class := (syn_csik syntaxClass0040)
  let syntaxClass0042 : Class := (syn_cins3k syntaxClass0041)
  let syntaxClass0043 : Class := (syn_cins3k syntaxClass0026)
  let syntaxClass0044 : Class := (syn_cins2k syntaxClass0043)
  let syntaxClass0045 : Class := (syn_cun syntaxClass0042 syntaxClass0044)
  let syntaxClass0046 : Class := (syn_cins2k syntaxClass0045)
  let syntaxClass0047 : Class := (syn_csik syntaxClass0023)
  let syntaxClass0048 : Class := (syn_csik syntaxClass0047)
  let syntaxClass0049 : Class := (syn_csik syntaxClass0048)
  let syntaxClass0050 : Class := (syn_csik syntaxClass0049)
  let syntaxClass0051 : Class := (syn_cins3k syntaxClass0050)
  let syntaxClass0052 : Class := (syn_cin syntaxClass0046 syntaxClass0051)
  let syntaxClass0053 : Class :=
    (syn_cimak syntaxClass0052
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  let syntaxClass0054 : Class := (syn_cun syntaxClass0039 syntaxClass0053)
  let syntaxClass0055 : Class :=
    (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0054)
  let syntaxClass0056 : Class :=
    (syn_cimak syntaxClass0055 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
  let syntaxClass0057 : Class := (syn_ccompl syntaxClass0056)
  let syntaxFormula0058 : Wff :=
    (.classMem (syn_copk (.cv t) (syn_copk (.cv y) (.cv x))) syntaxClass0057)
  let syntaxFormula0059 : Wff := (syn_wrex t (syn_cpw1 (syn_c1c)) syntaxFormula0058)
  let syntaxFormula0060 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_c1c))) syntaxFormula0058)
  let syntaxFormula0061 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (.cv z)))) syntaxFormula0058)
  let syntaxFormula0062 : Wff := (syn_wex z syntaxFormula0061)
  let syntaxFormula0063 : Wff := (syn_wex t syntaxFormula0060)
  let syntaxFormula0064 : Wff := (syn_wex t syntaxFormula0061)
  let syntaxFormula0065 : Wff := (syn_wex z syntaxFormula0064)
  let syntaxClass0066 : Class := (syn_cimak syntaxClass0057 (syn_cpw1 (syn_c1c)))
  let syntaxFormula0067 : Wff := (.classMem (syn_copk (.cv y) (.cv x)) syntaxClass0066)
  let syntaxFormula0068 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
      syntaxClass0057)
  let syntaxClass0069 : Class :=
    (syn_copk (.cv t) (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
  let syntaxFormula0070 : Wff := (.classMem syntaxClass0069 syntaxClass0055)
  let syntaxFormula0071 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) syntaxFormula0070)
  let syntaxFormula0072 : Wff :=
    (syn_wa (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      syntaxFormula0070)
  let syntaxFormula0073 : Wff :=
    (syn_wa (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
      syntaxFormula0070)
  let syntaxFormula0074 : Wff := (syn_wex w syntaxFormula0073)
  let syntaxFormula0075 : Wff := (syn_wex t syntaxFormula0072)
  let syntaxFormula0076 : Wff := (syn_wex t syntaxFormula0073)
  let syntaxFormula0077 : Wff := (syn_wex w syntaxFormula0076)
  let syntaxFormula0078 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
      syntaxClass0056)
  let syntaxClass0079 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
  let syntaxFormula0080 : Wff := (.classMem syntaxClass0079 syntaxClass0055)
  let syntaxFormula0081 : Wff :=
    (.classMem syntaxClass0079 (syn_cins2k (syn_cins2k (syn_cssetk))))
  let syntaxFormula0082 : Wff :=
    (.classMem (.cv t)
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))))
  let syntaxFormula0083 : Wff :=
    (.classEq (.cv t)
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v)))))))))
  let syntaxFormula0084 : Wff := (syn_wex v syntaxFormula0083)
  let syntaxClass0085 : Class := (syn_copk (.cv t) syntaxClass0079)
  let syntaxFormula0086 : Wff := (.classMem syntaxClass0085 syntaxClass0038)
  let syntaxFormula0087 : Wff := (syn_wa syntaxFormula0082 syntaxFormula0086)
  let syntaxFormula0088 : Wff := (syn_wa syntaxFormula0083 syntaxFormula0086)
  let syntaxFormula0089 : Wff := (syn_wex v syntaxFormula0088)
  let syntaxFormula0090 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      syntaxFormula0086)
  let syntaxFormula0091 : Wff := (syn_wex t syntaxFormula0088)
  let syntaxFormula0092 : Wff := (syn_wex v syntaxFormula0091)
  let syntaxClass0093 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))))
      syntaxClass0079)
  let syntaxFormula0094 : Wff := (.classMem syntaxClass0093 syntaxClass0038)
  let syntaxClass0095 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))))
  let syntaxFormula0096 : Wff := (.classMem syntaxClass0095 syntaxClass0016)
  let syntaxFormula0097 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv v))) (syn_csn (.cv z))) syntaxClass0027)
  let syntaxFormula0098 : Wff :=
    (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cun (syn_cphi (.cv u)) (syn_csn (syn_c0c)))))
  let syntaxFormula0099 : Wff := (.classMem syntaxClass0095 syntaxClass0029)
  let syntaxFormula0100 : Wff := (.classMem syntaxClass0095 syntaxClass0030)
  let syntaxFormula0101 : Wff :=
    (syn_wo (syn_wrex u (.cv y) (.classEq (.cv v) (syn_cphi (.cv u)))) syntaxFormula0098)
  let syntaxClass0102 : Class := (.cab v syntaxFormula0098)
  let syntaxClass0103 : Class :=
    (syn_cun (.cab v (syn_wrex u (.cv y) (.classEq (.cv v) (syn_cphi (.cv u)))))
      syntaxClass0102)
  let syntaxFormula0104 : Wff := (.classMem syntaxClass0093 syntaxClass0031)
  let syntaxClass0105 : Class := (syn_cimak syntaxClass0010 (.cv v))
  let syntaxFormula0106 : Wff := (.classMem (syn_copk (.cv v) (.cv w)) syntaxClass0011)
  let syntaxFormula0107 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv v))) (syn_csn (syn_csn (.cv w))))
      syntaxClass0033)
  let syntaxClass0108 : Class :=
    (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (.cv v)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
  let syntaxFormula0109 : Wff := (.classMem syntaxClass0108 syntaxClass0035)
  let syntaxFormula0110 : Wff := (.classMem syntaxClass0093 syntaxClass0037)
  let syntaxFormula0111 : Wff :=
    (syn_wa (.classMem (.cv v) (syn_cop (.cv y) (.cv z))) (.classEq (.cv w) (syn_cphi (.cv v))))
  let syntaxFormula0112 : Wff := (.classMem syntaxClass0079 syntaxClass0039)
  let syntaxFormula0113 : Wff := (.classMem syntaxClass0085 syntaxClass0052)
  let syntaxFormula0114 : Wff := (.classMem syntaxClass0093 syntaxClass0052)
  let syntaxFormula0115 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv v))) (syn_csn (.cv z))) syntaxClass0040)
  let syntaxFormula0116 : Wff := (.classMem syntaxClass0095 syntaxClass0042)
  let syntaxFormula0117 : Wff := (.classMem syntaxClass0095 syntaxClass0044)
  let syntaxFormula0118 : Wff :=
    (syn_wrex u (.cv y) (.classEq (.cv v) (syn_cun (syn_cphi (.cv u)) (syn_csn (syn_c0c)))))
  let syntaxFormula0119 : Wff := (.classMem syntaxClass0093 syntaxClass0046)
  let syntaxFormula0120 : Wff :=
    (syn_wo (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cphi (.cv u)))) syntaxFormula0118)
  let syntaxClass0121 : Class := (.cab v syntaxFormula0118)
  let syntaxClass0122 : Class :=
    (syn_cun (.cab v (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cphi (.cv u)))))
      syntaxClass0121)
  let syntaxFormula0123 : Wff :=
    (.classMem (syn_copk (syn_csn (syn_csn (.cv v))) (syn_csn (syn_csn (.cv w))))
      syntaxClass0047)
  let syntaxFormula0124 : Wff := (.classMem syntaxClass0108 syntaxClass0049)
  let syntaxFormula0125 : Wff := (.classMem syntaxClass0093 syntaxClass0051)
  let syntaxFormula0126 : Wff := (syn_wa syntaxFormula0083 syntaxFormula0113)
  let syntaxFormula0127 : Wff := (syn_wex t syntaxFormula0126)
  let syntaxFormula0128 : Wff :=
    (syn_wa (.classMem (.cv v) (syn_cop (.cv z) (.cv y)))
      (.classEq (.cv w) (syn_cun (syn_cphi (.cv v)) (syn_csn (syn_c0c)))))
  let syntaxFormula0129 : Wff :=
    (syn_wrex t (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      syntaxFormula0113)
  let syntaxFormula0130 : Wff := (syn_wa syntaxFormula0082 syntaxFormula0113)
  let syntaxFormula0131 : Wff := (syn_wex v syntaxFormula0126)
  let syntaxFormula0132 : Wff := (syn_wex t syntaxFormula0131)
  let syntaxFormula0133 : Wff := (.classMem syntaxClass0079 syntaxClass0053)
  let syntaxFormula0134 : Wff := (syn_wex v syntaxFormula0127)
  let syntaxFormula0135 : Wff :=
    (syn_wrex v (syn_cop (.cv z) (.cv y))
      (.classEq (.cv w) (syn_cun (syn_cphi (.cv v)) (syn_csn (syn_c0c)))))
  let syntaxClass0136 : Class :=
    (.cab w (syn_wrex v (syn_cop (.cv y) (.cv z)) (.classEq (.cv w) (syn_cphi (.cv v)))))
  let syntaxClass0137 : Class := (.cab w syntaxFormula0135)
  let syntaxClass0138 : Class := (syn_cun syntaxClass0136 syntaxClass0137)
  let syntaxFormula0139 : Wff :=
    (.classMem (.cv w) (syn_cop (syn_cop (.cv y) (.cv z)) (syn_cop (.cv z) (.cv y))))
  let syntaxFormula0140 : Wff :=
    (syn_wo (syn_wrex v (syn_cop (.cv y) (.cv z)) (.classEq (.cv w) (syn_cphi (.cv v))))
      syntaxFormula0135)
  let syntaxFormula0141 : Wff := (.classMem syntaxClass0079 syntaxClass0054)
  let syntaxFormula0142 : Wff := (syn_wb syntaxFormula0081 syntaxFormula0141)
  let syntaxFormula0143 : Wff :=
    (.classEq (.cv x) (syn_cop (syn_cop (.cv y) (.cv z)) (syn_cop (.cv z) (.cv y))))
  let syntaxClass0144 : Class := (syn_cimak syntaxClass0066 (syn_cvv))
  have p0000 := @g_opkex (.cv y) (.cv x)
  have p0001 :=
    @g_elimak t syntaxClass0057 (syn_cpw1 (syn_c1c)) (syn_copk (.cv y) (.cv x))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0002 := (Nominal.biimpRefl syntaxFormula0059)
  have p0003 := @g_elpw11c z (.cv t) dv_cache_0004
  have p0004 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_c1c)))
      (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))) syntaxFormula0058 p0003
  have p0005 :=
    @g_n_19_41v (.classEq (.cv t) (syn_csn (syn_csn (.cv z)))) syntaxFormula0058 z
      dv_cache_0005
  have p0006 :=
    @g_bitr4i syntaxFormula0060
      (syn_wa (syn_wex z (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))) syntaxFormula0058)
      syntaxFormula0062 p0004 p0005
  have p0007 := @g_exbii syntaxFormula0060 syntaxFormula0062 t p0006
  have p0008 := @g_excom syntaxFormula0061 z t
  have p0009 :=
    @g_bitr4i syntaxFormula0063 (syn_wex t syntaxFormula0062) syntaxFormula0065 p0007
      p0008
  have p0010 :=
    @g_n_3bitri syntaxFormula0067 syntaxFormula0059 syntaxFormula0063 syntaxFormula0065
      p0001 p0002 p0009
  have p0011 := @g_snex (syn_csn (.cv z))
  have p0012 := @g_opkeq1 (.cv t) (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))
  have p0013 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (.cv z))))
      (syn_copk (.cv t) (syn_copk (.cv y) (.cv x)))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) syntaxClass0057
      p0012
  have p0014 :=
    @g_ceqsexv syntaxFormula0058 syntaxFormula0068 t (syn_csn (syn_csn (.cv z)))
      dv_cache_0006 dv_cache_0007 p0011 p0013
  have p0015 := @g_opkex (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))
  have p0016 :=
    @g_elimak t syntaxClass0055 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) dv_cache_0008
      dv_cache_0009 dv_cache_0010 p0015
  have p0017 := (Nominal.biimpRefl syntaxFormula0071)
  have p0018 := @g_elpw141c w (.cv t) dv_cache_0011
  have p0019 :=
    @g_anbi1i (.classMem (.cv t) (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))
      (syn_wex w (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))))
      syntaxFormula0070 p0018
  have p0020 :=
    @g_n_19_41v
      (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
      syntaxFormula0070 w dv_cache_0012
  have p0021 :=
    @g_bitr4i syntaxFormula0072
      (syn_wa (syn_wex w
          (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))))
        syntaxFormula0070)
      syntaxFormula0074 p0019 p0020
  have p0022 := @g_exbii syntaxFormula0072 syntaxFormula0074 t p0021
  have p0023 := @g_excom syntaxFormula0073 w t
  have p0024 :=
    @g_bitr4i syntaxFormula0075 (syn_wex t syntaxFormula0074) syntaxFormula0077 p0022
      p0023
  have p0025 :=
    @g_n_3bitri syntaxFormula0078 syntaxFormula0071 syntaxFormula0075 syntaxFormula0077
      p0016 p0017 p0024
  have p0026 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))
  have p0027 :=
    @g_opkeq1 (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
  have p0028 :=
    @g_eleq1d (.classEq (.cv t) (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))))
      syntaxClass0069 syntaxClass0079 syntaxClass0055 p0027
  have p0029 :=
    @g_ceqsexv syntaxFormula0070 syntaxFormula0080 t
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w)))))) dv_cache_0013
      dv_cache_0014 p0026 p0028
  have p0030 :=
    @g_elsymdif syntaxClass0079 (syn_cins2k (syn_cins2k (syn_cssetk))) syntaxClass0054
  have p0031 := @g_snex (syn_csn (syn_csn (.cv w)))
  have p0032 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv w)))) (syn_csn (syn_csn (.cv z)))
      (syn_copk (.cv y) (.cv x)) (syn_cins2k (syn_cssetk)) p0031 p0011 p0000
  have p0033 := @g_snex (.cv w)
  have p0034 := @g_vex y
  have p0035 := @g_vex x
  have p0036 :=
    @g_otkelins2k (syn_csn (.cv w)) (.cv y) (.cv x) (syn_cssetk) p0033 p0034 p0035
  have p0037 := @g_vex w
  have p0038 := @g_elssetk (.cv w) (.cv x) p0037 p0035
  have p0039_e02_recanon :
    Nominal.NPrf
      (syn_wb (.classMem (syn_copk (syn_csn (.cv w)) (.cv x)) (syn_cssetk)) (.objMem w x)) :=
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
      p0038
  have p0039 :=
    @g_n_3bitri syntaxFormula0081
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv w)))) (syn_copk (.cv y) (.cv x)))
        (syn_cins2k (syn_cssetk)))
      (.classMem (syn_copk (syn_csn (.cv w)) (.cv x)) (syn_cssetk)) (.objMem w x) p0032
      p0036 p0039_e02_recanon
  have p0040 :=
    @g_opkex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
  have p0041 :=
    @g_elimak t syntaxClass0038
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      syntaxClass0079 dv_cache_0015 dv_cache_0016 dv_cache_0017 p0040
  have p0042 := @g_elpw161c v (.cv t) dv_cache_0018
  have p0043 := @g_anbi1i syntaxFormula0082 syntaxFormula0084 syntaxFormula0086 p0042
  have p0044 := @g_n_19_41v syntaxFormula0083 syntaxFormula0086 v dv_cache_0019
  have p0045 :=
    @g_bitr4i syntaxFormula0087 (syn_wa syntaxFormula0084 syntaxFormula0086)
      syntaxFormula0089 p0043 p0044
  have p0046 := @g_exbii syntaxFormula0087 syntaxFormula0089 t p0045
  have p0047 := (Nominal.biimpRefl syntaxFormula0090)
  have p0048 := @g_excom syntaxFormula0088 v t
  have p0049 :=
    @g_n_3bitr4i (syn_wex t syntaxFormula0087) (syn_wex t syntaxFormula0089)
      syntaxFormula0090 syntaxFormula0092 p0046 p0047 p0048
  have p0050 :=
    @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v)))))))
  have p0051 :=
    @g_opkeq1 (.cv t)
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))))
      syntaxClass0079
  have p0052 :=
    @g_eleq1d syntaxFormula0083 syntaxClass0085 syntaxClass0093 syntaxClass0038 p0051
  have p0053 :=
    @g_ceqsexv syntaxFormula0086 syntaxFormula0094 t
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))))
      dv_cache_0020 dv_cache_0021 p0050 p0052
  have p0054 := @g_elin syntaxClass0093 syntaxClass0031 syntaxClass0037
  have p0055 := @g_elun syntaxClass0095 syntaxClass0016 syntaxClass0029
  have p0056 := @g_snex (syn_csn (syn_csn (.cv v)))
  have p0057 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv v)))) (syn_csn (syn_csn (.cv z)))
      (syn_copk (.cv y) (.cv x)) syntaxClass0015 p0056 p0011 p0000
  have p0058 := @g_snex (.cv v)
  have p0059 :=
    @g_otkelins3k (syn_csn (.cv v)) (.cv y) (.cv x) syntaxClass0014 p0058 p0034 p0035
  have p0060 := @g_vex v
  have p0061 := @g_setconslem1 u (.cv v) (.cv y) dv_cache_0022 dv_cache_0023 p0060 p0034
  have p0062 :=
    @g_n_3bitri syntaxFormula0096
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv v)))) (syn_copk (.cv y) (.cv x)))
        syntaxClass0015)
      (.classMem (syn_copk (syn_csn (.cv v)) (.cv y)) syntaxClass0014)
      (syn_wrex u (.cv y) (.classEq (.cv v) (syn_cphi (.cv u)))) p0057 p0059 p0061
  have p0063 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (.cv v)))) (syn_csn (syn_csn (.cv z)))
      (syn_copk (.cv y) (.cv x)) syntaxClass0028 p0056 p0011 p0000
  have p0064 := @g_snex (syn_csn (.cv v))
  have p0065 := @g_snex (.cv z)
  have p0066 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv v))) (syn_csn (.cv z)) syntaxClass0027 p0064
      p0065
  have p0067 := @g_vex z
  have p0068 := @g_opksnelsik (syn_csn (.cv v)) (.cv z) syntaxClass0026 p0058 p0067
  have p0069 := @g_setconslem2 u (.cv v) (.cv z) dv_cache_0022 dv_cache_0024 p0060 p0067
  have p0070 :=
    @g_bitri syntaxFormula0097
      (.classMem (syn_copk (syn_csn (.cv v)) (.cv z)) syntaxClass0026) syntaxFormula0098
      p0068 p0069
  have p0071 :=
    @g_n_3bitri syntaxFormula0099
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv v)))) (syn_csn (syn_csn (.cv z))))
        syntaxClass0028)
      syntaxFormula0097 syntaxFormula0098 p0063 p0066 p0070
  have p0072 :=
    @g_orbi12i syntaxFormula0096
      (syn_wrex u (.cv y) (.classEq (.cv v) (syn_cphi (.cv u)))) syntaxFormula0099
      syntaxFormula0098 p0062 p0071
  have p0073 :=
    @g_bitri syntaxFormula0100 (syn_wo syntaxFormula0096 syntaxFormula0099)
      syntaxFormula0101 p0055 p0072
  have p0074 := @g_snex (syn_csn (syn_csn (syn_csn (syn_csn (.cv v)))))
  have p0075 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) syntaxClass0030
      p0074 p0026 p0015
  have p0076 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op v u (.cv y)
      (.cv z) dv_cache_0025 dv_cache_0023 dv_cache_0026 dv_cache_0024 dv_cache_0027
  have p0077 := @g_eleq2i (syn_cop (.cv y) (.cv z)) syntaxClass0103 (.cv v) p0076
  have p0078 :=
    @g_elun (.cv v) (.cab v (syn_wrex u (.cv y) (.classEq (.cv v) (syn_cphi (.cv u)))))
      syntaxClass0102
  have p0079 := @g_abid (syn_wrex u (.cv y) (.classEq (.cv v) (syn_cphi (.cv u)))) v
  have p0080 := @g_abid syntaxFormula0098 v
  have p0081 :=
    @g_orbi12i
      (.classMem (.cv v) (.cab v (syn_wrex u (.cv y) (.classEq (.cv v) (syn_cphi (.cv u))))))
      (syn_wrex u (.cv y) (.classEq (.cv v) (syn_cphi (.cv u))))
      (.classMem (.cv v) syntaxClass0102) syntaxFormula0098 p0079 p0080
  have p0082 :=
    @g_n_3bitri (.classMem (.cv v) (syn_cop (.cv y) (.cv z)))
      (.classMem (.cv v) syntaxClass0103)
      (syn_wo (.classMem (.cv v)
          (.cab v (syn_wrex u (.cv y) (.classEq (.cv v) (syn_cphi (.cv u))))))
        (.classMem (.cv v) syntaxClass0102))
      syntaxFormula0101 p0077 p0078 p0081
  have p0083 :=
    @g_n_3bitr4i syntaxFormula0100 syntaxFormula0101 syntaxFormula0104
      (.classMem (.cv v) (syn_cop (.cv y) (.cv z))) p0073 p0075 p0082
  have p0084 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) syntaxClass0036
      p0074 p0026 p0015
  have p0085 := @g_snex (syn_csn (syn_csn (syn_csn (.cv v))))
  have p0086 := @g_snex (syn_csn (syn_csn (syn_csn (.cv w))))
  have p0087 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv v)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))) syntaxClass0035 p0085 p0086
  have p0088 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv v))))
      (syn_csn (syn_csn (syn_csn (.cv w)))) syntaxClass0034 p0056 p0031
  have p0089 := @g_snex (syn_csn (.cv w))
  have p0090 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv v))) (syn_csn (syn_csn (.cv w))) syntaxClass0033
      p0064 p0089
  have p0091 :=
    @g_opksnelsik (syn_csn (.cv v)) (syn_csn (.cv w)) syntaxClass0032 p0058 p0033
  have p0092 := @g_opksnelsik (.cv v) (.cv w) syntaxClass0011 p0060 p0037
  have p0093 := @g_opkelimagek (.cv v) (.cv w) syntaxClass0010 p0060 p0037
  have p0094 := @g_dfphi2 (.cv v)
  have p0095 := @g_eqeq2i (syn_cphi (.cv v)) syntaxClass0105 (.cv w) p0094
  have p0096 :=
    @g_bitr4i syntaxFormula0106 (.classEq (.cv w) syntaxClass0105)
      (.classEq (.cv w) (syn_cphi (.cv v))) p0093 p0095
  have p0097 :=
    @g_n_3bitri syntaxFormula0107
      (.classMem (syn_copk (syn_csn (.cv v)) (syn_csn (.cv w))) syntaxClass0032)
      syntaxFormula0106 (.classEq (.cv w) (syn_cphi (.cv v))) p0091 p0092 p0096
  have p0098 :=
    @g_n_3bitri syntaxFormula0109
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv v))))
          (syn_csn (syn_csn (syn_csn (.cv w))))) syntaxClass0034)
      syntaxFormula0107 (.classEq (.cv w) (syn_cphi (.cv v))) p0088 p0090 p0097
  have p0099 :=
    @g_n_3bitri syntaxFormula0110
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))) syntaxClass0036)
      syntaxFormula0109 (.classEq (.cv w) (syn_cphi (.cv v))) p0084 p0087 p0098
  have p0100 :=
    @g_anbi12i syntaxFormula0104 (.classMem (.cv v) (syn_cop (.cv y) (.cv z)))
      syntaxFormula0110 (.classEq (.cv w) (syn_cphi (.cv v))) p0083 p0099
  have p0101 :=
    @g_n_3bitri syntaxFormula0091 syntaxFormula0094
      (syn_wa syntaxFormula0104 syntaxFormula0110) syntaxFormula0111 p0053 p0054 p0100
  have p0102 := @g_exbii syntaxFormula0091 syntaxFormula0111 v p0101
  have p0103 :=
    @g_n_3bitri syntaxFormula0112 syntaxFormula0090 syntaxFormula0092
      (syn_wex v syntaxFormula0111) p0041 p0049 p0102
  have p0104 :=
    (Nominal.biimpRefl
      (syn_wrex v (syn_cop (.cv y) (.cv z)) (.classEq (.cv w) (syn_cphi (.cv v)))))
  have p0105 :=
    @g_bitr4i syntaxFormula0112 (syn_wex v syntaxFormula0111)
      (syn_wrex v (syn_cop (.cv y) (.cv z)) (.classEq (.cv w) (syn_cphi (.cv v)))) p0103
      p0104
  have p0106 :=
    @g_eleq1d syntaxFormula0083 syntaxClass0085 syntaxClass0093 syntaxClass0052 p0051
  have p0107 :=
    @g_ceqsexv syntaxFormula0113 syntaxFormula0114 t
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))))
      dv_cache_0020 dv_cache_0028 p0050 p0106
  have p0108 := @g_elin syntaxClass0093 syntaxClass0046 syntaxClass0051
  have p0109 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) syntaxClass0045
      p0074 p0026 p0015
  have p0110 := @g_elun syntaxClass0095 syntaxClass0042 syntaxClass0044
  have p0111 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (.cv v)))) (syn_csn (syn_csn (.cv z)))
      (syn_copk (.cv y) (.cv x)) syntaxClass0041 p0056 p0011 p0000
  have p0112 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv v))) (syn_csn (.cv z)) syntaxClass0040 p0064
      p0065
  have p0113 := @g_opksnelsik (syn_csn (.cv v)) (.cv z) syntaxClass0014 p0058 p0067
  have p0114 := @g_setconslem1 u (.cv v) (.cv z) dv_cache_0022 dv_cache_0024 p0060 p0067
  have p0115 :=
    @g_bitri syntaxFormula0115
      (.classMem (syn_copk (syn_csn (.cv v)) (.cv z)) syntaxClass0014)
      (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cphi (.cv u)))) p0113 p0114
  have p0116 :=
    @g_n_3bitri syntaxFormula0116
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv v)))) (syn_csn (syn_csn (.cv z))))
        syntaxClass0041)
      syntaxFormula0115 (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cphi (.cv u)))) p0111
      p0112 p0115
  have p0117 :=
    @g_otkelins2k (syn_csn (syn_csn (syn_csn (.cv v)))) (syn_csn (syn_csn (.cv z)))
      (syn_copk (.cv y) (.cv x)) syntaxClass0043 p0056 p0011 p0000
  have p0118 :=
    @g_otkelins3k (syn_csn (.cv v)) (.cv y) (.cv x) syntaxClass0026 p0058 p0034 p0035
  have p0119 := @g_setconslem2 u (.cv v) (.cv y) dv_cache_0022 dv_cache_0023 p0060 p0034
  have p0120 :=
    @g_n_3bitri syntaxFormula0117
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv v)))) (syn_copk (.cv y) (.cv x)))
        syntaxClass0043)
      (.classMem (syn_copk (syn_csn (.cv v)) (.cv y)) syntaxClass0026) syntaxFormula0118
      p0117 p0118 p0119
  have p0121 :=
    @g_orbi12i syntaxFormula0116
      (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cphi (.cv u)))) syntaxFormula0117
      syntaxFormula0118 p0116 p0120
  have p0122 :=
    @g_n_3bitri syntaxFormula0119 (.classMem syntaxClass0095 syntaxClass0045)
      (syn_wo syntaxFormula0116 syntaxFormula0117) syntaxFormula0120 p0109 p0110 p0121
  have p0123 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op v u (.cv z)
      (.cv y) dv_cache_0026 dv_cache_0024 dv_cache_0025 dv_cache_0023 dv_cache_0027
  have p0124 := @g_eleq2i (syn_cop (.cv z) (.cv y)) syntaxClass0122 (.cv v) p0123
  have p0125 :=
    @g_elun (.cv v) (.cab v (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cphi (.cv u)))))
      syntaxClass0121
  have p0126 := @g_abid (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cphi (.cv u)))) v
  have p0127 := @g_abid syntaxFormula0118 v
  have p0128 :=
    @g_orbi12i
      (.classMem (.cv v) (.cab v (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cphi (.cv u))))))
      (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cphi (.cv u))))
      (.classMem (.cv v) syntaxClass0121) syntaxFormula0118 p0126 p0127
  have p0129 :=
    @g_n_3bitri (.classMem (.cv v) (syn_cop (.cv z) (.cv y)))
      (.classMem (.cv v) syntaxClass0122)
      (syn_wo (.classMem (.cv v)
          (.cab v (syn_wrex u (.cv z) (.classEq (.cv v) (syn_cphi (.cv u))))))
        (.classMem (.cv v) syntaxClass0121))
      syntaxFormula0120 p0124 p0125 p0128
  have p0130 :=
    @g_bitr4i syntaxFormula0119 syntaxFormula0120
      (.classMem (.cv v) (syn_cop (.cv z) (.cv y))) p0122 p0129
  have p0131 :=
    @g_otkelins3k (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))
      (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))
      (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x))) syntaxClass0050
      p0074 p0026 p0015
  have p0132 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (syn_csn (.cv v)))))
      (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))) syntaxClass0049 p0085 p0086
  have p0133 :=
    @g_opksnelsik (syn_csn (syn_csn (syn_csn (.cv v))))
      (syn_csn (syn_csn (syn_csn (.cv w)))) syntaxClass0048 p0056 p0031
  have p0134 :=
    @g_opksnelsik (syn_csn (syn_csn (.cv v))) (syn_csn (syn_csn (.cv w))) syntaxClass0047
      p0064 p0089
  have p0135 :=
    @g_opksnelsik (syn_csn (.cv v)) (syn_csn (.cv w)) syntaxClass0023 p0058 p0033
  have p0136 := @g_opksnelsik (.cv v) (.cv w) syntaxClass0022 p0060 p0037
  have p0137 := @g_dfop2lem1 v w dv_cache_0029
  have p0138 :=
    @g_n_3bitri syntaxFormula0123
      (.classMem (syn_copk (syn_csn (.cv v)) (syn_csn (.cv w))) syntaxClass0023)
      (.classMem (syn_copk (.cv v) (.cv w)) syntaxClass0022)
      (.classEq (.cv w) (syn_cun (syn_cphi (.cv v)) (syn_csn (syn_c0c)))) p0135 p0136
      p0137
  have p0139 :=
    @g_n_3bitri syntaxFormula0124
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (.cv v))))
          (syn_csn (syn_csn (syn_csn (.cv w))))) syntaxClass0048)
      syntaxFormula0123
      (.classEq (.cv w) (syn_cun (syn_cphi (.cv v)) (syn_csn (syn_c0c)))) p0133 p0134
      p0138
  have p0140 :=
    @g_n_3bitri syntaxFormula0125
      (.classMem (syn_copk (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv v))))))
          (syn_csn (syn_csn (syn_csn (syn_csn (syn_csn (.cv w))))))) syntaxClass0050)
      syntaxFormula0124
      (.classEq (.cv w) (syn_cun (syn_cphi (.cv v)) (syn_csn (syn_c0c)))) p0131 p0132
      p0139
  have p0141 :=
    @g_anbi12i syntaxFormula0119 (.classMem (.cv v) (syn_cop (.cv z) (.cv y)))
      syntaxFormula0125
      (.classEq (.cv w) (syn_cun (syn_cphi (.cv v)) (syn_csn (syn_c0c)))) p0130 p0140
  have p0142 :=
    @g_n_3bitri syntaxFormula0127 syntaxFormula0114
      (syn_wa syntaxFormula0119 syntaxFormula0125) syntaxFormula0128 p0107 p0108 p0141
  have p0143 := @g_exbii syntaxFormula0127 syntaxFormula0128 v p0142
  have p0144 :=
    @g_elimak t syntaxClass0052
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      syntaxClass0079 dv_cache_0030 dv_cache_0016 dv_cache_0017 p0040
  have p0145 := (Nominal.biimpRefl syntaxFormula0129)
  have p0146 := @g_anbi1i syntaxFormula0082 syntaxFormula0084 syntaxFormula0113 p0042
  have p0147 := @g_n_19_41v syntaxFormula0083 syntaxFormula0113 v dv_cache_0031
  have p0148 :=
    @g_bitr4i syntaxFormula0130 (syn_wa syntaxFormula0084 syntaxFormula0113)
      syntaxFormula0131 p0146 p0147
  have p0149 := @g_exbii syntaxFormula0130 syntaxFormula0131 t p0148
  have p0150 :=
    @g_bitri syntaxFormula0129 (syn_wex t syntaxFormula0130) syntaxFormula0132 p0145 p0149
  have p0151 := @g_excom syntaxFormula0126 t v
  have p0152 :=
    @g_n_3bitri syntaxFormula0133 syntaxFormula0129 syntaxFormula0132 syntaxFormula0134
      p0144 p0150 p0151
  have p0153 := (Nominal.biimpRefl syntaxFormula0135)
  have p0154 :=
    @g_n_3bitr4i syntaxFormula0134 (syn_wex v syntaxFormula0128) syntaxFormula0133
      syntaxFormula0135 p0143 p0152 p0153
  have p0155 :=
    @g_orbi12i syntaxFormula0112
      (syn_wrex v (syn_cop (.cv y) (.cv z)) (.classEq (.cv w) (syn_cphi (.cv v))))
      syntaxFormula0133 syntaxFormula0135 p0105 p0154
  have p0156 := @g_elun syntaxClass0079 syntaxClass0039 syntaxClass0053
  have p0157 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominal_df_op w v
      (syn_cop (.cv y) (.cv z)) (syn_cop (.cv z) (.cv y)) dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0035 dv_cache_0036
  have p0158 :=
    @g_eleq2i (syn_cop (syn_cop (.cv y) (.cv z)) (syn_cop (.cv z) (.cv y)))
      syntaxClass0138 (.cv w) p0157
  have p0159 := @g_elun (.cv w) syntaxClass0136 syntaxClass0137
  have p0160 :=
    @g_abid (syn_wrex v (syn_cop (.cv y) (.cv z)) (.classEq (.cv w) (syn_cphi (.cv v)))) w
  have p0161 := @g_abid syntaxFormula0135 w
  have p0162 :=
    @g_orbi12i (.classMem (.cv w) syntaxClass0136)
      (syn_wrex v (syn_cop (.cv y) (.cv z)) (.classEq (.cv w) (syn_cphi (.cv v))))
      (.classMem (.cv w) syntaxClass0137) syntaxFormula0135 p0160 p0161
  have p0163 :=
    @g_n_3bitri syntaxFormula0139 (.classMem (.cv w) syntaxClass0138)
      (syn_wo (.classMem (.cv w) syntaxClass0136) (.classMem (.cv w) syntaxClass0137))
      syntaxFormula0140 p0158 p0159 p0162
  have p0164 :=
    @g_n_3bitr4i (syn_wo syntaxFormula0112 syntaxFormula0133) syntaxFormula0140
      syntaxFormula0141 syntaxFormula0139 p0155 p0156 p0163
  have p0165 :=
    @g_bibi12i syntaxFormula0081 (.objMem w x) syntaxFormula0141 syntaxFormula0139 p0039
      p0164
  have p0166 := @g_notbii syntaxFormula0142 (syn_wb (.objMem w x) syntaxFormula0139) p0165
  have p0167 :=
    @g_n_3bitri syntaxFormula0076 syntaxFormula0080 (.neg syntaxFormula0142)
      (.neg (syn_wb (.objMem w x) syntaxFormula0139)) p0029 p0030 p0166
  have p0168 :=
    @g_exbii syntaxFormula0076 (.neg (syn_wb (.objMem w x) syntaxFormula0139)) w p0167
  have p0169 := @g_exnal (syn_wb (.objMem w x) syntaxFormula0139) w
  have p0170 :=
    @g_n_3bitri syntaxFormula0078 syntaxFormula0077
      (syn_wex w (.neg (syn_wb (.objMem w x) syntaxFormula0139)))
      (.neg (.all w (syn_wb (.objMem w x) syntaxFormula0139))) p0025 p0168 p0169
  have p0171 :=
    @g_con2bii syntaxFormula0078 (.all w (syn_wb (.objMem w x) syntaxFormula0139)) p0170
  have p0172 :=
    @g_dfcleq w (.cv x) (syn_cop (syn_cop (.cv y) (.cv z)) (syn_cop (.cv z) (.cv y)))
      dv_cache_0037 dv_cache_0038
  have p0173 :=
    @g_elcompl (syn_copk (syn_csn (syn_csn (.cv z))) (syn_copk (.cv y) (.cv x)))
      syntaxClass0056 p0015
  have p0174_e01_recanon :
    Nominal.NPrf
      (syn_wb syntaxFormula0143 (.all w (syn_wb (.objMem w x) syntaxFormula0139))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [syn_wb, syn_cop, syn_cun, syn_cnin, syn_wnan, syn_wa, syn_ccompl,
          syn_wrex, syn_wex, syn_cphi]
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
      p0172
  have p0174 :=
    @g_n_3bitr4ri (.all w (syn_wb (.objMem w x) syntaxFormula0139))
      (.neg syntaxFormula0078) syntaxFormula0143 syntaxFormula0068 p0171 p0174_e01_recanon
      p0173
  have p0175 := @g_bitri syntaxFormula0064 syntaxFormula0068 syntaxFormula0143 p0014 p0174
  have p0176 := @g_exbii syntaxFormula0064 syntaxFormula0143 z p0175
  have p0177 :=
    @g_bitr2i syntaxFormula0067 syntaxFormula0065 (syn_wex z syntaxFormula0143) p0010
      p0176
  have p0178 := @g_exbii (syn_wex z syntaxFormula0143) syntaxFormula0067 y p0177
  have p0179 := @g_elswap y z (.cv x) dv_cache_0039 dv_cache_0040 dv_cache_0041
  have p0180 := @g_elimakv y syntaxClass0066 (.cv x) dv_cache_0042 dv_cache_0039 p0035
  have p0181 :=
    @g_n_3bitr4i (syn_wex y (syn_wex z syntaxFormula0143)) (syn_wex y syntaxFormula0067)
      (.classMem (.cv x) (syn_cswap)) (.classMem (.cv x) syntaxClass0144) p0178 p0179
      p0180
  have p0182 := @g_eqriv x (syn_cswap) syntaxClass0144 dv_cache_0043 dv_cache_0044 p0181
  exact p0182


end NFChoice.DirectNominalPrf.WPPReplay
