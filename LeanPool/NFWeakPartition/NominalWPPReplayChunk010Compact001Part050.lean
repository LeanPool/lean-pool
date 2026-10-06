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

/-- Checked nominal proof certificate identified upstream as `g_dfswap2`. -/
@[expose]
noncomputable def gDfswap2 :
    Nominal.NPrf
      (.classEq (synCswap) (synCimak (synCimak (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCimak (synCin
                        (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk)
                                  (synCsik (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))))))) (synCins3k (synCsik (synCsik (synCimak
                                    (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
        (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
        (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k
                          (synCsik (synCsik (synCsik (synCsik (synCsik (synCimagek
                                      (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))))))))) (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik
        (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))) (synCins2k (synCins3k (synCimak
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
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k
                          (synCsik (synCsik (synCsik (synCsik (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k
        (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
        (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k
        (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))
          (synCvv))) :=
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
      ((synCcompl (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
                (synCimak (synCin (synCins2k (synCun (synCins2k (synCins3k
                            (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                                      (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k
                      (synCsik (synCsik (synCsik (synCsik (synCsik (synCimagek (synCun
                                    (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                              (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                                        (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv))))))))))) (synCins2k (synCins3k (synCimak
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
                              (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCsik
                        (synCsik (synCsik (synCsik (synCsik (synCcompl (synCimak
                                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
        (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                    (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
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
  have dv_cache_0003 : t ∉ ((synCopk (.cv y) (.cv x))).fv :=
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
      ((Wff.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) (synCcompl (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCimak (synCin
                      (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk)
                                (synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))))))) (synCins3k (synCsik (synCsik (synCimak
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
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k
                        (synCsik (synCsik (synCsik (synCsik (synCsik (synCimagek (synCun
                                      (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                        (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv))))))))))) (synCins2k (synCins3k (synCimak
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
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k
                        (synCsik (synCsik (synCsik (synCsik (synCsik (synCcompl (synCimak
                                      (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
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
      ((Wff.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
          (synCcompl (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
                  (synCimak (synCin (synCins2k (synCun (synCins2k (synCins3k
                              (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                                        (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))))))) (synCins3k (synCsik (synCsik (synCimak
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
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k
                        (synCsik (synCsik (synCsik (synCsik (synCsik (synCimagek (synCun
                                      (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                        (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv))))))))))) (synCins2k (synCins3k (synCimak
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
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k
                        (synCsik (synCsik (synCsik (synCsik (synCsik (synCcompl (synCimak
                                      (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
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
      ((synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCimak (synCin
                (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik
                            (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                        (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
                            (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k (synCsik
                    (synCsik (synCsik (synCsik (synCsik (synCimagek (synCun (synCin
                                  (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                          (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                                    (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                      (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                      (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
                    (synCins2k (synCins3k (synCimak (synCin (synCins2k (synCssetk))
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
                          (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCsik (synCsik
                      (synCsik (synCsik (synCsik (synCcompl (synCimak
                                (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                      (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1 (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))).fv :=
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
  have dv_cache_0009 : t ∉ ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))).fv :=
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
    t ∉ ((synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))).fv :=
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
      ((Wff.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCimak (synCin
                  (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik
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
                              (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k (synCsik
                      (synCsik (synCsik (synCsik (synCsik (synCimagek (synCun (synCin
                                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                            (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                                      (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
                      (synCins2k (synCins3k (synCimak (synCin (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCcompl (synCimak
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
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCsik (synCsik
                        (synCsik (synCsik (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1 (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))).fv :=
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
    t ∉ ((synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))).fv :=
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
      ((Wff.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
            (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
          (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCimak (synCin
                  (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik
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
                              (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k (synCsik
                      (synCsik (synCsik (synCsik (synCsik (synCimagek (synCun (synCin
                                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                            (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                                      (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
                      (synCins2k (synCins3k (synCimak (synCin (synCins2k (synCssetk))
                              (synCins3k (synCsik (synCcompl (synCimak
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
                            (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCsik (synCsik
                        (synCsik (synCsik (synCsik (synCcompl (synCimak
                                  (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
                                        (synCcomk (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                  (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1 (synCpw1
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))))).fv :=
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
      ((synCin (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik
                      (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                  (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
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
                      (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k (synCsik (synCsik
                (synCsik (synCsik (synCsik (synCimagek (synCun (synCin (synCimagek
                              (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))).fv :=
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
      ((synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))).fv :=
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
      ((synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
          (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))).fv :=
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
      ((Wff.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))) (synCin
            (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik
                        (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                    (synCdif (synCins3k (synCcompl (synCimak
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
                        (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k (synCsik (synCsik
                  (synCsik (synCsik (synCsik (synCimagek (synCun (synCin (synCimagek
                                (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))))).fv :=
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
      ((synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))))).fv :=
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
      ((Wff.classMem (synCopk
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))))
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))) (synCin
            (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik
                        (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                    (synCdif (synCins3k (synCcompl (synCimak
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
                        (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k (synCsik (synCsik
                  (synCsik (synCsik (synCsik (synCimagek (synCun (synCin (synCimagek
                                (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))))).fv :=
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
      ((Wff.classMem (synCopk
            (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))))
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))) (synCin
            (synCins2k (synCun (synCins3k (synCsik (synCsik (synCcomk (synCssetk)
                        (synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek
                                    (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
                (synCins2k (synCins3k (synCimak (synCin (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCcompl (synCimak
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
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCsik (synCsik
                  (synCsik (synCsik (synCsik (synCcompl (synCimak
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
                            (synCpw1 (synCpw1 (synC1c)))))))))))))).fv :=
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
      ((synCin (synCins2k (synCun (synCins3k (synCsik (synCsik (synCcomk (synCssetk)
                      (synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek
                                  (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
              (synCins2k (synCins3k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
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
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCsik (synCsik
                (synCsik (synCsik (synCsik (synCcompl (synCimak
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
                          (synCpw1 (synCpw1 (synC1c))))))))))))).fv :=
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
      ((Wff.classMem (synCopk (.cv t)
            (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
              (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))) (synCin
            (synCins2k (synCun (synCins3k (synCsik (synCsik (synCcomk (synCssetk)
                        (synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek
                                    (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                  (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                  (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
                (synCins2k (synCins3k (synCimak (synCin (synCins2k (synCssetk))
                        (synCins3k (synCsik (synCcompl (synCimak
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
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCsik (synCsik
                  (synCsik (synCsik (synCsik (synCcompl (synCimak
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
                            (synCpw1 (synCpw1 (synC1c)))))))))))))).fv :=
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
  have dv_cache_0032 : w ∉ ((synCop (.cv y) (.cv z))).fv :=
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
  have dv_cache_0033 : v ∉ ((synCop (.cv y) (.cv z))).fv :=
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
  have dv_cache_0034 : w ∉ ((synCop (.cv z) (.cv y))).fv :=
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
  have dv_cache_0035 : v ∉ ((synCop (.cv z) (.cv y))).fv :=
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
    w ∉ ((synCop (synCop (.cv y) (.cv z)) (synCop (.cv z) (.cv y)))).fv :=
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
      ((synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCimak (synCin (synCins2k (synCun (synCins2k (synCins3k
                              (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                                        (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))))))) (synCins3k (synCsik (synCsik (synCimak
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
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k
                        (synCsik (synCsik (synCsik (synCsik (synCsik (synCimagek (synCun
                                      (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                                (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                                        (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv))))))))))) (synCins2k (synCins3k (synCimak
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
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k
                        (synCsik (synCsik (synCsik (synCsik (synCsik (synCcompl (synCimak
                                      (synCsymdif (synCins2k (synCssetk)) (synCins3k
        (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                      (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synC1c)))).fv :=
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
  have dv_cache_0043 : x ∉ ((synCswap)).fv :=
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
      ((synCimak (synCimak (synCcompl (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCimak (synCin
                        (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk)
                                  (synCsik (synCcnvk (synCimagek (synCun (synCin
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))))))) (synCins3k (synCsik (synCsik (synCimak
                                    (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
        (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun
        (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k
        (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1
        (synC1c))))))) (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
        (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))) (synCssetk))
        (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k
                          (synCsik (synCsik (synCsik (synCsik (synCsik (synCimagek
                                      (synCun (synCin (synCimagek (synCimak (synCdif
        (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))))))))) (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                    (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                                  (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
        (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1
        (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
        (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k (synCsik
        (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
        (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))) (synCins2k (synCins3k (synCimak
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
        (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k
                          (synCsik (synCsik (synCsik (synCsik (synCsik (synCcompl
                                      (synCimak (synCsymdif (synCins2k (synCssetk))
        (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k
        (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
        (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k
        (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                                        (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))
          (synCvv))).fv :=
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
    (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
      (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0001 : Class := (synCcompl syntaxClass0000)
  let syntaxClass0002 : Class := (synCins3k syntaxClass0001)
  let syntaxClass0003 : Class :=
    (synCun (synCins2k (synCins3k (synCssetk)))
      (synCins3k (synCsik (synCsik (synCssetk)))))
  let syntaxClass0004 : Class :=
    (synCsymdif (synCins2k (synCins2k (synCssetk))) syntaxClass0003)
  let syntaxClass0005 : Class :=
    (synCimak syntaxClass0004 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  let syntaxClass0006 : Class := (synCdif syntaxClass0002 syntaxClass0005)
  let syntaxClass0007 : Class :=
    (synCimak syntaxClass0006 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0008 : Class := (synCimagek syntaxClass0007)
  let syntaxClass0009 : Class := (synCin syntaxClass0008 (synCxpk (synCnnc) (synCvv)))
  let syntaxClass0010 : Class :=
    (synCun syntaxClass0009 (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))
  let syntaxClass0011 : Class := (synCimagek syntaxClass0010)
  let syntaxClass0012 : Class := (synCcnvk syntaxClass0011)
  let syntaxClass0013 : Class := (synCsik syntaxClass0012)
  let syntaxClass0014 : Class := (synCcomk (synCssetk) syntaxClass0013)
  let syntaxClass0015 : Class := (synCins3k syntaxClass0014)
  let syntaxClass0016 : Class := (synCins2k syntaxClass0015)
  let syntaxClass0017 : Class := (synCcomk syntaxClass0012 (synCssetk))
  let syntaxClass0018 : Class :=
    (synCun syntaxClass0017 (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))
  let syntaxClass0019 : Class := (synCins3k syntaxClass0018)
  let syntaxClass0020 : Class := (synCsymdif (synCins2k (synCssetk)) syntaxClass0019)
  let syntaxClass0021 : Class :=
    (synCimak syntaxClass0020 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0022 : Class := (synCcompl syntaxClass0021)
  let syntaxClass0023 : Class := (synCsik syntaxClass0022)
  let syntaxClass0024 : Class := (synCins3k syntaxClass0023)
  let syntaxClass0025 : Class := (synCin (synCins2k (synCssetk)) syntaxClass0024)
  let syntaxClass0026 : Class :=
    (synCimak syntaxClass0025 (synCpw1 (synCpw1 (synC1c))))
  let syntaxClass0027 : Class := (synCsik syntaxClass0026)
  let syntaxClass0028 : Class := (synCsik syntaxClass0027)
  let syntaxClass0029 : Class := (synCins3k syntaxClass0028)
  let syntaxClass0030 : Class := (synCun syntaxClass0016 syntaxClass0029)
  let syntaxClass0031 : Class := (synCins2k syntaxClass0030)
  let syntaxClass0032 : Class := (synCsik syntaxClass0011)
  let syntaxClass0033 : Class := (synCsik syntaxClass0032)
  let syntaxClass0034 : Class := (synCsik syntaxClass0033)
  let syntaxClass0035 : Class := (synCsik syntaxClass0034)
  let syntaxClass0036 : Class := (synCsik syntaxClass0035)
  let syntaxClass0037 : Class := (synCins3k syntaxClass0036)
  let syntaxClass0038 : Class := (synCin syntaxClass0031 syntaxClass0037)
  let syntaxClass0039 : Class :=
    (synCimak syntaxClass0038
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  let syntaxClass0040 : Class := (synCsik syntaxClass0014)
  let syntaxClass0041 : Class := (synCsik syntaxClass0040)
  let syntaxClass0042 : Class := (synCins3k syntaxClass0041)
  let syntaxClass0043 : Class := (synCins3k syntaxClass0026)
  let syntaxClass0044 : Class := (synCins2k syntaxClass0043)
  let syntaxClass0045 : Class := (synCun syntaxClass0042 syntaxClass0044)
  let syntaxClass0046 : Class := (synCins2k syntaxClass0045)
  let syntaxClass0047 : Class := (synCsik syntaxClass0023)
  let syntaxClass0048 : Class := (synCsik syntaxClass0047)
  let syntaxClass0049 : Class := (synCsik syntaxClass0048)
  let syntaxClass0050 : Class := (synCsik syntaxClass0049)
  let syntaxClass0051 : Class := (synCins3k syntaxClass0050)
  let syntaxClass0052 : Class := (synCin syntaxClass0046 syntaxClass0051)
  let syntaxClass0053 : Class :=
    (synCimak syntaxClass0052
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  let syntaxClass0054 : Class := (synCun syntaxClass0039 syntaxClass0053)
  let syntaxClass0055 : Class :=
    (synCsymdif (synCins2k (synCins2k (synCssetk))) syntaxClass0054)
  let syntaxClass0056 : Class :=
    (synCimak syntaxClass0055 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
  let syntaxClass0057 : Class := (synCcompl syntaxClass0056)
  let syntaxFormula0058 : Wff :=
    (.classMem (synCopk (.cv t) (synCopk (.cv y) (.cv x))) syntaxClass0057)
  let syntaxFormula0059 : Wff := (synWrex t (synCpw1 (synC1c)) syntaxFormula0058)
  let syntaxFormula0060 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synC1c))) syntaxFormula0058)
  let syntaxFormula0061 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (.cv z)))) syntaxFormula0058)
  let syntaxFormula0062 : Wff := (synWex z syntaxFormula0061)
  let syntaxFormula0063 : Wff := (synWex t syntaxFormula0060)
  let syntaxFormula0064 : Wff := (synWex t syntaxFormula0061)
  let syntaxFormula0065 : Wff := (synWex z syntaxFormula0064)
  let syntaxClass0066 : Class := (synCimak syntaxClass0057 (synCpw1 (synC1c)))
  let syntaxFormula0067 : Wff := (.classMem (synCopk (.cv y) (.cv x)) syntaxClass0066)
  let syntaxFormula0068 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
      syntaxClass0057)
  let syntaxClass0069 : Class :=
    (synCopk (.cv t) (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
  let syntaxFormula0070 : Wff := (.classMem syntaxClass0069 syntaxClass0055)
  let syntaxFormula0071 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) syntaxFormula0070)
  let syntaxFormula0072 : Wff :=
    (synWa (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      syntaxFormula0070)
  let syntaxFormula0073 : Wff :=
    (synWa (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
      syntaxFormula0070)
  let syntaxFormula0074 : Wff := (synWex w syntaxFormula0073)
  let syntaxFormula0075 : Wff := (synWex t syntaxFormula0072)
  let syntaxFormula0076 : Wff := (synWex t syntaxFormula0073)
  let syntaxFormula0077 : Wff := (synWex w syntaxFormula0076)
  let syntaxFormula0078 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
      syntaxClass0056)
  let syntaxClass0079 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
  let syntaxFormula0080 : Wff := (.classMem syntaxClass0079 syntaxClass0055)
  let syntaxFormula0081 : Wff :=
    (.classMem syntaxClass0079 (synCins2k (synCins2k (synCssetk))))
  let syntaxFormula0082 : Wff :=
    (.classMem (.cv t)
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
  let syntaxFormula0083 : Wff :=
    (.classEq (.cv t)
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v)))))))))
  let syntaxFormula0084 : Wff := (synWex v syntaxFormula0083)
  let syntaxClass0085 : Class := (synCopk (.cv t) syntaxClass0079)
  let syntaxFormula0086 : Wff := (.classMem syntaxClass0085 syntaxClass0038)
  let syntaxFormula0087 : Wff := (synWa syntaxFormula0082 syntaxFormula0086)
  let syntaxFormula0088 : Wff := (synWa syntaxFormula0083 syntaxFormula0086)
  let syntaxFormula0089 : Wff := (synWex v syntaxFormula0088)
  let syntaxFormula0090 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      syntaxFormula0086)
  let syntaxFormula0091 : Wff := (synWex t syntaxFormula0088)
  let syntaxFormula0092 : Wff := (synWex v syntaxFormula0091)
  let syntaxClass0093 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))))
      syntaxClass0079)
  let syntaxFormula0094 : Wff := (.classMem syntaxClass0093 syntaxClass0038)
  let syntaxClass0095 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))))
  let syntaxFormula0096 : Wff := (.classMem syntaxClass0095 syntaxClass0016)
  let syntaxFormula0097 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv v))) (synCsn (.cv z))) syntaxClass0027)
  let syntaxFormula0098 : Wff :=
    (synWrex u (.cv z) (.classEq (.cv v) (synCun (synCphi (.cv u)) (synCsn (synC0c)))))
  let syntaxFormula0099 : Wff := (.classMem syntaxClass0095 syntaxClass0029)
  let syntaxFormula0100 : Wff := (.classMem syntaxClass0095 syntaxClass0030)
  let syntaxFormula0101 : Wff :=
    (synWo (synWrex u (.cv y) (.classEq (.cv v) (synCphi (.cv u)))) syntaxFormula0098)
  let syntaxClass0102 : Class := (.cab v syntaxFormula0098)
  let syntaxClass0103 : Class :=
    (synCun (.cab v (synWrex u (.cv y) (.classEq (.cv v) (synCphi (.cv u)))))
      syntaxClass0102)
  let syntaxFormula0104 : Wff := (.classMem syntaxClass0093 syntaxClass0031)
  let syntaxClass0105 : Class := (synCimak syntaxClass0010 (.cv v))
  let syntaxFormula0106 : Wff := (.classMem (synCopk (.cv v) (.cv w)) syntaxClass0011)
  let syntaxFormula0107 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv v))) (synCsn (synCsn (.cv w))))
      syntaxClass0033)
  let syntaxClass0108 : Class :=
    (synCopk (synCsn (synCsn (synCsn (synCsn (.cv v)))))
      (synCsn (synCsn (synCsn (synCsn (.cv w))))))
  let syntaxFormula0109 : Wff := (.classMem syntaxClass0108 syntaxClass0035)
  let syntaxFormula0110 : Wff := (.classMem syntaxClass0093 syntaxClass0037)
  let syntaxFormula0111 : Wff :=
    (synWa (.classMem (.cv v) (synCop (.cv y) (.cv z))) (.classEq (.cv w) (synCphi (.cv v))))
  let syntaxFormula0112 : Wff := (.classMem syntaxClass0079 syntaxClass0039)
  let syntaxFormula0113 : Wff := (.classMem syntaxClass0085 syntaxClass0052)
  let syntaxFormula0114 : Wff := (.classMem syntaxClass0093 syntaxClass0052)
  let syntaxFormula0115 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv v))) (synCsn (.cv z))) syntaxClass0040)
  let syntaxFormula0116 : Wff := (.classMem syntaxClass0095 syntaxClass0042)
  let syntaxFormula0117 : Wff := (.classMem syntaxClass0095 syntaxClass0044)
  let syntaxFormula0118 : Wff :=
    (synWrex u (.cv y) (.classEq (.cv v) (synCun (synCphi (.cv u)) (synCsn (synC0c)))))
  let syntaxFormula0119 : Wff := (.classMem syntaxClass0093 syntaxClass0046)
  let syntaxFormula0120 : Wff :=
    (synWo (synWrex u (.cv z) (.classEq (.cv v) (synCphi (.cv u)))) syntaxFormula0118)
  let syntaxClass0121 : Class := (.cab v syntaxFormula0118)
  let syntaxClass0122 : Class :=
    (synCun (.cab v (synWrex u (.cv z) (.classEq (.cv v) (synCphi (.cv u)))))
      syntaxClass0121)
  let syntaxFormula0123 : Wff :=
    (.classMem (synCopk (synCsn (synCsn (.cv v))) (synCsn (synCsn (.cv w))))
      syntaxClass0047)
  let syntaxFormula0124 : Wff := (.classMem syntaxClass0108 syntaxClass0049)
  let syntaxFormula0125 : Wff := (.classMem syntaxClass0093 syntaxClass0051)
  let syntaxFormula0126 : Wff := (synWa syntaxFormula0083 syntaxFormula0113)
  let syntaxFormula0127 : Wff := (synWex t syntaxFormula0126)
  let syntaxFormula0128 : Wff :=
    (synWa (.classMem (.cv v) (synCop (.cv z) (.cv y)))
      (.classEq (.cv w) (synCun (synCphi (.cv v)) (synCsn (synC0c)))))
  let syntaxFormula0129 : Wff :=
    (synWrex t (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      syntaxFormula0113)
  let syntaxFormula0130 : Wff := (synWa syntaxFormula0082 syntaxFormula0113)
  let syntaxFormula0131 : Wff := (synWex v syntaxFormula0126)
  let syntaxFormula0132 : Wff := (synWex t syntaxFormula0131)
  let syntaxFormula0133 : Wff := (.classMem syntaxClass0079 syntaxClass0053)
  let syntaxFormula0134 : Wff := (synWex v syntaxFormula0127)
  let syntaxFormula0135 : Wff :=
    (synWrex v (synCop (.cv z) (.cv y))
      (.classEq (.cv w) (synCun (synCphi (.cv v)) (synCsn (synC0c)))))
  let syntaxClass0136 : Class :=
    (.cab w (synWrex v (synCop (.cv y) (.cv z)) (.classEq (.cv w) (synCphi (.cv v)))))
  let syntaxClass0137 : Class := (.cab w syntaxFormula0135)
  let syntaxClass0138 : Class := (synCun syntaxClass0136 syntaxClass0137)
  let syntaxFormula0139 : Wff :=
    (.classMem (.cv w) (synCop (synCop (.cv y) (.cv z)) (synCop (.cv z) (.cv y))))
  let syntaxFormula0140 : Wff :=
    (synWo (synWrex v (synCop (.cv y) (.cv z)) (.classEq (.cv w) (synCphi (.cv v))))
      syntaxFormula0135)
  let syntaxFormula0141 : Wff := (.classMem syntaxClass0079 syntaxClass0054)
  let syntaxFormula0142 : Wff := (synWb syntaxFormula0081 syntaxFormula0141)
  let syntaxFormula0143 : Wff :=
    (.classEq (.cv x) (synCop (synCop (.cv y) (.cv z)) (synCop (.cv z) (.cv y))))
  let syntaxClass0144 : Class := (synCimak syntaxClass0066 (synCvv))
  have p0000 := @gOpkex (.cv y) (.cv x)
  have p0001 :=
    @gElimak t syntaxClass0057 (synCpw1 (synC1c)) (synCopk (.cv y) (.cv x))
      dv_cache_0001 dv_cache_0002 dv_cache_0003 p0000
  have p0002 := (Nominal.biimpRefl syntaxFormula0059)
  have p0003 := @gElpw11c z (.cv t) dv_cache_0004
  have p0004 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synC1c)))
      (synWex z (.classEq (.cv t) (synCsn (synCsn (.cv z))))) syntaxFormula0058 p0003
  have p0005 :=
    @gN1941v (.classEq (.cv t) (synCsn (synCsn (.cv z)))) syntaxFormula0058 z
      dv_cache_0005
  have p0006 :=
    @gBitr4i syntaxFormula0060
      (synWa (synWex z (.classEq (.cv t) (synCsn (synCsn (.cv z))))) syntaxFormula0058)
      syntaxFormula0062 p0004 p0005
  have p0007 := @gExbii syntaxFormula0060 syntaxFormula0062 t p0006
  have p0008 := @gExcom syntaxFormula0061 z t
  have p0009 :=
    @gBitr4i syntaxFormula0063 (synWex t syntaxFormula0062) syntaxFormula0065 p0007
      p0008
  have p0010 :=
    @gN3bitri syntaxFormula0067 syntaxFormula0059 syntaxFormula0063 syntaxFormula0065
      p0001 p0002 p0009
  have p0011 := @gSnex (synCsn (.cv z))
  have p0012 := @gOpkeq1 (.cv t) (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))
  have p0013 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (.cv z))))
      (synCopk (.cv t) (synCopk (.cv y) (.cv x)))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) syntaxClass0057
      p0012
  have p0014 :=
    @gCeqsexv syntaxFormula0058 syntaxFormula0068 t (synCsn (synCsn (.cv z)))
      dv_cache_0006 dv_cache_0007 p0011 p0013
  have p0015 := @gOpkex (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))
  have p0016 :=
    @gElimak t syntaxClass0055 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) dv_cache_0008
      dv_cache_0009 dv_cache_0010 p0015
  have p0017 := (Nominal.biimpRefl syntaxFormula0071)
  have p0018 := @gElpw141c w (.cv t) dv_cache_0011
  have p0019 :=
    @gAnbi1i (.classMem (.cv t) (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      (synWex w (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))))
      syntaxFormula0070 p0018
  have p0020 :=
    @gN1941v
      (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
      syntaxFormula0070 w dv_cache_0012
  have p0021 :=
    @gBitr4i syntaxFormula0072
      (synWa (synWex w
          (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))))
        syntaxFormula0070)
      syntaxFormula0074 p0019 p0020
  have p0022 := @gExbii syntaxFormula0072 syntaxFormula0074 t p0021
  have p0023 := @gExcom syntaxFormula0073 w t
  have p0024 :=
    @gBitr4i syntaxFormula0075 (synWex t syntaxFormula0074) syntaxFormula0077 p0022
      p0023
  have p0025 :=
    @gN3bitri syntaxFormula0078 syntaxFormula0071 syntaxFormula0075 syntaxFormula0077
      p0016 p0017 p0024
  have p0026 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv w)))))
  have p0027 :=
    @gOpkeq1 (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
  have p0028 :=
    @gEleq1d (.classEq (.cv t) (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))))
      syntaxClass0069 syntaxClass0079 syntaxClass0055 p0027
  have p0029 :=
    @gCeqsexv syntaxFormula0070 syntaxFormula0080 t
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w)))))) dv_cache_0013
      dv_cache_0014 p0026 p0028
  have p0030 :=
    @gElsymdif syntaxClass0079 (synCins2k (synCins2k (synCssetk))) syntaxClass0054
  have p0031 := @gSnex (synCsn (synCsn (.cv w)))
  have p0032 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv w)))) (synCsn (synCsn (.cv z)))
      (synCopk (.cv y) (.cv x)) (synCins2k (synCssetk)) p0031 p0011 p0000
  have p0033 := @gSnex (.cv w)
  have p0034 := @gVex y
  have p0035 := @gVex x
  have p0036 :=
    @gOtkelins2k (synCsn (.cv w)) (.cv y) (.cv x) (synCssetk) p0033 p0034 p0035
  have p0037 := @gVex w
  have p0038 := @gElssetk (.cv w) (.cv x) p0037 p0035
  have p0039_e02_recanon :
    Nominal.NPrf
      (synWb (.classMem (synCopk (synCsn (.cv w)) (.cv x)) (synCssetk)) (.objMem w x)) :=
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
      p0038
  have p0039 :=
    @gN3bitri syntaxFormula0081
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv w)))) (synCopk (.cv y) (.cv x)))
        (synCins2k (synCssetk)))
      (.classMem (synCopk (synCsn (.cv w)) (.cv x)) (synCssetk)) (.objMem w x) p0032
      p0036 p0039_e02_recanon
  have p0040 :=
    @gOpkex (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
  have p0041 :=
    @gElimak t syntaxClass0038
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      syntaxClass0079 dv_cache_0015 dv_cache_0016 dv_cache_0017 p0040
  have p0042 := @gElpw161c v (.cv t) dv_cache_0018
  have p0043 := @gAnbi1i syntaxFormula0082 syntaxFormula0084 syntaxFormula0086 p0042
  have p0044 := @gN1941v syntaxFormula0083 syntaxFormula0086 v dv_cache_0019
  have p0045 :=
    @gBitr4i syntaxFormula0087 (synWa syntaxFormula0084 syntaxFormula0086)
      syntaxFormula0089 p0043 p0044
  have p0046 := @gExbii syntaxFormula0087 syntaxFormula0089 t p0045
  have p0047 := (Nominal.biimpRefl syntaxFormula0090)
  have p0048 := @gExcom syntaxFormula0088 v t
  have p0049 :=
    @gN3bitr4i (synWex t syntaxFormula0087) (synWex t syntaxFormula0089)
      syntaxFormula0090 syntaxFormula0092 p0046 p0047 p0048
  have p0050 :=
    @gSnex (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v)))))))
  have p0051 :=
    @gOpkeq1 (.cv t)
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))))
      syntaxClass0079
  have p0052 :=
    @gEleq1d syntaxFormula0083 syntaxClass0085 syntaxClass0093 syntaxClass0038 p0051
  have p0053 :=
    @gCeqsexv syntaxFormula0086 syntaxFormula0094 t
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))))
      dv_cache_0020 dv_cache_0021 p0050 p0052
  have p0054 := @gElin syntaxClass0093 syntaxClass0031 syntaxClass0037
  have p0055 := @gElun syntaxClass0095 syntaxClass0016 syntaxClass0029
  have p0056 := @gSnex (synCsn (synCsn (.cv v)))
  have p0057 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv v)))) (synCsn (synCsn (.cv z)))
      (synCopk (.cv y) (.cv x)) syntaxClass0015 p0056 p0011 p0000
  have p0058 := @gSnex (.cv v)
  have p0059 :=
    @gOtkelins3k (synCsn (.cv v)) (.cv y) (.cv x) syntaxClass0014 p0058 p0034 p0035
  have p0060 := @gVex v
  have p0061 := @gSetconslem1 u (.cv v) (.cv y) dv_cache_0022 dv_cache_0023 p0060 p0034
  have p0062 :=
    @gN3bitri syntaxFormula0096
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv v)))) (synCopk (.cv y) (.cv x)))
        syntaxClass0015)
      (.classMem (synCopk (synCsn (.cv v)) (.cv y)) syntaxClass0014)
      (synWrex u (.cv y) (.classEq (.cv v) (synCphi (.cv u)))) p0057 p0059 p0061
  have p0063 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (.cv v)))) (synCsn (synCsn (.cv z)))
      (synCopk (.cv y) (.cv x)) syntaxClass0028 p0056 p0011 p0000
  have p0064 := @gSnex (synCsn (.cv v))
  have p0065 := @gSnex (.cv z)
  have p0066 :=
    @gOpksnelsik (synCsn (synCsn (.cv v))) (synCsn (.cv z)) syntaxClass0027 p0064
      p0065
  have p0067 := @gVex z
  have p0068 := @gOpksnelsik (synCsn (.cv v)) (.cv z) syntaxClass0026 p0058 p0067
  have p0069 := @gSetconslem2 u (.cv v) (.cv z) dv_cache_0022 dv_cache_0024 p0060 p0067
  have p0070 :=
    @gBitri syntaxFormula0097
      (.classMem (synCopk (synCsn (.cv v)) (.cv z)) syntaxClass0026) syntaxFormula0098
      p0068 p0069
  have p0071 :=
    @gN3bitri syntaxFormula0099
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv v)))) (synCsn (synCsn (.cv z))))
        syntaxClass0028)
      syntaxFormula0097 syntaxFormula0098 p0063 p0066 p0070
  have p0072 :=
    @gOrbi12i syntaxFormula0096
      (synWrex u (.cv y) (.classEq (.cv v) (synCphi (.cv u)))) syntaxFormula0099
      syntaxFormula0098 p0062 p0071
  have p0073 :=
    @gBitri syntaxFormula0100 (synWo syntaxFormula0096 syntaxFormula0099)
      syntaxFormula0101 p0055 p0072
  have p0074 := @gSnex (synCsn (synCsn (synCsn (synCsn (.cv v)))))
  have p0075 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) syntaxClass0030
      p0074 p0026 p0015
  have p0076 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOp v u (.cv y)
      (.cv z) dv_cache_0025 dv_cache_0023 dv_cache_0026 dv_cache_0024 dv_cache_0027
  have p0077 := @gEleq2i (synCop (.cv y) (.cv z)) syntaxClass0103 (.cv v) p0076
  have p0078 :=
    @gElun (.cv v) (.cab v (synWrex u (.cv y) (.classEq (.cv v) (synCphi (.cv u)))))
      syntaxClass0102
  have p0079 := @gAbid (synWrex u (.cv y) (.classEq (.cv v) (synCphi (.cv u)))) v
  have p0080 := @gAbid syntaxFormula0098 v
  have p0081 :=
    @gOrbi12i
      (.classMem (.cv v) (.cab v (synWrex u (.cv y) (.classEq (.cv v) (synCphi (.cv u))))))
      (synWrex u (.cv y) (.classEq (.cv v) (synCphi (.cv u))))
      (.classMem (.cv v) syntaxClass0102) syntaxFormula0098 p0079 p0080
  have p0082 :=
    @gN3bitri (.classMem (.cv v) (synCop (.cv y) (.cv z)))
      (.classMem (.cv v) syntaxClass0103)
      (synWo (.classMem (.cv v)
          (.cab v (synWrex u (.cv y) (.classEq (.cv v) (synCphi (.cv u))))))
        (.classMem (.cv v) syntaxClass0102))
      syntaxFormula0101 p0077 p0078 p0081
  have p0083 :=
    @gN3bitr4i syntaxFormula0100 syntaxFormula0101 syntaxFormula0104
      (.classMem (.cv v) (synCop (.cv y) (.cv z))) p0073 p0075 p0082
  have p0084 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) syntaxClass0036
      p0074 p0026 p0015
  have p0085 := @gSnex (synCsn (synCsn (synCsn (.cv v))))
  have p0086 := @gSnex (synCsn (synCsn (synCsn (.cv w))))
  have p0087 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (.cv v)))))
      (synCsn (synCsn (synCsn (synCsn (.cv w))))) syntaxClass0035 p0085 p0086
  have p0088 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (.cv v))))
      (synCsn (synCsn (synCsn (.cv w)))) syntaxClass0034 p0056 p0031
  have p0089 := @gSnex (synCsn (.cv w))
  have p0090 :=
    @gOpksnelsik (synCsn (synCsn (.cv v))) (synCsn (synCsn (.cv w))) syntaxClass0033
      p0064 p0089
  have p0091 :=
    @gOpksnelsik (synCsn (.cv v)) (synCsn (.cv w)) syntaxClass0032 p0058 p0033
  have p0092 := @gOpksnelsik (.cv v) (.cv w) syntaxClass0011 p0060 p0037
  have p0093 := @gOpkelimagek (.cv v) (.cv w) syntaxClass0010 p0060 p0037
  have p0094 := @gDfphi2 (.cv v)
  have p0095 := @gEqeq2i (synCphi (.cv v)) syntaxClass0105 (.cv w) p0094
  have p0096 :=
    @gBitr4i syntaxFormula0106 (.classEq (.cv w) syntaxClass0105)
      (.classEq (.cv w) (synCphi (.cv v))) p0093 p0095
  have p0097 :=
    @gN3bitri syntaxFormula0107
      (.classMem (synCopk (synCsn (.cv v)) (synCsn (.cv w))) syntaxClass0032)
      syntaxFormula0106 (.classEq (.cv w) (synCphi (.cv v))) p0091 p0092 p0096
  have p0098 :=
    @gN3bitri syntaxFormula0109
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv v))))
          (synCsn (synCsn (synCsn (.cv w))))) syntaxClass0034)
      syntaxFormula0107 (.classEq (.cv w) (synCphi (.cv v))) p0088 p0090 p0097
  have p0099 :=
    @gN3bitri syntaxFormula0110
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))
          (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))) syntaxClass0036)
      syntaxFormula0109 (.classEq (.cv w) (synCphi (.cv v))) p0084 p0087 p0098
  have p0100 :=
    @gAnbi12i syntaxFormula0104 (.classMem (.cv v) (synCop (.cv y) (.cv z)))
      syntaxFormula0110 (.classEq (.cv w) (synCphi (.cv v))) p0083 p0099
  have p0101 :=
    @gN3bitri syntaxFormula0091 syntaxFormula0094
      (synWa syntaxFormula0104 syntaxFormula0110) syntaxFormula0111 p0053 p0054 p0100
  have p0102 := @gExbii syntaxFormula0091 syntaxFormula0111 v p0101
  have p0103 :=
    @gN3bitri syntaxFormula0112 syntaxFormula0090 syntaxFormula0092
      (synWex v syntaxFormula0111) p0041 p0049 p0102
  have p0104 :=
    (Nominal.biimpRefl
      (synWrex v (synCop (.cv y) (.cv z)) (.classEq (.cv w) (synCphi (.cv v)))))
  have p0105 :=
    @gBitr4i syntaxFormula0112 (synWex v syntaxFormula0111)
      (synWrex v (synCop (.cv y) (.cv z)) (.classEq (.cv w) (synCphi (.cv v)))) p0103
      p0104
  have p0106 :=
    @gEleq1d syntaxFormula0083 syntaxClass0085 syntaxClass0093 syntaxClass0052 p0051
  have p0107 :=
    @gCeqsexv syntaxFormula0113 syntaxFormula0114 t
      (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))))
      dv_cache_0020 dv_cache_0028 p0050 p0106
  have p0108 := @gElin syntaxClass0093 syntaxClass0046 syntaxClass0051
  have p0109 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) syntaxClass0045
      p0074 p0026 p0015
  have p0110 := @gElun syntaxClass0095 syntaxClass0042 syntaxClass0044
  have p0111 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (.cv v)))) (synCsn (synCsn (.cv z)))
      (synCopk (.cv y) (.cv x)) syntaxClass0041 p0056 p0011 p0000
  have p0112 :=
    @gOpksnelsik (synCsn (synCsn (.cv v))) (synCsn (.cv z)) syntaxClass0040 p0064
      p0065
  have p0113 := @gOpksnelsik (synCsn (.cv v)) (.cv z) syntaxClass0014 p0058 p0067
  have p0114 := @gSetconslem1 u (.cv v) (.cv z) dv_cache_0022 dv_cache_0024 p0060 p0067
  have p0115 :=
    @gBitri syntaxFormula0115
      (.classMem (synCopk (synCsn (.cv v)) (.cv z)) syntaxClass0014)
      (synWrex u (.cv z) (.classEq (.cv v) (synCphi (.cv u)))) p0113 p0114
  have p0116 :=
    @gN3bitri syntaxFormula0116
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv v)))) (synCsn (synCsn (.cv z))))
        syntaxClass0041)
      syntaxFormula0115 (synWrex u (.cv z) (.classEq (.cv v) (synCphi (.cv u)))) p0111
      p0112 p0115
  have p0117 :=
    @gOtkelins2k (synCsn (synCsn (synCsn (.cv v)))) (synCsn (synCsn (.cv z)))
      (synCopk (.cv y) (.cv x)) syntaxClass0043 p0056 p0011 p0000
  have p0118 :=
    @gOtkelins3k (synCsn (.cv v)) (.cv y) (.cv x) syntaxClass0026 p0058 p0034 p0035
  have p0119 := @gSetconslem2 u (.cv v) (.cv y) dv_cache_0022 dv_cache_0023 p0060 p0034
  have p0120 :=
    @gN3bitri syntaxFormula0117
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv v)))) (synCopk (.cv y) (.cv x)))
        syntaxClass0043)
      (.classMem (synCopk (synCsn (.cv v)) (.cv y)) syntaxClass0026) syntaxFormula0118
      p0117 p0118 p0119
  have p0121 :=
    @gOrbi12i syntaxFormula0116
      (synWrex u (.cv z) (.classEq (.cv v) (synCphi (.cv u)))) syntaxFormula0117
      syntaxFormula0118 p0116 p0120
  have p0122 :=
    @gN3bitri syntaxFormula0119 (.classMem syntaxClass0095 syntaxClass0045)
      (synWo syntaxFormula0116 syntaxFormula0117) syntaxFormula0120 p0109 p0110 p0121
  have p0123 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOp v u (.cv z)
      (.cv y) dv_cache_0026 dv_cache_0024 dv_cache_0025 dv_cache_0023 dv_cache_0027
  have p0124 := @gEleq2i (synCop (.cv z) (.cv y)) syntaxClass0122 (.cv v) p0123
  have p0125 :=
    @gElun (.cv v) (.cab v (synWrex u (.cv z) (.classEq (.cv v) (synCphi (.cv u)))))
      syntaxClass0121
  have p0126 := @gAbid (synWrex u (.cv z) (.classEq (.cv v) (synCphi (.cv u)))) v
  have p0127 := @gAbid syntaxFormula0118 v
  have p0128 :=
    @gOrbi12i
      (.classMem (.cv v) (.cab v (synWrex u (.cv z) (.classEq (.cv v) (synCphi (.cv u))))))
      (synWrex u (.cv z) (.classEq (.cv v) (synCphi (.cv u))))
      (.classMem (.cv v) syntaxClass0121) syntaxFormula0118 p0126 p0127
  have p0129 :=
    @gN3bitri (.classMem (.cv v) (synCop (.cv z) (.cv y)))
      (.classMem (.cv v) syntaxClass0122)
      (synWo (.classMem (.cv v)
          (.cab v (synWrex u (.cv z) (.classEq (.cv v) (synCphi (.cv u))))))
        (.classMem (.cv v) syntaxClass0121))
      syntaxFormula0120 p0124 p0125 p0128
  have p0130 :=
    @gBitr4i syntaxFormula0119 syntaxFormula0120
      (.classMem (.cv v) (synCop (.cv z) (.cv y))) p0122 p0129
  have p0131 :=
    @gOtkelins3k (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))
      (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))
      (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x))) syntaxClass0050
      p0074 p0026 p0015
  have p0132 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (synCsn (.cv v)))))
      (synCsn (synCsn (synCsn (synCsn (.cv w))))) syntaxClass0049 p0085 p0086
  have p0133 :=
    @gOpksnelsik (synCsn (synCsn (synCsn (.cv v))))
      (synCsn (synCsn (synCsn (.cv w)))) syntaxClass0048 p0056 p0031
  have p0134 :=
    @gOpksnelsik (synCsn (synCsn (.cv v))) (synCsn (synCsn (.cv w))) syntaxClass0047
      p0064 p0089
  have p0135 :=
    @gOpksnelsik (synCsn (.cv v)) (synCsn (.cv w)) syntaxClass0023 p0058 p0033
  have p0136 := @gOpksnelsik (.cv v) (.cv w) syntaxClass0022 p0060 p0037
  have p0137 := @gDfop2lem1 v w dv_cache_0029
  have p0138 :=
    @gN3bitri syntaxFormula0123
      (.classMem (synCopk (synCsn (.cv v)) (synCsn (.cv w))) syntaxClass0023)
      (.classMem (synCopk (.cv v) (.cv w)) syntaxClass0022)
      (.classEq (.cv w) (synCun (synCphi (.cv v)) (synCsn (synC0c)))) p0135 p0136
      p0137
  have p0139 :=
    @gN3bitri syntaxFormula0124
      (.classMem (synCopk (synCsn (synCsn (synCsn (.cv v))))
          (synCsn (synCsn (synCsn (.cv w))))) syntaxClass0048)
      syntaxFormula0123
      (.classEq (.cv w) (synCun (synCphi (.cv v)) (synCsn (synC0c)))) p0133 p0134
      p0138
  have p0140 :=
    @gN3bitri syntaxFormula0125
      (.classMem (synCopk (synCsn (synCsn (synCsn (synCsn (synCsn (.cv v))))))
          (synCsn (synCsn (synCsn (synCsn (synCsn (.cv w))))))) syntaxClass0050)
      syntaxFormula0124
      (.classEq (.cv w) (synCun (synCphi (.cv v)) (synCsn (synC0c)))) p0131 p0132
      p0139
  have p0141 :=
    @gAnbi12i syntaxFormula0119 (.classMem (.cv v) (synCop (.cv z) (.cv y)))
      syntaxFormula0125
      (.classEq (.cv w) (synCun (synCphi (.cv v)) (synCsn (synC0c)))) p0130 p0140
  have p0142 :=
    @gN3bitri syntaxFormula0127 syntaxFormula0114
      (synWa syntaxFormula0119 syntaxFormula0125) syntaxFormula0128 p0107 p0108 p0141
  have p0143 := @gExbii syntaxFormula0127 syntaxFormula0128 v p0142
  have p0144 :=
    @gElimak t syntaxClass0052
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      syntaxClass0079 dv_cache_0030 dv_cache_0016 dv_cache_0017 p0040
  have p0145 := (Nominal.biimpRefl syntaxFormula0129)
  have p0146 := @gAnbi1i syntaxFormula0082 syntaxFormula0084 syntaxFormula0113 p0042
  have p0147 := @gN1941v syntaxFormula0083 syntaxFormula0113 v dv_cache_0031
  have p0148 :=
    @gBitr4i syntaxFormula0130 (synWa syntaxFormula0084 syntaxFormula0113)
      syntaxFormula0131 p0146 p0147
  have p0149 := @gExbii syntaxFormula0130 syntaxFormula0131 t p0148
  have p0150 :=
    @gBitri syntaxFormula0129 (synWex t syntaxFormula0130) syntaxFormula0132 p0145 p0149
  have p0151 := @gExcom syntaxFormula0126 t v
  have p0152 :=
    @gN3bitri syntaxFormula0133 syntaxFormula0129 syntaxFormula0132 syntaxFormula0134
      p0144 p0150 p0151
  have p0153 := (Nominal.biimpRefl syntaxFormula0135)
  have p0154 :=
    @gN3bitr4i syntaxFormula0134 (synWex v syntaxFormula0128) syntaxFormula0133
      syntaxFormula0135 p0143 p0152 p0153
  have p0155 :=
    @gOrbi12i syntaxFormula0112
      (synWrex v (synCop (.cv y) (.cv z)) (.classEq (.cv w) (synCphi (.cv v))))
      syntaxFormula0133 syntaxFormula0135 p0105 p0154
  have p0156 := @gElun syntaxClass0079 syntaxClass0039 syntaxClass0053
  have p0157 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfOp w v
      (synCop (.cv y) (.cv z)) (synCop (.cv z) (.cv y)) dv_cache_0032 dv_cache_0033
      dv_cache_0034 dv_cache_0035 dv_cache_0036
  have p0158 :=
    @gEleq2i (synCop (synCop (.cv y) (.cv z)) (synCop (.cv z) (.cv y)))
      syntaxClass0138 (.cv w) p0157
  have p0159 := @gElun (.cv w) syntaxClass0136 syntaxClass0137
  have p0160 :=
    @gAbid (synWrex v (synCop (.cv y) (.cv z)) (.classEq (.cv w) (synCphi (.cv v)))) w
  have p0161 := @gAbid syntaxFormula0135 w
  have p0162 :=
    @gOrbi12i (.classMem (.cv w) syntaxClass0136)
      (synWrex v (synCop (.cv y) (.cv z)) (.classEq (.cv w) (synCphi (.cv v))))
      (.classMem (.cv w) syntaxClass0137) syntaxFormula0135 p0160 p0161
  have p0163 :=
    @gN3bitri syntaxFormula0139 (.classMem (.cv w) syntaxClass0138)
      (synWo (.classMem (.cv w) syntaxClass0136) (.classMem (.cv w) syntaxClass0137))
      syntaxFormula0140 p0158 p0159 p0162
  have p0164 :=
    @gN3bitr4i (synWo syntaxFormula0112 syntaxFormula0133) syntaxFormula0140
      syntaxFormula0141 syntaxFormula0139 p0155 p0156 p0163
  have p0165 :=
    @gBibi12i syntaxFormula0081 (.objMem w x) syntaxFormula0141 syntaxFormula0139 p0039
      p0164
  have p0166 := @gNotbii syntaxFormula0142 (synWb (.objMem w x) syntaxFormula0139) p0165
  have p0167 :=
    @gN3bitri syntaxFormula0076 syntaxFormula0080 (.neg syntaxFormula0142)
      (.neg (synWb (.objMem w x) syntaxFormula0139)) p0029 p0030 p0166
  have p0168 :=
    @gExbii syntaxFormula0076 (.neg (synWb (.objMem w x) syntaxFormula0139)) w p0167
  have p0169 := @gExnal (synWb (.objMem w x) syntaxFormula0139) w
  have p0170 :=
    @gN3bitri syntaxFormula0078 syntaxFormula0077
      (synWex w (.neg (synWb (.objMem w x) syntaxFormula0139)))
      (.neg (.all w (synWb (.objMem w x) syntaxFormula0139))) p0025 p0168 p0169
  have p0171 :=
    @gCon2bii syntaxFormula0078 (.all w (synWb (.objMem w x) syntaxFormula0139)) p0170
  have p0172 :=
    @gDfcleq w (.cv x) (synCop (synCop (.cv y) (.cv z)) (synCop (.cv z) (.cv y)))
      dv_cache_0037 dv_cache_0038
  have p0173 :=
    @gElcompl (synCopk (synCsn (synCsn (.cv z))) (synCopk (.cv y) (.cv x)))
      syntaxClass0056 p0015
  have p0174_e01_recanon :
    Nominal.NPrf
      (synWb syntaxFormula0143 (.all w (synWb (.objMem w x) syntaxFormula0139))) :=
    Nominal.RecanonTransportDev.transport
      (by
        simp only [synWb, synCop, synCun, synCnin, synWnan, synWa, synCcompl,
          synWrex, synWex, synCphi]
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
    @gN3bitr4ri (.all w (synWb (.objMem w x) syntaxFormula0139))
      (.neg syntaxFormula0078) syntaxFormula0143 syntaxFormula0068 p0171 p0174_e01_recanon
      p0173
  have p0175 := @gBitri syntaxFormula0064 syntaxFormula0068 syntaxFormula0143 p0014 p0174
  have p0176 := @gExbii syntaxFormula0064 syntaxFormula0143 z p0175
  have p0177 :=
    @gBitr2i syntaxFormula0067 syntaxFormula0065 (synWex z syntaxFormula0143) p0010
      p0176
  have p0178 := @gExbii (synWex z syntaxFormula0143) syntaxFormula0067 y p0177
  have p0179 := @gElswap y z (.cv x) dv_cache_0039 dv_cache_0040 dv_cache_0041
  have p0180 := @gElimakv y syntaxClass0066 (.cv x) dv_cache_0042 dv_cache_0039 p0035
  have p0181 :=
    @gN3bitr4i (synWex y (synWex z syntaxFormula0143)) (synWex y syntaxFormula0067)
      (.classMem (.cv x) (synCswap)) (.classMem (.cv x) syntaxClass0144) p0178 p0179
      p0180
  have p0182 := @gEqriv x (synCswap) syntaxClass0144 dv_cache_0043 dv_cache_0044 p0181
  exact p0182


end NFChoice.DirectNominalPrf.WPPReplay
