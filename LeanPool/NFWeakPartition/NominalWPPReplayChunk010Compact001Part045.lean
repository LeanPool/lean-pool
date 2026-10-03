/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk010Compact001Part044

/-! NF weak partition development: NominalWPPReplayChunk010Compact001Part045. -/


public section


namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

@[expose]
noncomputable def g_setconslem5 :
    Nominal.NPrf
      (.classMem (syn_ccompl (syn_cimak
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
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))))) (syn_cvv)) :=
  by
  have p0000 := @g_ssetkex
  have p0001 := @g_sikex (syn_cssetk) p0000
  have p0002 := @g_sikex (syn_csik (syn_cssetk)) p0001
  have p0003 := @g_ins3kex (syn_csik (syn_csik (syn_cssetk))) p0002
  have p0005 := @g_addcexlem
  have p0006 := @g_n_1cex
  have p0007 := @g_pw1ex (syn_c1c) p0006
  have p0008 := @g_pw1ex (syn_cpw1 (syn_c1c)) p0007
  have p0009 :=
    @g_imakex
      (syn_cdif (syn_cins3k (syn_ccompl
            (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
              (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
          (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
            (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
              (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
          (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0005 p0008
  have p0010 :=
    @g_imagekex
      (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
              (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
            (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
              (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
            (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
        (syn_cpw1 (syn_cpw1 (syn_c1c))))
      p0009
  have p0011 := @g_nncex
  have p0012 := @g_vvex
  have p0013 := @g_xpkex (syn_cnnc) (syn_cvv) p0011 p0012
  have p0014 :=
    @g_inex
      (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                  (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
              (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                  (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
              (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
          (syn_cpw1 (syn_cpw1 (syn_c1c)))))
      (syn_cxpk (syn_cnnc) (syn_cvv)) p0010 p0013
  have p0015 := @g_idkex
  have p0017 := @g_complex (syn_cnnc) p0011
  have p0019 := @g_xpkex (syn_ccompl (syn_cnnc)) (syn_cvv) p0017 p0012
  have p0020 :=
    @g_inex (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv)) p0015 p0019
  have p0021 :=
    @g_unex
      (syn_cin (syn_cimagek (syn_cimak (syn_cdif (syn_cins3k (syn_ccompl
                  (syn_cimak (syn_cin (syn_cins3k (syn_cssetk)) (syn_cins2k (syn_cssetk)))
                    (syn_cpw1 (syn_cpw1 (syn_c1c)))))) (syn_cimak
                (syn_csymdif (syn_cins2k (syn_cins2k (syn_cssetk)))
                  (syn_cun (syn_cins2k (syn_cins3k (syn_cssetk)))
                    (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))))
                (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))))))
            (syn_cpw1 (syn_cpw1 (syn_c1c))))) (syn_cxpk (syn_cnnc) (syn_cvv)))
      (syn_cin (syn_cidk) (syn_cxpk (syn_ccompl (syn_cnnc)) (syn_cvv))) p0014 p0020
  have p0022 :=
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
      p0021
  have p0023 :=
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
      p0022
  have p0024 :=
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
      p0023
  have p0025 :=
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
      p0000 p0024
  have p0026 :=
    @g_ins3kex
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
      p0025
  have p0028 := @g_ins2kex (syn_cssetk) p0000
  have p0030 :=
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
      (syn_cssetk) p0023 p0000
  have p0031 := @g_snex (syn_csn (syn_c0c))
  have p0033 := @g_xpkex (syn_csn (syn_csn (syn_c0c))) (syn_cvv) p0031 p0012
  have p0034 :=
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
      (syn_cxpk (syn_csn (syn_csn (syn_c0c))) (syn_cvv)) p0030 p0033
  have p0035 :=
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
      p0034
  have p0036 :=
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
      p0028 p0035
  have p0037 :=
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
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0036 p0008
  have p0038 :=
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
      p0037
  have p0039 :=
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
      p0038
  have p0040 :=
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
      p0039
  have p0041 :=
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
      p0028 p0040
  have p0042 :=
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
      (syn_cpw1 (syn_cpw1 (syn_c1c))) p0041 p0008
  have p0043 :=
    @g_ins2kex
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
      p0042
  have p0044 :=
    @g_unex
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
      p0026 p0043
  have p0045 :=
    @g_ins2kex
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
      p0044
  have p0046 :=
    @g_symdifex (syn_cins3k (syn_csik (syn_csik (syn_cssetk))))
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
      p0003 p0045
  have p0047 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_c1c))) p0008
  have p0048 := @g_pw1ex (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c)))) p0047
  have p0049 :=
    @g_imakex
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
      (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_cpw1 (syn_c1c))))) p0046 p0048
  have p0050 :=
    @g_complex
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
      p0049
  exact p0050


end NFChoice.DirectNominalPrf.WPPReplay
