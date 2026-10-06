/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.NominalWPPReplayChunk010Compact001Part050

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part051`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_swapex`. -/
@[expose]
noncomputable def gSwapex : Nominal.NPrf (.classMem (synCswap) (synCvv)) :=
  by
  have p0000 := @gDfswap2
  have p0001 := @gSsetkex
  have p0002 := @gIns2kex (synCssetk) p0001
  have p0003 := @gIns2kex (synCins2k (synCssetk)) p0002
  have p0005 := @gAddcexlem
  have p0006 := @gN1cex
  have p0007 := @gPw1ex (synC1c) p0006
  have p0008 := @gPw1ex (synCpw1 (synC1c)) p0007
  have p0009 :=
    @gImakex
      (synCdif (synCins3k (synCcompl
            (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
          (synCsymdif (synCins2k (synCins2k (synCssetk)))
            (synCun (synCins2k (synCins3k (synCssetk)))
              (synCins3k (synCsik (synCsik (synCssetk))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synCpw1 (synC1c))) p0005 p0008
  have p0010 :=
    @gImagekex
      (synCimak (synCdif (synCins3k (synCcompl
              (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
            (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCins2k (synCins3k (synCssetk)))
                (synCins3k (synCsik (synCsik (synCssetk))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
        (synCpw1 (synCpw1 (synC1c))))
      p0009
  have p0011 := @gNncex
  have p0012 := @gVvex
  have p0013 := @gXpkex (synCnnc) (synCvv) p0011 p0012
  have p0014 :=
    @gInex
      (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                (synCun (synCins2k (synCins3k (synCssetk)))
                  (synCins3k (synCsik (synCsik (synCssetk))))))
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
          (synCpw1 (synCpw1 (synC1c)))))
      (synCxpk (synCnnc) (synCvv)) p0010 p0013
  have p0015 := @gIdkex
  have p0017 := @gComplex (synCnnc) p0011
  have p0019 := @gXpkex (synCcompl (synCnnc)) (synCvv) p0017 p0012
  have p0020 :=
    @gInex (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)) p0015 p0019
  have p0021 :=
    @gUnex
      (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                  (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                  (synCun (synCins2k (synCins3k (synCssetk)))
                    (synCins3k (synCsik (synCsik (synCssetk))))))
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))) p0014 p0020
  have p0022 :=
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
      p0021
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
      p0022
  have p0024 :=
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
      p0023
  have p0025 :=
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
      p0001 p0024
  have p0026 :=
    @gIns3kex
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
      p0025
  have p0027 :=
    @gIns2kex
      (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      p0026
  have p0029 :=
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
      (synCssetk) p0023 p0001
  have p0030 := @gSnex (synCsn (synC0c))
  have p0032 := @gXpkex (synCsn (synCsn (synC0c))) (synCvv) p0030 p0012
  have p0033 :=
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
      (synCxpk (synCsn (synCsn (synC0c))) (synCvv)) p0029 p0032
  have p0034 :=
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
      p0033
  have p0035 :=
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
      p0002 p0034
  have p0036 :=
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
      (synCpw1 (synCpw1 (synC1c))) p0035 p0008
  have p0037 :=
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
      p0036
  have p0038 :=
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
      p0037
  have p0039 :=
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
      p0038
  have p0040 :=
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
      p0002 p0039
  have p0041 :=
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
      (synCpw1 (synCpw1 (synC1c))) p0040 p0008
  have p0042 :=
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
      p0041
  have p0043 :=
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
      p0042
  have p0044 :=
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
      p0043
  have p0045 :=
    @gUnex
      (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
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
      p0027 p0044
  have p0046 :=
    @gIns2kex
      (synCun (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
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
      p0045
  have p0047 :=
    @gSikex
      (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                      (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                      (synCun (synCins2k (synCins3k (synCssetk)))
                        (synCins3k (synCsik (synCsik (synCssetk))))))
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
          (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))
      p0022
  have p0048 :=
    @gSikex
      (synCsik (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                      (synCcompl (synCimak
                          (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                          (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                        (synCun (synCins2k (synCins3k (synCssetk)))
                          (synCins3k (synCsik (synCsik (synCssetk))))))
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                  (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
            (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))
      p0047
  have p0049 :=
    @gSikex
      (synCsik (synCsik (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                      (synCins3k (synCcompl (synCimak
                            (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                            (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                        (synCsymdif (synCins2k (synCins2k (synCssetk)))
                          (synCun (synCins2k (synCins3k (synCssetk)))
                            (synCins3k (synCsik (synCsik (synCssetk))))))
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                    (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
              (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))
      p0048
  have p0050 :=
    @gSikex
      (synCsik (synCsik (synCsik (synCimagek (synCun (synCin (synCimagek (synCimak
                      (synCdif (synCins3k (synCcompl (synCimak
                              (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                              (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                          (synCsymdif (synCins2k (synCins2k (synCssetk)))
                            (synCun (synCins2k (synCins3k (synCssetk)))
                              (synCins3k (synCsik (synCsik (synCssetk))))))
                          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                      (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))
      p0049
  have p0051 :=
    @gSikex
      (synCsik (synCsik (synCsik (synCsik (synCimagek (synCun (synCin (synCimagek
                      (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      p0050
  have p0052 :=
    @gIns3kex
      (synCsik (synCsik (synCsik (synCsik (synCsik (synCimagek (synCun (synCin
                      (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                  (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                  (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                              (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                (synCun (synCins2k (synCins3k (synCssetk)))
                                  (synCins3k (synCsik (synCsik (synCssetk))))))
                              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                          (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                    (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))
      p0051
  have p0053 :=
    @gInex
      (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
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
      (synCins3k (synCsik (synCsik (synCsik (synCsik (synCsik (synCimagek (synCun
                      (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                  (synCimak (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
      p0046 p0052
  have p0054 := @gPw1ex (synCpw1 (synCpw1 (synC1c))) p0008
  have p0055 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synC1c)))) p0054
  have p0056 := @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0055
  have p0057 :=
    @gPw1ex (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))) p0056
  have p0058 :=
    @gImakex
      (synCin (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik
                    (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                  (synCins3k (synCcompl (synCimak
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
                    (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k (synCsik (synCsik
              (synCsik (synCsik (synCsik (synCimagek (synCun (synCin (synCimagek
                            (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                      (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk)
                          (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) p0053
      p0057
  have p0059 :=
    @gSikex
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
      p0025
  have p0060 :=
    @gSikex
      (synCsik (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                    (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
                                (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
                                (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                            (synCsymdif (synCins2k (synCins2k (synCssetk)))
                              (synCun (synCins2k (synCins3k (synCssetk)))
                                (synCins3k (synCsik (synCsik (synCssetk))))))
                            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                        (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                  (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))
      p0059
  have p0061 :=
    @gIns3kex
      (synCsik (synCsik (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
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
      p0060
  have p0062 :=
    @gIns3kex
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
      p0041
  have p0063 :=
    @gIns2kex
      (synCins3k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
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
                            (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c)))))
      p0062
  have p0064 :=
    @gUnex
      (synCins3k (synCsik (synCsik (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek
                    (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl
                                  (synCimak (synCin (synCins3k (synCssetk))
                                      (synCins2k (synCssetk)))
                                    (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                  (synCun (synCins2k (synCins3k (synCssetk)))
                                    (synCins3k (synCsik (synCsik (synCssetk))))))
                                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                            (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                      (synCin (synCidk) (synCxpk (synCcompl (synCnnc)) (synCvv)))))))))))
      (synCins2k (synCins3k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k
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
                      (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 (synC1c))))))
      p0061 p0063
  have p0065 :=
    @gIns2kex
      (synCun (synCins3k (synCsik (synCsik (synCcomk (synCssetk) (synCsik (synCcnvk
                    (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif (synCins3k
                                  (synCcompl (synCimak (synCin (synCins3k (synCssetk))
                                        (synCins2k (synCssetk)))
                                      (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                  (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                    (synCun (synCins2k (synCins3k (synCssetk)))
                                      (synCins3k (synCsik (synCsik (synCssetk))))))
                                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                              (synCpw1 (synCpw1 (synC1c))))) (synCxpk (synCnnc) (synCvv)))
                        (synCin (synCidk)
                          (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))) (synCins2k
          (synCins3k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
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
      p0064
  have p0066 :=
    @gSikex
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
      p0038
  have p0067 :=
    @gSikex
      (synCsik (synCsik (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
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
      p0066
  have p0068 :=
    @gSikex
      (synCsik (synCsik (synCsik (synCcompl (synCimak
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
      p0067
  have p0069 :=
    @gSikex
      (synCsik (synCsik (synCsik (synCsik (synCcompl (synCimak
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
                  (synCpw1 (synCpw1 (synC1c)))))))))
      p0068
  have p0070 :=
    @gIns3kex
      (synCsik (synCsik (synCsik (synCsik (synCsik (synCcompl (synCimak
                    (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk
                            (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                        (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                    (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                    (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                            (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                    (synCpw1 (synCpw1 (synC1c))))))))))
      p0069
  have p0071 :=
    @gInex
      (synCins2k (synCun (synCins3k (synCsik (synCsik (synCcomk (synCssetk) (synCsik
                    (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak (synCdif
                                  (synCins3k (synCcompl (synCimak
                                        (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                    (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                      (synCun (synCins2k (synCins3k (synCssetk)))
                                        (synCins3k (synCsik (synCsik (synCssetk))))))
                                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                (synCpw1 (synCpw1 (synC1c)))))
                            (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                            (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))) (synCins2k
            (synCins3k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                      (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk)) (synCins3k
                              (synCun (synCcomk (synCcnvk (synCimagek (synCun (synCin
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
      (synCins3k (synCsik (synCsik (synCsik (synCsik (synCsik (synCcompl (synCimak
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
                      (synCpw1 (synCpw1 (synC1c)))))))))))
      p0065 p0070
  have p0072 :=
    @gImakex
      (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik (synCcomk (synCssetk)
                    (synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                  (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak
                                      (synCsymdif (synCins2k (synCins2k (synCssetk)))
                                        (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
                                        (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
                                  (synCpw1 (synCpw1 (synC1c)))))
                              (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                              (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))) (synCins2k
              (synCins3k (synCimak (synCin (synCins2k (synCssetk)) (synCins3k (synCsik
                        (synCcompl (synCimak (synCsymdif (synCins2k (synCssetk))
                              (synCins3k (synCun (synCcomk (synCcnvk (synCimagek (synCun
        (synCin (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                            (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 (synC1c)))))))) (synCins3k (synCsik (synCsik (synCsik
                (synCsik (synCsik (synCcompl (synCimak
                        (synCsymdif (synCins2k (synCssetk)) (synCins3k (synCun (synCcomk
                                (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1
        (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
                                        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk)
                                        (synCxpk (synCcompl (synCnnc)) (synCvv))))))
                                (synCssetk))
                              (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                        (synCpw1 (synCpw1 (synC1c))))))))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) p0071
      p0057
  have p0073 :=
    @gUnex
      (synCimak (synCin (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk)
                    (synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
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
                            (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                    (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun (synCin
                                (synCimagek (synCimak (synCdif (synCins3k (synCcompl
        (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
                          (synCpw1 (synCpw1 (synC1c))))))))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
      p0058 p0072
  have p0074 :=
    @gSymdifex (synCins2k (synCins2k (synCssetk)))
      (synCun (synCimak (synCin (synCins2k (synCun (synCins2k (synCins3k
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
                              (synCxpk (synCcompl (synCnnc)) (synCvv))))))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
        (synCimak (synCin (synCins2k (synCun (synCins3k (synCsik (synCsik
                      (synCcomk (synCssetk) (synCsik (synCcnvk (synCimagek (synCun
                                (synCin (synCimagek (synCimak (synCdif (synCins3k
        (synCcompl (synCimak (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
                            (synCpw1 (synCpw1 (synC1c))))))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
      p0003 p0073
  have p0075 :=
    @gImakex
      (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCimak (synCin
              (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk) (synCsik
                          (synCcnvk (synCimagek (synCun (synCin (synCimagek (synCimak
                                      (synCdif (synCins3k (synCcompl (synCimak
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
                          (synCpw1 (synCpw1 (synC1c))))))))) (synCins3k (synCsik (synCsik
                    (synCsik (synCsik (synCsik (synCimagek (synCun (synCin (synCimagek
                                  (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
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
        (synCimagek (synCimak (synCdif (synCins3k (synCcompl (synCimak (synCin
        (synCins3k (synCssetk)) (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c))))))
        (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k
        (synCins3k (synCssetk))) (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1
        (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
        (synCxpk (synCnnc) (synCvv))) (synCin (synCidk) (synCxpk (synCcompl (synCnnc))
        (synCvv)))))) (synCssetk)) (synCxpk (synCsn (synCsn (synC0c))) (synCvv)))))
                              (synCpw1 (synCpw1 (synC1c))))))))))))
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))) p0074 p0055
  have p0076 :=
    @gComplex
      (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun (synCimak
              (synCin (synCins2k (synCun (synCins2k (synCins3k (synCcomk (synCssetk)
                          (synCsik (synCcnvk (synCimagek (synCun (synCin (synCimagek
                                      (synCimak (synCdif (synCins3k (synCcompl (synCimak
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
                                (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))
      p0075
  have p0077 :=
    @gImakex
      (synCcompl (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk))) (synCun
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
                                  (synCpw1 (synCpw1 (synC1c)))))))))))) (synCpw1
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))))
          (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))
      (synCpw1 (synC1c)) p0076 p0007
  have p0079 :=
    @gImakex
      (synCimak (synCcompl (synCimak (synCsymdif (synCins2k (synCins2k (synCssetk)))
              (synCun (synCimak (synCin (synCins2k (synCun (synCins2k (synCins3k
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
            (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))
      (synCvv) p0077 p0012
  have p0080 :=
    @gEqeltri (synCswap)
      (synCimak (synCimak (synCcompl (synCimak
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))) (synCpw1 (synC1c)))
        (synCvv))
      (synCvv) p0000 p0079
  exact p0080


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part052`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfsset2`. -/
@[expose]
noncomputable def gDfsset2 :
    Nominal.NPrf
      (.classEq (synCsset) (synCuni1 (synCuni1 (synCimak
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
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))))
              (synCssetk))))) :=
  by
  let proofSupport : Finset Var := (∅ : Finset Var)
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have dv_cache_0001 : x ∉ ((synCssetk)).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0002 : y ∉ ((synCssetk)).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          compact_fv_not_mem_empty, not_false_eq_true])
  have dv_cache_0003 : x ≠ y :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact (show x ≠ y from (by exact fresh_x_ne_y))
  have p0000 := @gVex x
  have p0001 := @gVex y
  have p0002 := @gOpkelssetkg (.cv x) (.cv y) (synCvv) (synCvv)
  have p0003 :=
    @gMp2an (.classMem (.cv x) (synCvv)) (.classMem (.cv y) (synCvv))
      (synWb (.classMem (synCopk (.cv x) (.cv y)) (synCssetk)) (synWss (.cv x) (.cv y)))
      p0000 p0001 p0002
  have p0004 :=
    @gOpabbii (.classMem (synCopk (.cv x) (.cv y)) (synCssetk))
      (synWss (.cv x) (.cv y)) x y p0003
  have p0005 := @gSetconslem4 x y (synCssetk) dv_cache_0001 dv_cache_0002 dv_cache_0003
  have p0006 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfSset x y
      dv_cache_0003
  have p0007 :=
    @gN3eqtr4ri (synCopab x y (.classMem (synCopk (.cv x) (.cv y)) (synCssetk)))
      (synCopab x y (synWss (.cv x) (.cv y)))
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
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCssetk))))
      (synCsset) p0004 p0005 p0006
  exact p0007

/-- Checked nominal proof certificate identified upstream as `g_ssetex`. -/
@[expose]
noncomputable def gSsetex : Nominal.NPrf (.classMem (synCsset) (synCvv)) :=
  by
  have p0000 := @gDfsset2
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
  have p0010 :=
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
      (synCssetk) p0008 p0009
  have p0011 :=
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
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCssetk))
      p0010
  have p0012 :=
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
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCssetk)))
      p0011
  have p0013 :=
    @gEqeltri (synCsset)
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
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCssetk))))
      (synCvv) p0000 p0012
  exact p0013


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part053`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_dfima2`. -/
@[expose]
noncomputable def gDfima2 (A : Class) (B : Class) :
    Nominal.NPrf
      (.classEq (synCima A B) (synCimak (synCimak
            (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
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
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 A))) B)) :=
  by
  let proofSupport : Finset Var := A.fv ∪ B.fv
  let x : Var := freshVar proofSupport 0
  let y : Var := freshVar proofSupport 1
  let w : Var := freshVar proofSupport 2
  let t : Var := freshVar proofSupport 3
  let z : Var := freshVar proofSupport 4
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
  have fresh_w : w ∉ proofSupport :=
    by
    change freshVar proofSupport 2 ∉ proofSupport
    exact freshVar_not_mem proofSupport 2
  have fresh_w_not_A : w ∉ A.fv := by
    intro h
    exact fresh_w (Finset.mem_union_left _ (h))
  have fresh_t : t ∉ proofSupport :=
    by
    change freshVar proofSupport 3 ∉ proofSupport
    exact freshVar_not_mem proofSupport 3
  have fresh_t_not_A : t ∉ A.fv := by
    intro h
    exact fresh_t (Finset.mem_union_left _ (h))
  have fresh_z : z ∉ proofSupport :=
    by
    change freshVar proofSupport 4 ∉ proofSupport
    exact freshVar_not_mem proofSupport 4
  have fresh_z_not_A : z ∉ A.fv := by
    intro h
    exact fresh_z (Finset.mem_union_left _ (h))
  have fresh_x_ne_y : x ≠ y :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 1
    exact freshVar_injective proofSupport (i := 0) (j := 1) (by decide)
  have fresh_y_ne_x : y ≠ x := Ne.symm fresh_x_ne_y
  have fresh_x_ne_w : x ≠ w :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 0) (j := 2) (by decide)
  have fresh_w_ne_x : w ≠ x := Ne.symm fresh_x_ne_w
  have fresh_x_ne_t : x ≠ t :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 0) (j := 3) (by decide)
  have fresh_t_ne_x : t ≠ x := Ne.symm fresh_x_ne_t
  have fresh_x_ne_z : x ≠ z :=
    by
    change freshVar proofSupport 0 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 0) (j := 4) (by decide)
  have fresh_z_ne_x : z ≠ x := Ne.symm fresh_x_ne_z
  have fresh_y_ne_w : y ≠ w :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 2
    exact freshVar_injective proofSupport (i := 1) (j := 2) (by decide)
  have fresh_w_ne_y : w ≠ y := Ne.symm fresh_y_ne_w
  have fresh_y_ne_t : y ≠ t :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 1) (j := 3) (by decide)
  have fresh_t_ne_y : t ≠ y := Ne.symm fresh_y_ne_t
  have fresh_y_ne_z : y ≠ z :=
    by
    change freshVar proofSupport 1 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 1) (j := 4) (by decide)
  have fresh_z_ne_y : z ≠ y := Ne.symm fresh_y_ne_z
  have fresh_w_ne_t : w ≠ t :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 3
    exact freshVar_injective proofSupport (i := 2) (j := 3) (by decide)
  have fresh_w_ne_z : w ≠ z :=
    by
    change freshVar proofSupport 2 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 2) (j := 4) (by decide)
  have fresh_z_ne_w : z ≠ w := Ne.symm fresh_w_ne_z
  have fresh_t_ne_z : t ≠ z :=
    by
    change freshVar proofSupport 3 ≠ freshVar proofSupport 4
    exact freshVar_injective proofSupport (i := 3) (j := 4) (by decide)
  have fresh_z_ne_t : z ≠ t := Ne.symm fresh_t_ne_z
  have dv_cache_0001 : y ∉ (A).fv := by
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_A, not_false_eq_true])
  have dv_cache_0002 : x ∉ (A).fv :=
    by
    clear dv_cache_0001
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_A, not_false_eq_true])
  have dv_cache_0003 : y ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_y_not_B, not_false_eq_true])
  have dv_cache_0004 : x ∉ (B).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_x_not_B, not_false_eq_true])
  have dv_cache_0005 : y ≠ x :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004
    exact (show y ≠ x from (by exact fresh_y_ne_x))
  have dv_cache_0006 :
    x ∉
      ((synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
              (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
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
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 A)))).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_x_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0007 : x ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006
    exact
      (by
        have compact_fv_not_mem_empty : x ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_x_ne_y, not_false_eq_true])
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
  have dv_cache_0009 : t ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008
    exact
      (by
        have compact_fv_not_mem_empty : t ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_t_not_A, not_false_eq_true])
  have dv_cache_0010 : z ∉ (A).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [fresh_z_not_A, not_false_eq_true])
  have dv_cache_0011 : w ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010
    exact (show w ≠ t from (by exact fresh_w_ne_t))
  have dv_cache_0012 : w ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
    exact (show w ≠ z from (by exact fresh_w_ne_z))
  have dv_cache_0013 : t ≠ z :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012
    exact (show t ≠ z from (by exact fresh_t_ne_z))
  have dv_cache_0014 :
    w ∉
      ((synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
              (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
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
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 A)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_w_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0015 :
    t ∉
      ((synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
              (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
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
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 A)))).fv :=
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
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_t_not_A, compact_fv_not_mem_empty, or_false, not_false_eq_true])
  have dv_cache_0016 : z ∉ ((Class.cv x)).fv :=
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
          fresh_z_ne_x, not_false_eq_true])
  have dv_cache_0017 : w ∉ ((Class.cv x)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_x, not_false_eq_true])
  have dv_cache_0018 : t ∉ ((Class.cv x)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_x, not_false_eq_true])
  have dv_cache_0019 : z ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_z_ne_y, not_false_eq_true])
  have dv_cache_0020 : w ∉ ((Class.cv y)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_w_ne_y, not_false_eq_true])
  have dv_cache_0021 : t ∉ ((Class.cv y)).fv :=
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
        simp only [NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_singleton,
          fresh_t_ne_y, not_false_eq_true])
  have dv_cache_0022 : t ∉ ((Wff.classMem (synCop (.cv x) (.cv y)) A)).fv :=
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
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_t_ne_x, fresh_t_ne_y, fresh_t_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0023 : z ∉ ((Wff.classMem (synCop (.cv w) (.cv t)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022
    exact
      (by
        have compact_fv_not_mem_empty : z ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_z_ne_w, fresh_z_ne_t, fresh_z_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0024 : w ∉ ((Wff.classMem (synCop (.cv x) (.cv t)) A)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
    exact
      (by
        have compact_fv_not_mem_empty : w ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CoreFVSimp.fv_wff_classMem,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cop,
          NFChoice.Compiler.CoreFVSimp.fv_class_cv, Finset.mem_union,
          Finset.mem_singleton, fresh_w_ne_x, fresh_w_ne_t, fresh_w_not_A, or_false,
          not_false_eq_true])
  have dv_cache_0025 : z ≠ w :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024
    exact (show z ≠ w from (by exact fresh_z_ne_w))
  have dv_cache_0026 : z ≠ t :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025
    exact (show z ≠ t from (by exact fresh_z_ne_t))
  have dv_cache_0027 :
    y ∉
      ((synCimak (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
              (synCcompl (synCimak
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
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 A))) B)).fv :=
    by
    clear dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
      dv_cache_0006 dv_cache_0007 dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013 dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026
    exact
      (by
        have compact_fv_not_mem_empty : y ∉ (∅ : Finset Var) :=
          by
          intro hmem
          cases hmem
        simp only [NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimak,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cin,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cxpk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cvv,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccompl,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csymdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins3k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csik,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cssetk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cins2k,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cun,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccomk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_ccnvk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cimagek,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cdif,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cpw1,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c1c,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cnnc,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_cidk,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_csn,
          NFChoice.Compiler.CompactSyntaxFVExplicit.fv_syn_c0c, Finset.mem_union,
          fresh_y_not_A, fresh_y_not_B, compact_fv_not_mem_empty, or_false,
          not_false_eq_true])
  have p0000 :=
    NFChoice.DirectNominalPrf.NominalAlphaWrappersRepaired.nominalDfIma y x A B
      dv_cache_0001 dv_cache_0002 dv_cache_0003 dv_cache_0004 dv_cache_0005
  have p0001 := @gVex y
  have p0002 :=
    @gElimak x
      (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 A)))
      B (.cv y) dv_cache_0006 dv_cache_0004 dv_cache_0007 p0001
  have p0003 :=
    @gSetconslem6 w t z A dv_cache_0008 dv_cache_0009 dv_cache_0010 dv_cache_0011
      dv_cache_0012 dv_cache_0013
  have p0004 := @gOpeq1 (.cv w) (.cv x) (.cv t)
  have p0005_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq w x) (.classEq (synCop (.cv w) (.cv t)) (synCop (.cv x) (.cv t)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0004
  have p0005 :=
    @gEleq1d (.objEq w x) (synCop (.cv w) (.cv t)) (synCop (.cv x) (.cv t)) A
      p0005_e00_recanon
  have p0006 := @gOpeq2 (.cv t) (.cv y) (.cv x)
  have p0007_e00_recanon :
    Nominal.NPrf
      (.imp (.objEq t y) (.classEq (synCop (.cv x) (.cv t)) (synCop (.cv x) (.cv y)))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.classEq_objEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0006
  have p0007 :=
    @gEleq1d (.objEq t y) (synCop (.cv x) (.cv t)) (synCop (.cv x) (.cv y)) A
      p0007_e00_recanon
  have p0008 := @gVex x
  have p0009_e01_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv w) (.cv x)) (synWb (.classMem (synCop (.cv w) (.cv t)) A)
          (.classMem (synCop (.cv x) (.cv t)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0005
  have p0009_e02_recanon :
    Nominal.NPrf
      (.imp (.classEq (.cv t) (.cv y)) (synWb (.classMem (synCop (.cv x) (.cv t)) A)
          (.classMem (synCop (.cv x) (.cv y)) A))) :=
    Nominal.RecanonTransportDev.transport
      (by
        unfold synWb synCop synCun synCnin synWnan synWa synCcompl synWrex synWex
          synCphi
        simp (config :=
          { failIfUnchanged := false }) only [NFChoice.Compiler.CoreFVSimp.fv_class_cv]
        apply Nominal.RecanonTransportDev.TRecanonWff.imp
        · exact Nominal.RecanonTransportDev.TRecanonWff.objEq_classEq _ _
        · exact Nominal.RecanonTransportDev.TRecanonWff.same _)
      p0007
  have p0009 :=
    @gOpkelopkab (.classMem (synCop (.cv w) (.cv t)) A)
      (.classMem (synCop (.cv x) (.cv t)) A) (.classMem (synCop (.cv x) (.cv y)) A) z w
      t
      (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 A)))
      (.cv x) (.cv y) dv_cache_0014 dv_cache_0015 dv_cache_0016 dv_cache_0017
      dv_cache_0018 dv_cache_0019 dv_cache_0020 dv_cache_0021 dv_cache_0022 dv_cache_0023
      dv_cache_0024 dv_cache_0025 dv_cache_0026 dv_cache_0011 p0003 p0009_e01_recanon
      p0009_e02_recanon p0008 p0001
  have p0010 := (Nominal.biimpRefl (synWbr (.cv x) A (.cv y)))
  have p0011 :=
    @gBitr4i
      (.classMem (synCopk (.cv x) (.cv y)) (synCimak
          (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
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
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 A))))
      (.classMem (synCop (.cv x) (.cv y)) A) (synWbr (.cv x) A (.cv y)) p0009 p0010
  have p0012 :=
    @gRexbii
      (.classMem (synCopk (.cv x) (.cv y)) (synCimak
          (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
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
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 A))))
      (synWbr (.cv x) A (.cv y)) x B p0011
  have p0013 :=
    @gBitri
      (.classMem (.cv y) (synCimak (synCimak
            (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
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
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 A))) B))
      (synWrex x B (.classMem (synCopk (.cv x) (.cv y)) (synCimak
            (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
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
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
            (synCpw1 (synCpw1 A)))))
      (synWrex x B (synWbr (.cv x) A (.cv y))) p0002 p0012
  have p0014 :=
    @gEqabi (synWrex x B (synWbr (.cv x) A (.cv y))) y
      (synCimak (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
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
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 A))) B)
      dv_cache_0027 p0013
  have p0015 :=
    @gEqtr4i (synCima A B) (.cab y (synWrex x B (synWbr (.cv x) A (.cv y))))
      (synCimak (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
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
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
          (synCpw1 (synCpw1 A))) B)
      p0000 p0014
  exact p0015


end NFChoice.DirectNominalPrf.WPPReplay

end
