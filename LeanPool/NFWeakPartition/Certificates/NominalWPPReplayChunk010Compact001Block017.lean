/-
Copyright (c) 2026 Elliot Glazer and NFNotWPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Elliot Glazer and NFNotWPP contributors
-/

module

public import LeanPool.NFWeakPartition.Certificates.NominalWPPReplayChunk010Compact001Block016

/-! Nominal proof certificates grouped in dependency order. -/


public section

/-! Certificates from `NominalWPPReplayChunk010Compact001Part056`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_coexg`. -/
@[expose]
noncomputable def gCoexg (A : Class) (B : Class) (V : Class) (W : Class) :
    Nominal.NPrf
      (.imp (synWa (.classMem A V) (.classMem B W)) (.classMem (synCcom A B) (synCvv))) :=
  by
  have p0000 := @gDfco1 A B
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
  have p0010 := @gXpkex (synCvv) (synCxpk (synCvv) (synCvv)) p0001 p0003
  have p0012 :=
    @gInex (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
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
      p0010 p0006
  have p0013 := @gPw1exg A V
  have p0014 := @gPw1exg (synCpw1 A) (synCvv)
  have p0015 :=
    @gSyl (.classMem A V) (.classMem (synCpw1 A) (synCvv))
      (.classMem (synCpw1 (synCpw1 A)) (synCvv)) p0013 p0014
  have p0016 :=
    @gImakexg
      (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
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
      (synCpw1 (synCpw1 A)) (synCvv) (synCvv)
  have p0017 :=
    @gSylancr (.classMem A V)
      (.classMem (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCvv))
      (.classMem (synCpw1 (synCpw1 A)) (synCvv))
      (.classMem (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
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
          (synCpw1 (synCpw1 A))) (synCvv))
      p0012 p0015 p0016
  have p0018 := @gPw1exg B W
  have p0019 := @gPw1exg (synCpw1 B) (synCvv)
  have p0020 :=
    @gSyl (.classMem B W) (.classMem (synCpw1 B) (synCvv))
      (.classMem (synCpw1 (synCpw1 B)) (synCvv)) p0018 p0019
  have p0021 :=
    @gImakexg
      (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl (synCimak
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
      (synCpw1 (synCpw1 B)) (synCvv) (synCvv)
  have p0022 :=
    @gSylancr (.classMem B W)
      (.classMem (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCvv))
      (.classMem (synCpw1 (synCpw1 B)) (synCvv))
      (.classMem (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
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
          (synCpw1 (synCpw1 B))) (synCvv))
      p0012 p0020 p0021
  have p0023 :=
    @gCokexg
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
              (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c)))))))) (synCpw1 (synCpw1 B)))
      (synCvv) (synCvv)
  have p0024 :=
    @gSyl2an (.classMem A V)
      (.classMem (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
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
          (synCpw1 (synCpw1 A))) (synCvv))
      (.classMem (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
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
          (synCpw1 (synCpw1 B))) (synCvv))
      (.classMem (synCcomk (synCimak
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
            (synCpw1 (synCpw1 A))) (synCimak
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
            (synCpw1 (synCpw1 B)))) (synCvv))
      (.classMem B W) p0017 p0022 p0023
  have p0025 :=
    @gImakexg
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
      (synCcomk (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
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
          (synCpw1 (synCpw1 A))) (synCimak
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
          (synCpw1 (synCpw1 B))))
      (synCvv) (synCvv)
  have p0026 :=
    @gSylancr (synWa (.classMem A V) (.classMem B W))
      (.classMem (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv)) (synCcnvk
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
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCvv))
      (.classMem (synCcomk (synCimak
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
            (synCpw1 (synCpw1 A))) (synCimak
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
            (synCpw1 (synCpw1 B)))) (synCvv))
      (.classMem (synCimak (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv))
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
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCcomk
            (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
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
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 A))) (synCimak
              (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
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
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 B))))) (synCvv))
      p0008 p0024 p0025
  have p0027 :=
    @gUni1exg
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
                (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCcomk (synCimak
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
            (synCpw1 (synCpw1 A))) (synCimak
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
            (synCpw1 (synCpw1 B)))))
      (synCvv)
  have p0028 :=
    @gUni1exg
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
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCcomk
            (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
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
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 A))) (synCimak
              (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
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
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 B))))))
      (synCvv)
  have p0029 :=
    @gN3syl (synWa (.classMem A V) (.classMem B W))
      (.classMem (synCimak (synCin (synCxpk (synCxpk (synCvv) (synCvv)) (synCvv))
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
                  (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCcomk
            (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
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
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 A))) (synCimak
              (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
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
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
              (synCpw1 (synCpw1 B))))) (synCvv))
      (.classMem (synCuni1 (synCimak
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
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCcomk
              (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
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
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 A))) (synCimak
                (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
                    (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
                        (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik
                                  (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
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
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 B)))))) (synCvv))
      (.classMem (synCuni1 (synCuni1 (synCimak
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
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCcomk
                (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
                    (synCcompl (synCimak
                        (synCsymdif (synCins3k (synCsik (synCsik (synCssetk)))) (synCins2k
                            (synCun (synCins3k (synCcomk (synCssetk) (synCsik (synCcnvk
                                      (synCimagek (synCun (synCin (synCimagek (synCimak
        (synCdif (synCins3k (synCcompl (synCimak (synCin (synCins3k (synCssetk))
        (synCins2k (synCssetk))) (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
        (synCins2k (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk)))
        (synCins3k (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
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
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 A))) (synCimak
                  (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
                      (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
                          (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik
                                    (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif (synCins2k
        (synCins2k (synCssetk))) (synCun (synCins2k (synCins3k (synCssetk))) (synCins3k
        (synCsik (synCsik (synCssetk)))))) (synCpw1 (synCpw1 (synCpw1
        (synCpw1 (synC1c))))))) (synCpw1 (synCpw1 (synC1c)))))
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
                        (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                  (synCpw1 (synCpw1 B))))))) (synCvv))
      p0026 p0027 p0028
  have p0030 :=
    @gSyl5eqel (synWa (.classMem A V) (.classMem B W)) (synCcom A B)
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
                    (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))) (synCcomk
              (synCimak (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv)))
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
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 A))) (synCimak
                (synCin (synCxpk (synCvv) (synCxpk (synCvv) (synCvv))) (synCcompl
                    (synCimak (synCsymdif (synCins3k (synCsik (synCsik (synCssetk))))
                        (synCins2k (synCun (synCins3k (synCcomk (synCssetk) (synCsik
                                  (synCcnvk (synCimagek (synCun (synCin (synCimagek
        (synCimak (synCdif (synCins3k (synCcompl (synCimak
        (synCin (synCins3k (synCssetk)) (synCins2k (synCssetk)))
        (synCpw1 (synCpw1 (synC1c)))))) (synCimak (synCsymdif
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
                      (synCpw1 (synCpw1 (synCpw1 (synCpw1 (synC1c))))))))
                (synCpw1 (synCpw1 B)))))))
      (synCvv) p0000 p0029
  exact p0030


end NFChoice.DirectNominalPrf.WPPReplay

end

/-! Certificates from `NominalWPPReplayChunk010Compact001Part057`. -/


section

namespace NFChoice.DirectNominalPrf.WPPReplay

open scoped Fol
open NFChoice.Foundation
open NFChoice.SemanticCore
open NFChoice.ReplaySupport
open NFChoice.Compiler.CompactSourceSyntax

/-- Checked nominal proof certificate identified upstream as `g_coex`. -/
@[expose]
noncomputable def gCoex (A : Class) (B : Class)
    (hyp_coex_1 : Nominal.NPrf (.classMem A (synCvv)))
    (hyp_coex_2 : Nominal.NPrf (.classMem B (synCvv))) :
    Nominal.NPrf (.classMem (synCcom A B) (synCvv)) :=
  by
  have p0000 := @gCoexg A B (synCvv) (synCvv)
  have p0001 :=
    @gMp2an (.classMem A (synCvv)) (.classMem B (synCvv))
      (.classMem (synCcom A B) (synCvv)) hyp_coex_1 hyp_coex_2 p0000
  exact p0001


end NFChoice.DirectNominalPrf.WPPReplay

end
